package org.cloudburstmc.protocol.bedrock.util;

import lombok.experimental.UtilityClass;
import lombok.extern.log4j.Log4j2;
import org.cloudburstmc.protocol.bedrock.codec.LoginLimits;
import org.cloudburstmc.protocol.bedrock.data.auth.AuthPayload;
import org.cloudburstmc.protocol.bedrock.data.auth.AuthType;
import org.cloudburstmc.protocol.bedrock.data.auth.CertificateChainPayload;
import org.cloudburstmc.protocol.bedrock.data.auth.TokenPayload;
import org.jose4j.json.JsonUtil;
import org.jose4j.jwa.AlgorithmConstraints;
import org.jose4j.jwa.AlgorithmConstraints.ConstraintType;
import org.jose4j.jwk.JsonWebKey;
import org.jose4j.jwk.JsonWebKeySet;
import org.jose4j.jws.AlgorithmIdentifiers;
import org.jose4j.jws.JsonWebSignature;
import org.jose4j.jwt.JwtClaims;
import org.jose4j.jwt.consumer.InvalidJwtException;
import org.jose4j.jwt.consumer.JwtConsumer;
import org.jose4j.jwt.consumer.JwtConsumerBuilder;
import org.jose4j.jwt.consumer.JwtContext;
import org.jose4j.jwx.HeaderParameterNames;
import org.jose4j.keys.resolvers.JwksVerificationKeyResolver;
import org.jose4j.lang.JoseException;

import javax.crypto.Cipher;
import javax.crypto.KeyAgreement;
import javax.crypto.NoSuchPaddingException;
import javax.crypto.SecretKey;
import javax.crypto.spec.IvParameterSpec;
import javax.crypto.spec.SecretKeySpec;
import javax.net.ssl.HttpsURLConnection;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.*;
import java.security.interfaces.ECPublicKey;
import java.security.spec.ECGenParameterSpec;
import java.security.spec.InvalidKeySpecException;
import java.security.spec.X509EncodedKeySpec;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.TimeUnit;

/**
 * WaterdogPE copy of the CloudburstMC Protocol class (Apache License 2.0), which takes priority over the library's.
 * <p>
 * The library fetches Microsoft's login keys while this class loads, so when the auth servers can't be reached
 * (filtered networks, sanctions) the class fails to load and every login fails until a restart.
 * Here the keys come from a copy bundled in the jar and from {@code auth_keys.json} in the proxy folder,
 * and are refreshed in the background whenever the network allows, so no login waits on the network.
 */
@Log4j2
@UtilityClass
public class EncryptionUtils {
    private static final ECPublicKey MOJANG_PUBLIC_KEY;

    private static final SecureRandom SECURE_RANDOM = new SecureRandom();
    private static final String MOJANG_PUBLIC_KEY_BASE64 =
            "MHYwEAYHKoZIzj0CAQYFK4EEACIDYgAECRXueJeTDqNRRgJi/vlRufByu/2G0i2Ebt6YMar5QX/R0DIIyrJMcUpruK4QveTfJSTp3Shlq4Gk34cD/4GUWwkv0DVuzeuB+tXija7HBxii03NHDbPAD0AKnLr2wdAp";
    private static final KeyPairGenerator KEY_PAIR_GEN;

    public static final String ALGORITHM_TYPE = AlgorithmIdentifiers.ECDSA_USING_P384_CURVE_AND_SHA384;
    private static final AlgorithmConstraints ALGORITHM_CONSTRAINTS =
            new AlgorithmConstraints(ConstraintType.PERMIT, ALGORITHM_TYPE);

    private static final String DISCOVERY_ENDPOINT =
            "https://client.discovery.minecraft-services.net/api/v1.0/discovery/MinecraftPE/builds/1.0.0.0";
    // what the discovery and OpenID endpoints returned when the bundled keys were taken
    private static final String DEFAULT_ISSUER = "https://authorization.franchise.minecraft-services.net/";
    private static final String BUNDLED_KEYS_RESOURCE = "mojang_auth_keys.json";
    private static final Path LOCAL_KEYS_FILE = Path.of("auth_keys.json");
    private static final long KEY_REFRESH_HOURS = 6;
    private static final long KEY_RETRY_MINUTES = 10;

    // every Microsoft signing key seen so far, by key id; old keys are kept so a rotation never locks players out
    private static final Map<String, JsonWebKey> KNOWN_KEYS = new ConcurrentHashMap<>();
    private static final Set<String> REPORTED_UNKNOWN_KEYS = ConcurrentHashMap.newKeySet();
    private static volatile String issuer = DEFAULT_ISSUER;
    private static volatile JwtConsumer mojangConsumer;
    private static volatile boolean refreshFailureReported = false;

    private static final JwtConsumer OFFLINE_CONSUMER = new JwtConsumerBuilder()
            .setSkipAllValidators()
            .setSkipSignatureVerification()
            .setRequireExpirationTime()
            .setSkipDefaultAudienceValidation()
            .build();

    static {
        // DO NOT REMOVE THIS
        // Since Java 8u231, secp384r1 is deprecated and will throw an exception.
        String namedGroups = System.getProperty("jdk.tls.namedGroups");
        System.setProperty("jdk.tls.namedGroups", namedGroups == null || namedGroups.isEmpty() ? "secp384r1" : namedGroups + ", secp384r1");

        try {
            KEY_PAIR_GEN = KeyPairGenerator.getInstance("EC");
            KEY_PAIR_GEN.initialize(new ECGenParameterSpec("secp384r1"));
            MOJANG_PUBLIC_KEY = parseKey(MOJANG_PUBLIC_KEY_BASE64);
        } catch (NoSuchAlgorithmException | InvalidAlgorithmParameterException | InvalidKeySpecException e) {
            throw new AssertionError("Unable to initialize required encryption", e);
        }

        loadKeys("bundled", readBundledKeys());
        if (Files.isRegularFile(LOCAL_KEYS_FILE)) {
            try {
                loadKeys(LOCAL_KEYS_FILE.toString(), Files.readString(LOCAL_KEYS_FILE));
            } catch (IOException e) {
                log.warn("Unable to read Xbox login keys from {}", LOCAL_KEYS_FILE.toAbsolutePath(), e);
            }
        }
        rebuildMojangConsumer();

        ScheduledExecutorService refresher = Executors.newSingleThreadScheduledExecutor(runnable -> {
            Thread thread = new Thread(runnable, "Xbox Login Keys Refresh");
            thread.setDaemon(true);
            return thread;
        });
        refresher.schedule(() -> refreshKeys(refresher), 0, TimeUnit.SECONDS);
    }

    private static String readBundledKeys() {
        try (InputStream stream = EncryptionUtils.class.getClassLoader().getResourceAsStream(BUNDLED_KEYS_RESOURCE)) {
            if (stream == null) {
                throw new AssertionError("Missing bundled Xbox login keys: " + BUNDLED_KEYS_RESOURCE);
            }
            return new String(stream.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new AssertionError("Unable to read bundled Xbox login keys", e);
        }
    }

    private static void loadKeys(String source, String json) {
        try {
            int added = 0;
            for (JsonWebKey key : new JsonWebKeySet(json).getJsonWebKeys()) {
                if (key.getKeyId() != null && KNOWN_KEYS.putIfAbsent(key.getKeyId(), key) == null) {
                    added++;
                }
            }
            log.debug("Loaded {} new Xbox login keys from {}", added, source);
        } catch (JoseException e) {
            log.warn("Unable to parse Xbox login keys from {}", source, e);
        }
    }

    private static void rebuildMojangConsumer() {
        mojangConsumer = new JwtConsumerBuilder()
                .setVerificationKeyResolver(new JwksVerificationKeyResolver(new ArrayList<>(KNOWN_KEYS.values())))
                .setRequireExpirationTime()
                .setRequireSubject()
                .setExpectedAudience(true, "api://auth-minecraft-services/multiplayer")
                .setExpectedIssuer(issuer)
                .build();
    }

    /**
     * Fetches Microsoft's current login keys and keeps them next to the known ones.
     * Runs on its own thread, so an unreachable auth server only means the known keys stay in use.
     */
    private static void refreshKeys(ScheduledExecutorService refresher) {
        long nextRun = KEY_REFRESH_HOURS;
        TimeUnit unit = TimeUnit.HOURS;
        try {
            String serviceUri = getServiceUri(JsonUtil.parseJson(fetch(DISCOVERY_ENDPOINT)));
            Map<String, Object> openIdConfiguration = JsonUtil.parseJson(fetch(serviceUri + "/.well-known/openid-configuration"));
            String jwksUrl = getRequiredString(openIdConfiguration, "jwks_uri");
            String fetchedIssuer = getRequiredString(openIdConfiguration, "issuer");

            int knownBefore = KNOWN_KEYS.size();
            loadKeys(jwksUrl, fetch(jwksUrl));
            boolean changed = KNOWN_KEYS.size() != knownBefore || !fetchedIssuer.equals(issuer);
            issuer = fetchedIssuer;
            if (changed) {
                rebuildMojangConsumer();
                saveKeys();
            }
            refreshFailureReported = false;
        } catch (Exception e) {
            if (!refreshFailureReported) {
                refreshFailureReported = true;
                log.warn("Unable to reach Microsoft's auth servers ({}), using the {} known Xbox login keys. Will retry every {} minutes.",
                        e.getMessage(), KNOWN_KEYS.size(), KEY_RETRY_MINUTES);
            }
            nextRun = KEY_RETRY_MINUTES;
            unit = TimeUnit.MINUTES;
        }
        refresher.schedule(() -> refreshKeys(refresher), nextRun, unit);
    }

    private static void saveKeys() {
        try {
            String json = new JsonWebKeySet(new ArrayList<>(KNOWN_KEYS.values())).toJson(JsonWebKey.OutputControlLevel.PUBLIC_ONLY);
            Files.writeString(LOCAL_KEYS_FILE, json);
        } catch (IOException e) {
            log.warn("Unable to save Xbox login keys to {}", LOCAL_KEYS_FILE.toAbsolutePath(), e);
        }
    }

    private static String fetch(String endpoint) throws IOException {
        HttpsURLConnection connection = (HttpsURLConnection) new URL(endpoint).openConnection();
        try {
            connection.setRequestMethod("GET");
            connection.setRequestProperty("Accept", "application/json");
            connection.setConnectTimeout(5000);
            connection.setReadTimeout(5000);
            if (connection.getResponseCode() != 200) {
                throw new IOException("HTTP " + connection.getResponseCode() + " from " + endpoint);
            }
            try (InputStream stream = connection.getInputStream()) {
                return new String(stream.readAllBytes(), StandardCharsets.UTF_8);
            }
        } finally {
            connection.disconnect();
        }
    }

    @SuppressWarnings("unchecked")
    private static String getServiceUri(Map<String, Object> discoveryData) {
        Map<String, Object> result = (Map<String, Object>) discoveryData.get("result");
        if (result == null) {
            throw new IllegalStateException("Discovery data does not contain 'result' key" + discoveryData);
        }
        Map<String, Object> environments = (Map<String, Object>) result.get("serviceEnvironments");
        if (environments == null) {
            throw new IllegalStateException("Discovery data does not contain 'serviceEnvironments' key" + result);
        }
        Map<String, Object> authEnv = (Map<String, Object>) environments.get("auth");
        if (authEnv == null) {
            throw new IllegalStateException("Discovery data does not contain 'auth' environment" + environments);
        }
        Map<String, Object> prodEnv = (Map<String, Object>) authEnv.get("prod");
        if (prodEnv == null) {
            throw new IllegalStateException("Discovery data does not contain 'prod' environment" + authEnv);
        }
        return getRequiredString(prodEnv, "serviceUri");
    }

    private static String getRequiredString(Map<String, Object> map, String key) {
        Object value = map.get(key);
        if (!(value instanceof String) || ((String) value).isEmpty()) {
            throw new IllegalStateException("Missing '" + key + "' in " + map);
        }
        return (String) value;
    }

    /**
     * Generate EC public key from base 64 encoded string
     *
     * @param b64 base 64 encoded key
     * @return key generated
     * @throws NoSuchAlgorithmException runtime does not support the EC key spec
     * @throws InvalidKeySpecException  input does not conform with EC key spec
     */
    public static ECPublicKey parseKey(String b64) throws NoSuchAlgorithmException, InvalidKeySpecException {
        return (ECPublicKey) KeyFactory.getInstance("EC").generatePublic(new X509EncodedKeySpec(Base64.getDecoder().decode(b64)));
    }

    /**
     * Create EC key pair to be used for handshake and encryption
     *
     * @return EC KeyPair
     */
    public static KeyPair createKeyPair() {
        return KEY_PAIR_GEN.generateKeyPair();
    }

    public static byte[] verifyClientData(String clientDataJwt, String identityPublicKey)
            throws NoSuchAlgorithmException, InvalidKeySpecException, JoseException {
        return verifyClientData(clientDataJwt, parseKey(identityPublicKey));
    }

    public static byte[] verifyClientData(String clientDataJwt, PublicKey identityPublicKey) throws JoseException {
        LoginLimits.checkJwtHeader(clientDataJwt);
        JsonWebSignature clientData = new JsonWebSignature();
        clientData.setCompactSerialization(clientDataJwt);
        clientData.setKey(identityPublicKey);
        if (!clientData.verifySignature()) {
            return null;
        }
        return clientData.getUnverifiedPayloadBytes();
    }

    public static ChainValidationResult validatePayload(AuthPayload payload)
            throws JoseException, NoSuchAlgorithmException, InvalidKeySpecException, InvalidJwtException {
        ChainValidationResult result;

        if (payload instanceof CertificateChainPayload) {
            CertificateChainPayload chainPayload = (CertificateChainPayload) payload;
            List<String> chain = chainPayload.getChain();
            if (chain == null || chain.isEmpty()) {
                throw new IllegalStateException("Certificate chain is empty");
            }
            result = validateChain(chain);
        } else if (payload instanceof TokenPayload) {
            TokenPayload tokenPayload = (TokenPayload) payload;
            String token = tokenPayload.getToken();
            if (token == null || token.isEmpty()) {
                throw new IllegalStateException("Token is empty");
            }
            result = validateToken(payload.getAuthType(), token);
        } else {
            throw new IllegalArgumentException("Unsupported AuthPayload type: " + payload.getClass().getName());
        }

        if (payload.getAuthType() == AuthType.FULL) {
            if (result.identityClaims().extraData == null || result.identityClaims().extraData.xuid == null || result.identityClaims().extraData.displayName == null) {
                throw new IllegalStateException("Missing extraData for full auth");
            }
        }

        return result;
    }

    public static ChainValidationResult validateChain(List<String> chain)
            throws JoseException, NoSuchAlgorithmException, InvalidKeySpecException {
        switch (chain.size()) {
            case 1:
                // offline / proxied
                JsonWebSignature identity = new JsonWebSignature();
                identity.setCompactSerialization(chain.get(0));
                return new ChainValidationResult(false, identity.getUnverifiedPayload());
            case 3:
                ECPublicKey currentKey = null;
                Map<String, Object> parsedPayload = null;
                for (int i = 0; i < 3; i++) {
                    JsonWebSignature signature = new JsonWebSignature();
                    signature.setCompactSerialization(chain.get(i));

                    ECPublicKey expectedKey = parseKey(signature.getHeader(HeaderParameterNames.X509_URL));

                    if (currentKey == null) {
                        currentKey = expectedKey;
                    } else if (!currentKey.equals(expectedKey)) {
                        throw new IllegalStateException("Received broken chain");
                    }

                    signature.setAlgorithmConstraints(ALGORITHM_CONSTRAINTS);
                    signature.setKey(currentKey);
                    if (!signature.verifySignature()) {
                        throw new IllegalStateException("Chain signature doesn't match content");
                    }

                    // the second chain entry has to be signed by Mojang
                    if (i == 1 && !currentKey.equals(MOJANG_PUBLIC_KEY)) {
                        throw new IllegalStateException("The chain isn't signed by Mojang!");
                    }

                    // the client signs the first entry itself, so only the others' validity windows hold
                    if (i > 0) {
                        ChainEntryWindow.check(chain.get(i));
                    }

                    parsedPayload = JsonUtil.parseJson(signature.getUnverifiedPayload());
                    String identityPublicKey = JsonUtils.childAsType(parsedPayload, "identityPublicKey", String.class);
                    currentKey = parseKey(identityPublicKey);
                }
                return new ChainValidationResult(true, parsedPayload);
            default:
                throw new IllegalStateException("Unexpected login chain length");
        }
    }

    public static ChainValidationResult validateToken(AuthType type, String token) throws InvalidJwtException, JoseException {
        if (type == AuthType.FULL || type == AuthType.GUEST) {
            try {
                return new ChainValidationResult(true, mojangConsumer.process(token));
            } catch (InvalidJwtException e) {
                // an unverified token is an unauthenticated player: online_mode turns them away, offline mode lets them in
                reportUnknownKey(token);
                log.debug("Xbox login token could not be verified, treating it as not authenticated", e);
                return new ChainValidationResult(false, OFFLINE_CONSUMER.process(token));
            }
        } else if (type == AuthType.SELF_SIGNED) {
            JwtContext context = OFFLINE_CONSUMER.process(token);
            return new ChainValidationResult(false, context);
        }
        throw new JoseException("Unsupported AuthType: " + type);
    }

    // Microsoft rotates its keys now and then; a server that can't reach it has to be handed the new ones
    private static void reportUnknownKey(String token) {
        try {
            JsonWebSignature jws = new JsonWebSignature();
            jws.setCompactSerialization(token);
            String keyId = jws.getKeyIdHeaderValue();
            if (keyId != null && !KNOWN_KEYS.containsKey(keyId) && REPORTED_UNKNOWN_KEYS.add(keyId)) {
                log.warn("A player logged in with an Xbox login key this proxy doesn't know ({}), so they count as not authenticated. "
                        + "With online_mode on, download {} from a network that can reach it and save it as {}", keyId,
                        "https://authorization.franchise.minecraft-services.net/.well-known/keys", LOCAL_KEYS_FILE.toAbsolutePath());
            }
        } catch (JoseException ignored) {
            // a token that doesn't even parse isn't a key problem
        }
    }

    /**
     * Generate the secret key used to encrypt the connection
     *
     * @param localPrivateKey local private key
     * @param remotePublicKey remote public key
     * @param token           token generated or received from the server
     * @return secret key used to encrypt connection
     * @throws InvalidKeyException keys provided are not EC spec
     */
    public static SecretKey getSecretKey(PrivateKey localPrivateKey, PublicKey remotePublicKey, byte[] token) throws InvalidKeyException {
        byte[] sharedSecret = getEcdhSecret(localPrivateKey, remotePublicKey);

        MessageDigest digest;
        try {
            digest = MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException e) {
            throw new AssertionError(e);
        }

        digest.update(token);
        digest.update(sharedSecret);
        byte[] secretKeyBytes = digest.digest();
        return new SecretKeySpec(secretKeyBytes, "AES");
    }

    private static byte[] getEcdhSecret(PrivateKey localPrivateKey, PublicKey remotePublicKey) throws InvalidKeyException {
        KeyAgreement agreement;
        try {
            agreement = KeyAgreement.getInstance("ECDH");
        } catch (NoSuchAlgorithmException e) {
            throw new AssertionError(e);
        }

        agreement.init(localPrivateKey);
        agreement.doPhase(remotePublicKey, true);
        return agreement.generateSecret();
    }

    /**
     * Create handshake JWS used in the {@link org.cloudburstmc.protocol.bedrock.packet.ServerToClientHandshakePacket}
     * which completes the encryption handshake.
     *
     * @param serverKeyPair used to sign the JWT
     * @param token         salt for the encryption handshake
     * @return signed JWS object
     * @throws JoseException invalid key pair provided
     */
    public static String createHandshakeJwt(KeyPair serverKeyPair, byte[] token) throws JoseException {
        JsonWebSignature signature = new JsonWebSignature();
        signature.setAlgorithmHeaderValue(ALGORITHM_TYPE);
        signature.setHeader(
                HeaderParameterNames.X509_URL,
                Base64.getEncoder().encodeToString(serverKeyPair.getPublic().getEncoded())
        );
        signature.setKey(serverKeyPair.getPrivate());

        JwtClaims claims = new JwtClaims();
        claims.setClaim("salt", Base64.getEncoder().encodeToString(token));
        signature.setPayload(claims.toJson());

        return signature.getCompactSerialization();
    }

    /**
     * Generate 16 bytes of random data for the handshake token using a {@link SecureRandom}
     *
     * @return 16 byte token
     */
    public static byte[] generateRandomToken() {
        byte[] token = new byte[16];
        SECURE_RANDOM.nextBytes(token);
        return token;
    }

    /**
     * Mojang's public key used to verify the JWT during login.
     *
     * @return Mojang's public EC key
     */
    public static ECPublicKey getMojangPublicKey() {
        return MOJANG_PUBLIC_KEY;
    }

    public static Cipher createCipher(boolean gcm, boolean encrypt, SecretKey key) {
        try {
            byte[] iv;
            String transformation;
            if (gcm) {
                iv = new byte[16];
                System.arraycopy(key.getEncoded(), 0, iv, 0, 12);
                iv[15] = 2;
                transformation = "AES/CTR/NoPadding";
            } else {
                iv = Arrays.copyOf(key.getEncoded(), 16);
                transformation = "AES/CFB8/NoPadding";
            }
            Cipher cipher = Cipher.getInstance(transformation);
            cipher.init(encrypt ? Cipher.ENCRYPT_MODE : Cipher.DECRYPT_MODE, key, new IvParameterSpec(iv));
            return cipher;
        } catch (NoSuchAlgorithmException | NoSuchPaddingException | InvalidKeyException | InvalidAlgorithmParameterException e) {
            throw new AssertionError("Unable to initialize required encryption", e);
        }
    }
}
