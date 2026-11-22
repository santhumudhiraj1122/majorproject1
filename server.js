const { createServer } = require("node:http");
const { randomBytes, scrypt, timingSafeEqual } = require("node:crypto");
const { existsSync } = require("node:fs");
const { mkdirSync } = require("node:fs");
const { readFile } = require("node:fs/promises");
const path = require("node:path");
const { promisify } = require("node:util");
const { DatabaseSync } = require("node:sqlite");

const envFile = path.join(__dirname, ".env");
const port = Number(process.env.PORT) || 3000;
const host = process.env.HOST || "127.0.0.1";
const bodyLimit = 10 * 1024;
const productBodyLimit = 16 * 1024 * 1024;
const maximumImageBytes = 2 * 1024 * 1024;
const maximumProductImages = 5;
const accountTokenLifetimeMs = 8 * 60 * 60 * 1000;
const projectDirectory = __dirname;
const userDataDirectory = process.env.ZEUKART_DATA_DIR || path.join(__dirname, ".data");
const legacyProductCatalogFile = path.join(__dirname, "product-catalog.json");
const otpValidityMs = 5 * 60 * 1000;
const verificationExpirations = new Map();
const localVerificationCodes = new Map();
const uiTranslationCache = new Map();
const uiTranslationPending = new Map();
let uiTranslationStrings = null;
const accountSessions = new Map();
const scryptAsync = promisify(scrypt);
const productCategories = new Set([
    "mobiles",
    "laptops",
    "fashion",
    "electronics",
    "home-kitchen",
    "beauty",
    "grocery",
    "sports-fitness",
    "gaming",
    "books"
]);
const supportedEmiTenures = new Set([3, 6, 9, 12]);
let database = null;

function sendJson(response, statusCode, data) {
    response.writeHead(statusCode, { "Content-Type": "application/json; charset=utf-8" });
    response.end(JSON.stringify(data));
}

async function hashPassword(password) {
    const salt = randomBytes(16).toString("hex");
    const hash = await scryptAsync(password, salt, 64);
    return { passwordSalt: salt, passwordHash: hash.toString("hex") };
}

async function verifyPassword(password, user) {
    if (typeof user.passwordHash !== "string" || typeof user.passwordSalt !== "string") {
        return false;
    }
    const expectedHash = Buffer.from(user.passwordHash, "hex");
    if (expectedHash.length === 0) return false;
    const actualHash = await scryptAsync(password, user.passwordSalt, expectedHash.length);
    return timingSafeEqual(expectedHash, actualHash);
}

function publicUser(user) {
    return { username: user.username, mobile: user.mobile, email: user.email || "" };
}

function createAccountSession(ownerKey, displayName) {
    const now = Date.now();
    for (const [token, session] of accountSessions) {
        if (session.expiresAt <= now) accountSessions.delete(token);
    }

    const token = randomBytes(32).toString("hex");
    accountSessions.set(token, {
        role: "customer",
        ownerKey,
        displayName,
        expiresAt: now + accountTokenLifetimeMs
    });
    return { token, expiresInSeconds: accountTokenLifetimeMs / 1000 };
}

function getSession(request) {
    const authorization = request.headers.authorization || "";
    const token = authorization.startsWith("Bearer ") ? authorization.slice(7) : "";
    const session = accountSessions.get(token);
    if (!session) return null;
    if (session.expiresAt <= Date.now()) {
        accountSessions.delete(token);
        return null;
    }
    return session;
}

function getAccountSession(request) {
    const session = getSession(request);
    return session && session.role === "customer" ? session : null;
}

function getAdminSession(request) {
    const session = getSession(request);
    return session && session.role === "admin" ? session : null;
}

function createAdminSession(admin) {
    const now = Date.now();
    for (const [token, session] of accountSessions) {
        if (session.expiresAt <= now) accountSessions.delete(token);
    }

    const token = randomBytes(32).toString("hex");
    accountSessions.set(token, {
        role: "admin",
        adminId: admin.id,
        ownerKey: `admin:${admin.id}`,
        displayName: admin.username,
        expiresAt: now + accountTokenLifetimeMs
    });
    return { token, expiresInSeconds: accountTokenLifetimeMs / 1000 };
}

function readJsonBody(request, limit = bodyLimit) {
    return new Promise((resolve, reject) => {
        let body = "";
        let size = 0;
        let settled = false;

        request.on("data", (chunk) => {
            size += chunk.length;
            if (size > limit) {
                settled = true;
                const error = new Error("Request body is too large.");
                error.statusCode = 413;
                reject(error);
                return;
            }
            body += chunk;
        });

        request.on("end", () => {
            if (settled) return;
            try {
                const parsed = JSON.parse(body);
                if (!parsed || typeof parsed !== "object" || Array.isArray(parsed)) {
                    throw new Error("Request body must be a JSON object.");
                }
                resolve(parsed);
            } catch {
                const error = new Error("Request body must be valid JSON.");
                error.statusCode = 400;
                reject(error);
            }
        });

        request.on("error", reject);
    });
}

function normalizePhone(phone) {
    if (typeof phone !== "string") return null;

    const compactPhone = phone.trim().replace(/[\s()-]/g, "");
    if (/^\d{10}$/.test(compactPhone)) {
        return `+91${compactPhone}`;
    }
    if (/^91\d{10}$/.test(compactPhone)) {
        return `+${compactPhone}`;
    }
    return /^\+[1-9]\d{7,14}$/.test(compactPhone) ? compactPhone : null;
}

function loadLocalEnvironment() {
    if (existsSync(envFile)) {
        for (const setting of [
            "TWILIO_ACCOUNT_SID",
            "TWILIO_AUTH_TOKEN",
            "TWILIO_VERIFY_SERVICE_SID",
            "GOOGLE_CLIENT_ID",
            "GOOGLE_MAPS_API_KEY",
            "AZURE_TRANSLATOR_KEY",
            "AZURE_TRANSLATOR_REGION",
            "AZURE_TRANSLATOR_ENDPOINT"
        ]) {
            if (!process.env[setting]) {
                delete process.env[setting];
            }
        }
        process.loadEnvFile(envFile);
    }
}

async function initializeDatabase() {
    loadLocalEnvironment();
    mkdirSync(userDataDirectory, { recursive: true });
    database = new DatabaseSync(path.join(userDataDirectory, "zeukart.sqlite"));
    database.exec(`
        PRAGMA foreign_keys = ON;
        PRAGMA journal_mode = WAL;
        CREATE TABLE IF NOT EXISTS customers (
            id INTEGER PRIMARY KEY,
            username TEXT NOT NULL,
            username_key TEXT NOT NULL UNIQUE,
            mobile TEXT NOT NULL UNIQUE,
            email TEXT,
            email_key TEXT,
            password_salt TEXT NOT NULL,
            password_hash TEXT NOT NULL,
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS administrators (
            id INTEGER PRIMARY KEY,
            username TEXT NOT NULL,
            username_key TEXT NOT NULL UNIQUE,
            email TEXT UNIQUE,
            email_key TEXT,
            mobile TEXT UNIQUE,
            google_sub TEXT UNIQUE,
            password_salt TEXT NOT NULL,
            password_hash TEXT NOT NULL,
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS google_accounts (
            google_sub TEXT PRIMARY KEY,
            email TEXT NOT NULL UNIQUE,
            name TEXT NOT NULL,
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS products (
            id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            description TEXT NOT NULL DEFAULT '',
            category TEXT NOT NULL,
            price_paise INTEGER NOT NULL CHECK (price_paise > 0),
            offer TEXT NOT NULL DEFAULT '',
            image TEXT NOT NULL,
            images_json TEXT NOT NULL DEFAULT '[]',
            stock INTEGER NOT NULL DEFAULT 0 CHECK (stock >= 0),
            view_count INTEGER NOT NULL DEFAULT 0 CHECK (view_count >= 0),
            emi_tenures_json TEXT NOT NULL DEFAULT '[]',
            owner_key TEXT NOT NULL DEFAULT 'legacy',
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS orders (
            id INTEGER PRIMARY KEY,
            order_number TEXT NOT NULL UNIQUE,
            customer_name TEXT NOT NULL,
            customer_mobile TEXT NOT NULL,
            shipping_address TEXT NOT NULL,
            payment_method TEXT NOT NULL,
            payment_status TEXT NOT NULL,
            status TEXT NOT NULL,
            tracking_number TEXT NOT NULL DEFAULT '',
            total_paise INTEGER NOT NULL CHECK (total_paise > 0),
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS order_items (
            id INTEGER PRIMARY KEY,
            order_id INTEGER NOT NULL REFERENCES orders(id) ON DELETE CASCADE,
            product_id INTEGER NOT NULL,
            product_name TEXT NOT NULL,
            unit_price_paise INTEGER NOT NULL,
            quantity INTEGER NOT NULL CHECK (quantity > 0),
            owner_key TEXT NOT NULL DEFAULT 'legacy'
        );
        CREATE TABLE IF NOT EXISTS customer_addresses (
            id INTEGER PRIMARY KEY,
            owner_key TEXT NOT NULL,
            label TEXT NOT NULL CHECK (label IN ('Home', 'Office', 'Other')),
            recipient_name TEXT NOT NULL,
            mobile TEXT NOT NULL,
            line1 TEXT NOT NULL,
            street TEXT NOT NULL,
            city TEXT NOT NULL,
            district TEXT NOT NULL,
            state TEXT NOT NULL,
            country TEXT NOT NULL,
            pincode TEXT NOT NULL,
            is_default INTEGER NOT NULL DEFAULT 0 CHECK (is_default IN (0, 1)),
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            updated_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        );
        CREATE UNIQUE INDEX IF NOT EXISTS idx_customer_addresses_default
            ON customer_addresses(owner_key) WHERE is_default = 1;
        CREATE TABLE IF NOT EXISTS account_order_requests (
            id INTEGER PRIMARY KEY,
            order_id INTEGER NOT NULL REFERENCES orders(id) ON DELETE CASCADE,
            customer_mobile TEXT NOT NULL,
            request_type TEXT NOT NULL CHECK (request_type IN ('cancellation', 'return')),
            reason TEXT NOT NULL,
            request_status TEXT NOT NULL DEFAULT 'submitted',
            refund_status TEXT NOT NULL DEFAULT 'not_started',
            pickup_status TEXT NOT NULL DEFAULT 'not_scheduled',
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            UNIQUE (order_id, request_type)
        );
        CREATE TABLE IF NOT EXISTS support_tickets (
            id INTEGER PRIMARY KEY,
            owner_key TEXT NOT NULL,
            category TEXT NOT NULL,
            subject TEXT NOT NULL,
            message TEXT NOT NULL,
            product_id INTEGER REFERENCES products(id) ON DELETE SET NULL,
            admin_id INTEGER REFERENCES administrators(id) ON DELETE SET NULL,
            requester_name TEXT NOT NULL DEFAULT '',
            requester_contact TEXT NOT NULL DEFAULT '',
            status TEXT NOT NULL DEFAULT 'open',
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        );
        CREATE TABLE IF NOT EXISTS product_reviews (
            id INTEGER PRIMARY KEY,
            product_id INTEGER NOT NULL REFERENCES products(id) ON DELETE CASCADE,
            reviewer_key TEXT NOT NULL,
            reviewer_name TEXT NOT NULL,
            rating INTEGER NOT NULL CHECK (rating BETWEEN 1 AND 5),
            comment TEXT NOT NULL,
            created_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            UNIQUE (product_id, reviewer_key)
        );
        CREATE TABLE IF NOT EXISTS app_migrations (
            name TEXT PRIMARY KEY,
            applied_at TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP
        );
    `);
    const productColumns = database.prepare("PRAGMA table_info(products)").all();
    if (!productColumns.some((column) => column.name === "description")) {
        database.exec("ALTER TABLE products ADD COLUMN description TEXT NOT NULL DEFAULT ''");
    }
    if (!productColumns.some((column) => column.name === "owner_key")) {
        database.exec("ALTER TABLE products ADD COLUMN owner_key TEXT NOT NULL DEFAULT 'legacy'");
    }
    if (!productColumns.some((column) => column.name === "images_json")) {
        database.exec("ALTER TABLE products ADD COLUMN images_json TEXT NOT NULL DEFAULT '[]'");
    }
    if (!productColumns.some((column) => column.name === "view_count")) {
        database.exec("ALTER TABLE products ADD COLUMN view_count INTEGER NOT NULL DEFAULT 0 CHECK (view_count >= 0)");
    }
    if (!productColumns.some((column) => column.name === "emi_tenures_json")) {
        database.exec("ALTER TABLE products ADD COLUMN emi_tenures_json TEXT NOT NULL DEFAULT '[]'");
    }
    const customerColumns = database.prepare("PRAGMA table_info(customers)").all();
    if (!customerColumns.some((column) => column.name === "email")) {
        database.exec("ALTER TABLE customers ADD COLUMN email TEXT");
    }
    if (!customerColumns.some((column) => column.name === "email_key")) {
        database.exec("ALTER TABLE customers ADD COLUMN email_key TEXT");
    }
    const adminColumns = database.prepare("PRAGMA table_info(administrators)").all();
    if (!adminColumns.some((column) => column.name === "email")) {
        database.exec("ALTER TABLE administrators ADD COLUMN email TEXT");
    }
    if (!adminColumns.some((column) => column.name === "email_key")) {
        database.exec("ALTER TABLE administrators ADD COLUMN email_key TEXT");
    }
    if (!adminColumns.some((column) => column.name === "mobile")) {
        database.exec("ALTER TABLE administrators ADD COLUMN mobile TEXT");
    }
    if (!adminColumns.some((column) => column.name === "google_sub")) {
        database.exec("ALTER TABLE administrators ADD COLUMN google_sub TEXT");
    }
    const orderItemColumns = database.prepare("PRAGMA table_info(order_items)").all();
    if (!orderItemColumns.some((column) => column.name === "owner_key")) {
        database.exec("ALTER TABLE order_items ADD COLUMN owner_key TEXT NOT NULL DEFAULT 'legacy'");
    }
    const supportTicketColumns = database.prepare("PRAGMA table_info(support_tickets)").all();
    for (const [column, definition] of [
        ["product_id", "INTEGER REFERENCES products(id) ON DELETE SET NULL"],
        ["admin_id", "INTEGER REFERENCES administrators(id) ON DELETE SET NULL"],
        ["requester_name", "TEXT NOT NULL DEFAULT ''"],
        ["requester_contact", "TEXT NOT NULL DEFAULT ''"]
    ]) {
        if (!supportTicketColumns.some((existing) => existing.name === column)) {
            database.exec(`ALTER TABLE support_tickets ADD COLUMN ${column} ${definition}`);
        }
    }
    database.exec(`
        CREATE UNIQUE INDEX IF NOT EXISTS idx_customers_email_key
            ON customers(email_key) WHERE email_key IS NOT NULL;
        CREATE UNIQUE INDEX IF NOT EXISTS idx_administrators_email_key
            ON administrators(email_key) WHERE email_key IS NOT NULL;
        CREATE UNIQUE INDEX IF NOT EXISTS idx_administrators_mobile
            ON administrators(mobile) WHERE mobile IS NOT NULL;
        CREATE UNIQUE INDEX IF NOT EXISTS idx_administrators_email
            ON administrators(email) WHERE email IS NOT NULL;
        CREATE UNIQUE INDEX IF NOT EXISTS idx_administrators_google_sub
            ON administrators(google_sub) WHERE google_sub IS NOT NULL;
        CREATE INDEX IF NOT EXISTS idx_support_tickets_admin
            ON support_tickets(admin_id, id DESC);
    `);
    await removeLegacySampleProducts();
    console.log("ZeuKart account and marketplace storage: local SQLite");
}

async function removeLegacySampleProducts() {
    const migrationName = "remove-initial-sample-products";
    if (database.prepare("SELECT name FROM app_migrations WHERE name = ?").get(migrationName)) return;

    const catalog = JSON.parse(await readFile(legacyProductCatalogFile, "utf8"));
    const imageIndexes = Object.create(null);
    const deleteProduct = database.prepare(`
        DELETE FROM products
        WHERE id = (
            SELECT id FROM products
            WHERE id <= ?
              AND name = ?
              AND description = ''
              AND category = ?
              AND price_paise = ?
              AND offer = ?
              AND image = ?
              AND stock = 10
            ORDER BY id
            LIMIT 1
        )
    `);
    database.exec("BEGIN IMMEDIATE");
    try {
        for (const product of catalog.products) {
            const images = catalog.categoryImages[product.category];
            if (!Array.isArray(images) || images.length === 0) {
                throw new Error(`Missing legacy product images for category ${product.category}.`);
            }
            const imageIndex = imageIndexes[product.category] || 0;
            imageIndexes[product.category] = imageIndex + 1;
            deleteProduct.run(
                catalog.products.length,
                product.name,
                product.category,
                product.pricePaise,
                product.offer || "",
                images[imageIndex % images.length]
            );
        }
        database.prepare("INSERT INTO app_migrations (name) VALUES (?)").run(migrationName);
        database.exec("COMMIT");
    } catch (error) {
        database.exec("ROLLBACK");
        throw error;
    }
}

function accountConflict(username, phone, email) {
    const usernameKey = username.toLowerCase();
    return Boolean(database.prepare(
        "SELECT id FROM customers WHERE username_key = ? OR mobile = ? OR email_key = ? LIMIT 1"
    ).get(usernameKey, phone, email.toLowerCase()));
}

function findAccount(identifier, phone, emailKey = "") {
    return database.prepare(`
        SELECT username, mobile, email,
               password_salt AS passwordSalt,
               password_hash AS passwordHash
        FROM customers
        WHERE username_key = ? OR mobile = ? OR email_key = ?
        LIMIT 1
    `).get(identifier.toLowerCase(), phone || "", emailKey);
}

function findAccountByPhone(phone) {
    return database.prepare(
        "SELECT username, mobile, email FROM customers WHERE mobile = ? LIMIT 1"
    ).get(phone);
}

function insertAccount(username, phone, email, credentials) {
    const result = database.prepare(`
        INSERT OR IGNORE INTO customers
            (username, username_key, mobile, email, email_key, password_salt, password_hash)
        VALUES (?, ?, ?, ?, ?, ?, ?)
    `).run(
        username,
        username.toLowerCase(),
        phone,
        email,
        email.toLowerCase(),
        credentials.passwordSalt,
        credentials.passwordHash
    );
    return result.changes > 0;
}

function isValidEmail(email) {
    return typeof email === "string" &&
        email.length <= 254 &&
        /^[^\s@]+@[^\s@]+\.[^\s@]+$/.test(email);
}

function updateAccountPassword(phone, credentials) {
    const result = database.prepare(`
        UPDATE customers
        SET password_salt = ?, password_hash = ?
        WHERE mobile = ?
    `).run(credentials.passwordSalt, credentials.passwordHash, phone);
    return result.changes > 0;
}

function saveGoogleAccount(googleSub, email, name) {
    database.prepare(`
        INSERT INTO google_accounts (google_sub, email, name)
        VALUES (?, ?, ?)
        ON CONFLICT (google_sub)
        DO UPDATE SET email = excluded.email, name = excluded.name, updated_at = CURRENT_TIMESTAMP
    `).run(googleSub, email, name);
}

function getTwilioCredentials() {
    loadLocalEnvironment();

    const { TWILIO_ACCOUNT_SID, TWILIO_AUTH_TOKEN, TWILIO_VERIFY_SERVICE_SID } = process.env;
    const missingSettings = [];
    if (!TWILIO_ACCOUNT_SID) missingSettings.push("TWILIO_ACCOUNT_SID");
    if (!TWILIO_AUTH_TOKEN) missingSettings.push("TWILIO_AUTH_TOKEN");
    if (!TWILIO_VERIFY_SERVICE_SID) missingSettings.push("TWILIO_VERIFY_SERVICE_SID");

    if (missingSettings.length > 0) {
        const error = new Error(
            `SMS verification is missing ${missingSettings.join(", ")} in the local .env file.`
        );
        error.statusCode = 503;
        throw error;
    }

    return { TWILIO_ACCOUNT_SID, TWILIO_AUTH_TOKEN, TWILIO_VERIFY_SERVICE_SID };
}

function hasTwilioCredentials() {
    loadLocalEnvironment();
    return Boolean(
        process.env.TWILIO_ACCOUNT_SID &&
        process.env.TWILIO_AUTH_TOKEN &&
        process.env.TWILIO_VERIFY_SERVICE_SID
    );
}

const translatorLanguageCodes = {
    es: "es",
    fr: "fr",
    ar: "ar",
    as: "as",
    bn: "bn",
    brx: "brx",
    doi: "doi",
    gu: "gu",
    hi: "hi",
    kn: "kn",
    ks: "ks",
    kok: "gom",
    mai: "mai",
    ml: "ml",
    mni: "mni",
    mr: "mr",
    ne: "ne",
    or: "or",
    pa: "pa",
    sa: "sa",
    sat: "sat",
    sd: "sd",
    ta: "ta",
    te: "te",
    ur: "ur"
};

function getTranslatorCredentials() {
    loadLocalEnvironment();

    const { AZURE_TRANSLATOR_KEY, AZURE_TRANSLATOR_REGION } = process.env;
    if (!AZURE_TRANSLATOR_KEY || !AZURE_TRANSLATOR_REGION) {
        const error = new Error(
            "Configure AZURE_TRANSLATOR_KEY and AZURE_TRANSLATOR_REGION in the local .env file to enable all language translations."
        );
        error.statusCode = 503;
        throw error;
    }

    const endpoint = process.env.AZURE_TRANSLATOR_ENDPOINT || "https://api.cognitive.microsofttranslator.com";
    let parsedEndpoint;
    try {
        parsedEndpoint = new URL(endpoint);
    } catch {
        const error = new Error("AZURE_TRANSLATOR_ENDPOINT must be a valid HTTPS URL.");
        error.statusCode = 503;
        throw error;
    }
    if (parsedEndpoint.protocol !== "https:" || parsedEndpoint.username || parsedEndpoint.password) {
        const error = new Error("AZURE_TRANSLATOR_ENDPOINT must be a valid HTTPS URL.");
        error.statusCode = 503;
        throw error;
    }

    return {
        key: AZURE_TRANSLATOR_KEY,
        region: AZURE_TRANSLATOR_REGION,
        endpoint: parsedEndpoint.origin + parsedEndpoint.pathname.replace(/\/$/, "")
    };
}

async function getUiTranslationStrings() {
    if (uiTranslationStrings) return uiTranslationStrings;

    const html = await readFile(path.join(projectDirectory, "project1.html"), "utf8");
    const readRows = (name) => {
        const marker = `const ${name} = `;
        const start = html.indexOf(marker);
        const literalStart = start < 0 ? -1 : start + marker.length;
        const literalEnd = literalStart < 0 ? -1 : html.indexOf("];", literalStart);
        if (literalStart < 0 || literalEnd < 0) {
            throw new Error("The storefront translation source could not be loaded.");
        }
        return JSON.parse(html.slice(literalStart, literalEnd + 1));
    };

    const rows = [
        ...readRows("translationRows"),
        ...readRows("runtimeTranslationRows")
    ];
    if (!Array.isArray(rows) || rows.some((row) => !Array.isArray(row) || typeof row[0] !== "string")) {
        throw new Error("The storefront translation source has an invalid format.");
    }
    uiTranslationStrings = [...new Set(rows.map((row) => row[0]))];
    return uiTranslationStrings;
}

async function translateUiStringsUncached(language) {
    const credentials = getTranslatorCredentials();
    const strings = await getUiTranslationStrings();
    const translations = Object.create(null);
    const endpoint = new URL(`${credentials.endpoint}/translate`);
    endpoint.searchParams.set("api-version", "3.0");
    endpoint.searchParams.set("to", translatorLanguageCodes[language]);

    for (let offset = 0; offset < strings.length; offset += 50) {
        const batch = strings.slice(offset, offset + 50);
        const placeholders = [];
        const requestBody = batch.map((text) => ({
            Text: text.replace(/\{[\w]+\}/g, (placeholder) => {
                const marker = `ZXQPLACEHOLDER${placeholders.length}QXZ`;
                placeholders.push(placeholder);
                return marker;
            })
        }));
        const response = await fetch(endpoint, {
            method: "POST",
            headers: {
                "Ocp-Apim-Subscription-Key": credentials.key,
                "Ocp-Apim-Subscription-Region": credentials.region,
                "Content-Type": "application/json"
            },
            body: JSON.stringify(requestBody),
            signal: AbortSignal.timeout(30000)
        });
        const result = await response.json().catch(() => null);
        if (!response.ok || !Array.isArray(result) || result.length !== batch.length) {
            console.error("Azure translation request failed:", response.status);
            const error = new Error(
                "The translation service could not translate this language. Check your Azure Translator settings and language support."
            );
            error.statusCode = response.status === 429 ? 503 : 502;
            throw error;
        }

        result.forEach((entry, index) => {
            const translatedText = entry && entry.translations && entry.translations[0] &&
                entry.translations[0].text;
            if (typeof translatedText !== "string") {
                throw new Error("The translation service returned an invalid response.");
            }
            translations[batch[index]] = translatedText.replace(
                /ZXQPLACEHOLDER(\d+)QXZ/g,
                (marker, placeholderIndex) => placeholders[Number(placeholderIndex)] || marker
            );
        });
    }

    return translations;
}

async function translateUiStrings(language) {
    if (uiTranslationCache.has(language)) return uiTranslationCache.get(language);
    if (uiTranslationPending.has(language)) return uiTranslationPending.get(language);

    const pending = translateUiStringsUncached(language);
    uiTranslationPending.set(language, pending);
    try {
        const translations = await pending;
        uiTranslationCache.set(language, translations);
        return translations;
    } finally {
        uiTranslationPending.delete(language);
    }
}

async function handleUiTranslations(request, response) {
    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }

    const body = await readJsonBody(request);
    if (typeof body.language !== "string" ||
        !Object.prototype.hasOwnProperty.call(translatorLanguageCodes, body.language)) {
        sendJson(response, 400, { error: "Choose an available language." });
        return;
    }

    sendJson(response, 200, {
        language: body.language,
        translations: await translateUiStrings(body.language)
    });
}

async function callTwilioVerify(resource, parameters) {
    const { TWILIO_ACCOUNT_SID, TWILIO_AUTH_TOKEN, TWILIO_VERIFY_SERVICE_SID } = getTwilioCredentials();
    const endpoint = `https://verify.twilio.com/v2/Services/${encodeURIComponent(TWILIO_VERIFY_SERVICE_SID)}/${resource}`;
    const authorization = Buffer.from(`${TWILIO_ACCOUNT_SID}:${TWILIO_AUTH_TOKEN}`).toString("base64");
    const response = await fetch(endpoint, {
        method: "POST",
        headers: {
            Authorization: `Basic ${authorization}`,
            "Content-Type": "application/x-www-form-urlencoded"
        },
        body: new URLSearchParams(parameters)
    });
    const result = await response.json().catch(() => ({}));

    if (!response.ok) {
        console.error("Twilio Verify request failed:", response.status, result.code || "");
        const error = new Error("Twilio could not process the request. Check the phone number and server configuration.");
        error.statusCode = 502;
        throw error;
    }

    return result;
}

async function verifyOtpCode(phone, code) {
    if (typeof code !== "string" || !/^\d{4,10}$/.test(code)) {
        const error = new Error("Enter the verification code from the SMS.");
        error.statusCode = 400;
        throw error;
    }

    const expiresAt = verificationExpirations.get(phone);
    if (!expiresAt || Date.now() >= expiresAt) {
        verificationExpirations.delete(phone);
        const error = new Error("Verification code expired. Request a new one.");
        error.statusCode = 400;
        throw error;
    }

    const localCode = localVerificationCodes.get(phone);
    if (localCode) {
        if (
            localCode.length === code.length &&
            timingSafeEqual(Buffer.from(localCode), Buffer.from(code))
        ) {
            localVerificationCodes.delete(phone);
            verificationExpirations.delete(phone);
            return;
        }

        const error = new Error("Invalid verification code.");
        error.statusCode = 400;
        throw error;
    }

    const result = await callTwilioVerify("VerificationCheck", {
        To: phone,
        Code: code
    });
    if (result.status !== "approved") {
        const error = new Error("Invalid verification code.");
        error.statusCode = 400;
        throw error;
    }
    verificationExpirations.delete(phone);
}

function validateNewPassword(password) {
    if (typeof password !== "string" || password.length === 0 || password.length > 1024) {
        const error = new Error("Enter a password up to 1024 characters long.");
        error.statusCode = 400;
        throw error;
    }
}

async function handleRegister(request, response) {
    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }

    const body = await readJsonBody(request);
    const username = typeof body.username === "string" ? body.username.trim() : "";
    const phone = normalizePhone(body.mobile);
    const email = typeof body.email === "string" ? body.email.trim().toLowerCase() : "";
    validateNewPassword(body.password);

    if (!username || username.length > 80) {
        sendJson(response, 400, { error: "Enter a username up to 80 characters long." });
        return;
    }
    if (!phone) {
        sendJson(response, 400, { error: "Enter a valid phone number." });
        return;
    }
    if (!isValidEmail(email)) {
        sendJson(response, 400, { error: "Enter a valid email address." });
        return;
    }

    if (await accountConflict(username, phone, email)) {
        sendJson(response, 409, { error: "An account already exists for that name, mobile number, or email." });
        return;
    }

    await verifyOtpCode(phone, body.code);
    const passwordCredentials = await hashPassword(body.password);
    const inserted = await insertAccount(username, phone, email, passwordCredentials);
    if (!inserted) {
        sendJson(response, 409, { error: "An account already exists for that name, mobile number, or email." });
        return;
    }
    const user = publicUser({ username, mobile: phone, email });
    sendJson(response, 201, {
        user,
        ...createAccountSession(`customer:${phone}`, username)
    });
}

async function handleLogin(request, response) {
    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }

    const body = await readJsonBody(request);
    const identifier = typeof body.identifier === "string" ? body.identifier.trim() : "";
    const password = typeof body.password === "string" ? body.password : "";
    const phone = normalizePhone(identifier);
    const emailKey = identifier.includes("@") ? identifier.toLowerCase() : "";
    const user = await findAccount(identifier, phone, emailKey);

    if (!user || !password || !await verifyPassword(password, user)) {
        sendJson(response, 401, { error: "Invalid name, email/mobile, or password." });
        return;
    }

    sendJson(response, 200, {
        user: publicUser(user),
        ...createAccountSession(`customer:${user.mobile}`, user.username)
    });
}

async function handleAdminRegistration(request, response) {
    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }
    const body = await readJsonBody(request);
    const username = typeof body.username === "string" ? body.username.trim() : "";
    const password = typeof body.password === "string" ? body.password : "";
    const email = typeof body.email === "string" ? body.email.trim().toLowerCase() : "";
    const phone = normalizePhone(body.mobile);
    if (!username || username.length > 80) {
        sendJson(response, 400, { error: "Enter a name up to 80 characters long." });
        return;
    }
    if (password.length < 12 || password.length > 256) {
        sendJson(response, 400, { error: "Passwords must be between 12 and 256 characters." });
        return;
    }
    if (!isValidEmail(email)) {
        sendJson(response, 400, { error: "Enter a valid email address." });
        return;
    }
    if (!phone) {
        sendJson(response, 400, { error: "Enter a valid mobile number." });
        return;
    }

    const existing = database.prepare(`
        SELECT id FROM administrators
        WHERE username_key = ? OR email_key = ? OR mobile = ?
        LIMIT 1
    `).get(username.toLowerCase(), email, phone);
    if (existing) {
        sendJson(response, 409, { error: "A seller account already exists for that name, email, or mobile number." });
        return;
    }

    await verifyOtpCode(phone, body.code);
    const credentials = await hashPassword(password);
    try {
        const inserted = database.prepare(`
            INSERT INTO administrators
                (username, username_key, email, email_key, mobile, password_salt, password_hash)
            VALUES (?, ?, ?, ?, ?, ?, ?)
        `).run(
            username,
            username.toLocaleLowerCase(),
            email,
            email,
            phone,
            credentials.passwordSalt,
            credentials.passwordHash
        );
        const admin = { id: Number(inserted.lastInsertRowid), username };
        sendJson(response, 201, {
            user: { username, email, mobile: phone },
            ...createAdminSession(admin)
        });
    } catch (error) {
        if (error.errcode === 2067 || error.code === "ERR_SQLITE_CONSTRAINT_UNIQUE") {
            sendJson(response, 409, { error: "A seller account already exists for that name, email, or mobile number." });
            return;
        }
        throw error;
    }
}

async function handleAdminLogin(request, response) {
    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }
    const body = await readJsonBody(request);
    const identifier = typeof body.identifier === "string" ? body.identifier.trim() : "";
    const password = typeof body.password === "string" ? body.password : "";
    const phone = normalizePhone(identifier);
    const emailKey = identifier.includes("@") ? identifier.toLowerCase() : "";
    const admin = database.prepare(`
        SELECT id, username, email, mobile,
               password_salt AS passwordSalt, password_hash AS passwordHash
        FROM administrators
        WHERE username_key = ? OR email_key = ? OR mobile = ?
        LIMIT 1
    `)
        .get(identifier.toLocaleLowerCase(), emailKey, phone || "");
    if (!admin || !password || !await verifyPassword(password, admin)) {
        sendJson(response, 401, { error: "Name, email/mobile, or password does not match a seller account." });
        return;
    }
    sendJson(response, 200, {
        user: { username: admin.username, email: admin.email || "", mobile: admin.mobile || "" },
        ...createAdminSession(admin)
    });
}

async function verifyGoogleCredential(body, response) {
    if (typeof body.credential !== "string" || body.credential.length === 0) {
        sendJson(response, 400, { error: "Google did not provide a sign-in credential." });
        return null;
    }

    loadLocalEnvironment();
    const clientId = process.env.GOOGLE_CLIENT_ID;
    if (!clientId) {
        sendJson(response, 503, { error: "Google sign-in is not configured. Add GOOGLE_CLIENT_ID to the local .env file." });
        return null;
    }

    const tokenInfoUrl = new URL("https://oauth2.googleapis.com/tokeninfo");
    tokenInfoUrl.searchParams.set("id_token", body.credential);
    const googleResponse = await fetch(tokenInfoUrl);
    const claims = await googleResponse.json().catch(() => ({}));
    const validIssuer = claims.iss === "accounts.google.com" || claims.iss === "https://accounts.google.com";
    const emailVerified = claims.email_verified === "true" || claims.email_verified === true;
    if (!googleResponse.ok || claims.aud !== clientId || !validIssuer ||
        !emailVerified || !claims.email || !claims.sub) {
        sendJson(response, 401, { error: "Google sign-in could not be verified." });
        return null;
    }
    return claims;
}

async function handleAdminGoogleAuth(request, response) {
    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }
    const body = await readJsonBody(request);
    const claims = await verifyGoogleCredential(body, response);
    if (!claims) return;
    const email = claims.email.trim().toLocaleLowerCase();
    const displayName = typeof claims.name === "string" && claims.name.trim()
        ? claims.name.trim()
        : email;
    let admin = database.prepare("SELECT * FROM administrators WHERE google_sub = ?").get(claims.sub);
    if (!admin) {
        admin = database.prepare(`
            SELECT * FROM administrators
            WHERE email_key = ? OR lower(email) = ?
            LIMIT 1
        `).get(email, email);
        if (!admin) {
            sendJson(response, 404, {
                error: `No seller account is registered for ${email}. Create an account with this email and verify your mobile first.`
            });
            return;
        }
        if (!admin.mobile) {
            sendJson(response, 403, {
                error: "This seller account needs a verified mobile number. Sign in with its password and update its profile."
            });
            return;
        }
        database.prepare("UPDATE administrators SET google_sub = ?, email_key = ? WHERE id = ?")
            .run(claims.sub, email, admin.id);
    } else {
        if (!admin.mobile) {
            sendJson(response, 403, {
                error: "This seller account needs a verified mobile number. Sign in with its password and update its profile."
            });
            return;
        }
        database.prepare("UPDATE administrators SET email = ?, email_key = ? WHERE id = ?")
            .run(email, email, admin.id);
    }
    sendJson(response, 200, {
        user: { username: admin.username },
        ...createAdminSession(admin)
    });
}

async function handlePasswordReset(request, response) {
    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }

    const body = await readJsonBody(request);
    const phone = normalizePhone(body.mobile);
    validateNewPassword(body.password);
    if (!phone) {
        sendJson(response, 400, { error: "Enter a valid phone number." });
        return;
    }

    await verifyOtpCode(phone, body.code);
    const passwordCredentials = await hashPassword(body.password);
    const updated = await updateAccountPassword(phone, passwordCredentials);
    if (!updated) {
        sendJson(response, 404, { error: "No account was found for that mobile number." });
        return;
    }
    const user = await findAccountByPhone(phone);
    sendJson(response, 200, { user: publicUser(user) });
}

async function handleGoogleAuth(request, response) {
    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }

    const body = await readJsonBody(request);
    if (typeof body.credential !== "string" || body.credential.length === 0) {
        sendJson(response, 400, { error: "Google did not provide a sign-in credential." });
        return;
    }

    loadLocalEnvironment();
    const clientId = process.env.GOOGLE_CLIENT_ID;
    if (!clientId) {
        sendJson(response, 503, { error: "Google sign-in is not configured. Add GOOGLE_CLIENT_ID to the local .env file." });
        return;
    }

    const tokenInfoUrl = new URL("https://oauth2.googleapis.com/tokeninfo");
    tokenInfoUrl.searchParams.set("id_token", body.credential);
    const googleResponse = await fetch(tokenInfoUrl);
    const claims = await googleResponse.json().catch(() => ({}));
    const validIssuer = claims.iss === "accounts.google.com" || claims.iss === "https://accounts.google.com";
    const emailVerified = claims.email_verified === "true" || claims.email_verified === true;

    if (
        !googleResponse.ok ||
        claims.aud !== clientId ||
        !validIssuer ||
        !emailVerified ||
        !claims.email ||
        !claims.sub
    ) {
        sendJson(response, 401, { error: "Google sign-in could not be verified." });
        return;
    }

    const name = claims.name || claims.email;
    await saveGoogleAccount(claims.sub, claims.email, name);
    sendJson(response, 200, {
        authenticated: true,
        email: claims.email,
        name,
        ...createAccountSession(`google:${claims.sub}`, name)
    });
}

async function handleApiRequest(request, response, pathname) {
    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }

    const body = await readJsonBody(request);
    const phone = normalizePhone(body.phone);
    if (!phone) {
        sendJson(response, 400, { error: "Enter a valid phone number. For India, enter 10 digits or +91 followed by 10 digits." });
        return;
    }

    if (pathname === "/api/auth/password-reset/send") {
        const user = await findAccountByPhone(phone);
        if (!user) {
            sendJson(response, 404, { error: "No account was found for that mobile number." });
            return;
        }
    }

    let useLocalVerification = false;
    if (!hasTwilioCredentials()) {
        if (process.env.NODE_ENV === "production") getTwilioCredentials();
        useLocalVerification = process.env.NODE_ENV !== "production";
    } else {
        try {
            await callTwilioVerify("Verifications", {
                To: phone,
                Channel: "sms"
            });
        } catch (error) {
            if (process.env.NODE_ENV === "production") throw error;
            console.warn("Twilio verification unavailable; using hidden local verification.");
            useLocalVerification = true;
        }
    }

    verificationExpirations.set(phone, Date.now() + otpValidityMs);
    if (useLocalVerification) {
        const code = String(100000 + randomBytes(3).readUIntBE(0, 3) % 900000);
        localVerificationCodes.set(phone, code);
        console.log(`Local verification code for ${phone}: ${code}`);
    }
    sendJson(response, 200, {
        sent: true,
        expiresInSeconds: 60
    });
}

function formatProduct(row) {
    const storedImages = JSON.parse(row.images_json || "[]");
    const images = Array.isArray(storedImages)
        ? storedImages.filter((image) => typeof image === "string" && image.length > 0)
        : [];
    const storedEmiTenures = JSON.parse(row.emi_tenures_json || "[]");
    const emiTenures = Array.isArray(storedEmiTenures)
        ? storedEmiTenures.filter((months) => Number.isSafeInteger(months) && supportedEmiTenures.has(months))
        : [];
    if (images.length === 0 && row.image) images.push(row.image);
    return {
        id: row.id,
        name: row.name,
        description: row.description,
        category: row.category,
        pricePaise: row.price_paise,
        offer: row.offer,
        image: images[0] || row.image,
        images,
        stock: row.stock,
        viewCount: row.view_count || 0,
        emiTenures
    };
}

function validateProduct(body) {
    const name = typeof body.name === "string" ? body.name.trim() : "";
    const description = typeof body.description === "string" ? body.description.trim() : "";
    const category = typeof body.category === "string" ? body.category : "";
    const offer = typeof body.offer === "string" ? body.offer.trim() : "";
    const legacyImage = typeof body.image === "string" ? body.image.trim() : "";
    const images = Array.isArray(body.images)
        ? body.images.map((image) => typeof image === "string" ? image.trim() : "")
        : legacyImage ? [legacyImage] : [];
    const requestedEmiTenures = body.emiTenures === undefined ? [] : body.emiTenures;
    const pricePaise = Number(body.pricePaise);
    const stock = Number(body.stock);

    if (!name || name.length > 120) {
        return { error: "Product name is required and must be 120 characters or fewer." };
    }
    if (description.length > 2000) {
        return { error: "Product description must be 2,000 characters or fewer." };
    }
    if (!productCategories.has(category)) {
        return { error: "Choose a valid product category." };
    }
    if (!Number.isSafeInteger(pricePaise) || pricePaise < 1 || pricePaise > 10000000000) {
        return { error: "Enter a valid product price." };
    }
    if (!Number.isSafeInteger(stock) || stock < 0 || stock > 1000000) {
        return { error: "Stock must be a whole number between 0 and 1,000,000." };
    }
    if (offer.length > 40) {
        return { error: "Offer text must be 40 characters or fewer." };
    }
    if (!Array.isArray(requestedEmiTenures) ||
        requestedEmiTenures.some((months) => !Number.isSafeInteger(months) || !supportedEmiTenures.has(months)) ||
        new Set(requestedEmiTenures).size !== requestedEmiTenures.length) {
        return { error: "Choose valid EMI tenures: 3, 6, 9, or 12 months." };
    }
    if (images.length === 0 || images.length > maximumProductImages ||
        images.some((image) => !isValidProductImage(image))) {
        return { error: `Choose between 1 and ${maximumProductImages} valid JPG, PNG, WebP, or HTTP(S) image URLs. Uploaded images must be under 2 MB each.` };
    }

    const emiTenures = [...requestedEmiTenures].sort((left, right) => left - right);
    return { product: { name, description, category, pricePaise, offer, image: images[0], images, stock, emiTenures } };
}

function isValidProductImage(image) {
    const dataImage = image.match(/^data:image\/(?:jpeg|png|webp);base64,([A-Za-z0-9+/]+={0,2})$/i);
    if (dataImage) {
        return Buffer.from(dataImage[1], "base64").byteLength <= maximumImageBytes;
    }

    try {
        const url = new URL(image);
        return ["http:", "https:"].includes(url.protocol);
    } catch {
        return false;
    }
}

async function handleAdminProducts(request, response, pathname) {
    const session = getAdminSession(request);
    if (!session) {
        sendJson(response, 401, { error: "Sign in with the separate admin account to manage products." });
        return;
    }

    if (pathname === "/api/admin/products" && request.method === "GET") {
        const products = database.prepare(`
            SELECT * FROM products
            WHERE owner_key = ?
            ORDER BY created_at DESC, id DESC
        `).all(session.ownerKey);
        sendJson(response, 200, { products: products.map(formatProduct) });
        return;
    }

    if (pathname === "/api/admin/products" && request.method === "POST") {
        const body = await readJsonBody(request, productBodyLimit);
        const validation = validateProduct(body);
        if (validation.error) {
            sendJson(response, 400, { error: validation.error });
            return;
        }
        const product = validation.product;
        const result = database.prepare(`
            INSERT INTO products (name, description, category, price_paise, offer, image, images_json, stock, emi_tenures_json, owner_key)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
        `).run(
            product.name,
            product.description,
            product.category,
            product.pricePaise,
            product.offer,
            product.image,
            JSON.stringify(product.images),
            product.stock,
            JSON.stringify(product.emiTenures),
            session.ownerKey
        );
        const created = database.prepare("SELECT * FROM products WHERE id = ?").get(result.lastInsertRowid);
        sendJson(response, 201, { product: formatProduct(created) });
        return;
    }

    const productId = Number(pathname.slice("/api/admin/products/".length));
    if (!Number.isSafeInteger(productId) || productId < 1) {
        sendJson(response, 404, { error: "Product not found." });
        return;
    }

    if (request.method === "PUT") {
        const body = await readJsonBody(request, productBodyLimit);
        const validation = validateProduct(body);
        if (validation.error) {
            sendJson(response, 400, { error: validation.error });
            return;
        }
        const product = validation.product;
        const result = database.prepare(`
            UPDATE products
            SET name = ?, description = ?, category = ?, price_paise = ?, offer = ?, image = ?, images_json = ?, stock = ?, emi_tenures_json = ?,
                updated_at = CURRENT_TIMESTAMP
            WHERE id = ? AND owner_key = ?
        `).run(
            product.name,
            product.description,
            product.category,
            product.pricePaise,
            product.offer,
            product.image,
            JSON.stringify(product.images),
            product.stock,
            JSON.stringify(product.emiTenures),
            productId,
            session.ownerKey
        );
        if (result.changes === 0) {
            sendJson(response, 404, { error: "Product not found." });
            return;
        }
        const updated = database.prepare("SELECT * FROM products WHERE id = ?").get(productId);
        sendJson(response, 200, { product: formatProduct(updated) });
        return;
    }

    if (request.method === "DELETE") {
        const result = database.prepare("DELETE FROM products WHERE id = ? AND owner_key = ?")
            .run(productId, session.ownerKey);
        if (result.changes === 0) {
            sendJson(response, 404, { error: "Product not found." });
            return;
        }
        sendJson(response, 200, { deleted: true });
        return;
    }

    sendJson(response, 405, { error: "Method not allowed." });
}

async function handleCreateOrder(request, response) {
    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }

    const body = await readJsonBody(request);
    const customerName = typeof body.customerName === "string" ? body.customerName.trim() : "";
    const customerMobile = normalizePhone(body.customerMobile);
    const paymentMethods = new Set(["cash_on_delivery"]);
    const paymentMethod = typeof body.paymentMethod === "string" ? body.paymentMethod : "cash_on_delivery";
    if (!paymentMethods.has(paymentMethod)) {
        sendJson(response, 400, { error: "Choose a valid payment method." });
        return;
    }
    const rawAddress = body.shippingAddress;
    let shippingAddress = "";
    let addressError = "";
    if (typeof rawAddress === "string") {
        shippingAddress = rawAddress.trim();
    } else if (rawAddress && typeof rawAddress === "object" && !Array.isArray(rawAddress)) {
        const fields = {
            "Address line 1": rawAddress.line1,
            "Street / area": rawAddress.street,
            City: rawAddress.city,
            District: rawAddress.district,
            State: rawAddress.state,
            Country: rawAddress.country,
            "PIN / postal code": rawAddress.pincode
        };
        const limits = {
            "Address line 1": 200,
            "Street / area": 120,
            City: 100,
            District: 100,
            State: 100,
            Country: 100,
            "PIN / postal code": 12
        };
        const normalizedFields = {};
        for (const [label, value] of Object.entries(fields)) {
            const text = typeof value === "string" ? value.trim() : "";
            if (!text || text.length > limits[label]) {
                addressError = "Complete every delivery address field using the allowed length.";
                break;
            }
            normalizedFields[label] = text;
        }
        if (!addressError) {
            const pincode = normalizedFields["PIN / postal code"];
            const country = normalizedFields.Country;
            const isIndia = country.toLowerCase() === "india";
            if (isIndia ? !/^\d{6}$/.test(pincode) : !/^[A-Za-z0-9](?:[A-Za-z0-9 -]{0,10}[A-Za-z0-9])$/.test(pincode)) {
                addressError = isIndia
                    ? "Enter a valid 6-digit PIN code."
                    : "Enter a valid postal code.";
            } else {
                shippingAddress = Object.entries(normalizedFields)
                    .map(([label, value]) => `${label}: ${value}`)
                    .join("\n");
                const hasLatitude = rawAddress.latitude !== undefined && String(rawAddress.latitude).trim() !== "";
                const hasLongitude = rawAddress.longitude !== undefined && String(rawAddress.longitude).trim() !== "";
                if (hasLatitude || hasLongitude) {
                    const latitude = Number(rawAddress.latitude);
                    const longitude = Number(rawAddress.longitude);
                    if (!hasLatitude || !hasLongitude || !Number.isFinite(latitude) || !Number.isFinite(longitude) ||
                        latitude < -90 || latitude > 90 || longitude < -180 || longitude > 180) {
                        addressError = "Choose a valid map location.";
                    } else {
                        shippingAddress += `\nMap coordinates: ${latitude.toFixed(6)}, ${longitude.toFixed(6)}`;
                    }
                }
            }
        }
    } else {
        addressError = "Enter all delivery address fields.";
    }
    const items = Array.isArray(body.items) ? body.items : [];
    if (!customerName || customerName.length > 120) {
        sendJson(response, 400, { error: "Enter your name (up to 120 characters)." });
        return;
    }
    if (!customerMobile) {
        sendJson(response, 400, { error: "Enter a valid mobile number (10 digits or an international number such as +91 followed by 10 digits)." });
        return;
    }
    if (addressError) {
        sendJson(response, 400, { error: addressError });
        return;
    }
    if (!shippingAddress || shippingAddress.length > 1000) {
        sendJson(response, 400, { error: "Complete your delivery address." });
        return;
    }
    if (items.length === 0 || items.length > 50) {
        sendJson(response, 400, { error: "Select at least one product to place your order." });
        return;
    }

    const quantities = new Map();
    for (const item of items) {
        const productId = Number(item.productId);
        const quantity = Number(item.quantity);
        if (!Number.isSafeInteger(productId) || productId < 1 ||
            !Number.isSafeInteger(quantity) || quantity < 1 || quantity > 99) {
            sendJson(response, 400, { error: "One of the selected products or quantities is invalid." });
            return;
        }
        quantities.set(productId, (quantities.get(productId) || 0) + quantity);
        if (quantities.get(productId) > 99) {
            sendJson(response, 400, { error: "A product quantity cannot exceed 99." });
            return;
        }
    }

    const orderNumber = `ZK-${randomBytes(4).toString("hex").toUpperCase()}`;
    let orderId;
    let totalPaise = 0;
    database.exec("BEGIN IMMEDIATE");
    try {
        const selectedProducts = [];
        for (const [productId, quantity] of quantities) {
            const product = database.prepare("SELECT * FROM products WHERE id = ?").get(productId);
            if (!product || product.stock < quantity) {
                const error = new Error(product ? `${product.name} does not have enough stock.` : "A selected product is no longer available.");
                error.statusCode = 409;
                throw error;
            }
            totalPaise += product.price_paise * quantity;
            selectedProducts.push({ product, quantity });
        }
        if (new Set(selectedProducts.map((item) => item.product.owner_key)).size > 1) {
            const error = new Error("Place separate orders for products from different sellers.");
            error.statusCode = 400;
            throw error;
        }
        const orderResult = database.prepare(`
            INSERT INTO orders (
                order_number, customer_name, customer_mobile, shipping_address,
                payment_method, payment_status, status, total_paise
            ) VALUES (?, ?, ?, ?, ?, 'pending', 'received', ?)
        `).run(orderNumber, customerName, customerMobile, shippingAddress, paymentMethod, totalPaise);
        orderId = orderResult.lastInsertRowid;

        const insertItem = database.prepare(`
            INSERT INTO order_items (order_id, product_id, product_name, unit_price_paise, quantity, owner_key)
            VALUES (?, ?, ?, ?, ?, ?)
        `);
        const reserveStock = database.prepare(
            "UPDATE products SET stock = stock - ?, updated_at = CURRENT_TIMESTAMP WHERE id = ? AND stock >= ?"
        );
        for (const item of selectedProducts) {
            insertItem.run(
                orderId,
                item.product.id,
                item.product.name,
                item.product.price_paise,
                item.quantity,
                item.product.owner_key
            );
            const result = reserveStock.run(item.quantity, item.product.id, item.quantity);
            if (result.changes !== 1) {
                const error = new Error(`${item.product.name} no longer has enough stock.`);
                error.statusCode = 409;
                throw error;
            }
        }
        database.exec("COMMIT");
    } catch (error) {
        database.exec("ROLLBACK");
        throw error;
    }

    sendJson(response, 201, {
        orderNumber,
        totalPaise,
        paymentMethod,
        paymentStatus: "pending",
        status: "received"
    });
}

function handleTrackOrder(request, response, pathname, searchParams) {
    if (request.method !== "GET") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }
    const orderNumber = pathname.slice("/api/orders/".length);
    const mobile = normalizePhone(searchParams.get("mobile"));
    if (!mobile || !/^ZK-[A-F0-9]{8}$/.test(orderNumber)) {
        sendJson(response, 400, { error: "Enter the order number and mobile used at checkout." });
        return;
    }
    const order = database.prepare(`
        SELECT id, order_number, payment_method, payment_status, status, tracking_number,
               total_paise, created_at
        FROM orders
        WHERE order_number = ? AND customer_mobile = ?
    `).get(orderNumber, mobile);
    if (!order) {
        sendJson(response, 404, { error: "No order was found for those details." });
        return;
    }
    sendJson(response, 200, { order: getOrderWithItems(order) });
}

function handleCustomerOrders(request, response) {
    if (request.method !== "GET") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }

    const session = getAccountSession(request);
    if (!session) {
        sendJson(response, 401, { error: "Sign in to view your orders." });
        return;
    }
    if (!session.ownerKey.startsWith("customer:")) {
        sendJson(response, 403, { error: "This account is not linked to a customer mobile number." });
        return;
    }

    const mobile = normalizePhone(session.ownerKey.slice("customer:".length));
    if (!mobile) {
        sendJson(response, 403, { error: "This account is not linked to a valid customer mobile number." });
        return;
    }

    const orders = database.prepare(`
        SELECT id, order_number, customer_name, customer_mobile, shipping_address,
               payment_method, payment_status, status, tracking_number,
               total_paise, created_at
        FROM orders
        WHERE customer_mobile = ?
        ORDER BY created_at DESC, id DESC
    `).all(mobile);
    sendJson(response, 200, { orders: orders.map((order) => getOrderWithItems(order)) });
}

function getOrderWithItems(order, ownerKey) {
    const items = ownerKey
        ? database.prepare(`
        SELECT product_id AS productId, product_name AS name,
               unit_price_paise AS unitPricePaise, quantity
        FROM order_items
        WHERE order_id = ? AND owner_key = ?
    `).all(order.id, ownerKey)
        : database.prepare(`
            SELECT product_id AS productId, product_name AS name,
                   unit_price_paise AS unitPricePaise, quantity
            FROM order_items
            WHERE order_id = ?
        `).all(order.id);
    return { ...order, items };
}

function getCustomerMobileFromSession(request, response) {
    const session = getAccountSession(request);
    if (!session) {
        sendJson(response, 401, { error: "Sign in to manage your account." });
        return null;
    }
    if (!session.ownerKey.startsWith("customer:")) {
        sendJson(response, 403, { error: "This feature requires an account with a registered mobile number." });
        return null;
    }
    const mobile = normalizePhone(session.ownerKey.slice("customer:".length));
    if (!mobile) {
        sendJson(response, 403, { error: "This account is not linked to a valid customer mobile number." });
        return null;
    }
    return { session, mobile };
}

function normalizeAddress(body) {
    const labels = new Set(["Home", "Office", "Other"]);
    const fields = {
        label: { value: body.label, max: 20 },
        recipientName: { value: body.recipientName, max: 120 },
        mobile: { value: body.mobile, max: 30 },
        line1: { value: body.line1, max: 200 },
        street: { value: body.street, max: 120 },
        city: { value: body.city, max: 100 },
        district: { value: body.district, max: 100 },
        state: { value: body.state, max: 100 },
        country: { value: body.country, max: 100 },
        pincode: { value: body.pincode, max: 12 }
    };
    const result = {};
    for (const [key, field] of Object.entries(fields)) {
        if (typeof field.value !== "string" || !field.value.trim() || field.value.trim().length > field.max) {
            return { error: "Complete every address field using the allowed length." };
        }
        result[key] = field.value.trim();
    }
    if (!labels.has(result.label)) return { error: "Choose Home, Office, or Other for this address." };
    if (!normalizePhone(result.mobile)) return { error: "Enter a valid phone number for this address." };
    if (result.country.toLowerCase() === "india"
        ? !/^\d{6}$/.test(result.pincode)
        : !/^[A-Za-z0-9](?:[A-Za-z0-9 -]{0,10}[A-Za-z0-9])$/.test(result.pincode)) {
        return { error: result.country.toLowerCase() === "india"
            ? "Enter a valid 6-digit PIN code."
            : "Enter a valid postal code." };
    }
    return { address: result };
}

async function handleCustomerAddresses(request, response, pathname) {
    const account = getAccountSession(request);
    if (!account) {
        sendJson(response, 401, { error: "Sign in to manage saved addresses." });
        return;
    }
    const addressMatch = pathname.match(/^\/api\/account\/addresses\/(\d+)(\/default)?$/);
    if (request.method === "GET" && pathname === "/api/account/addresses") {
        const addresses = database.prepare(`
            SELECT id, label, recipient_name AS recipientName, mobile, line1, street, city,
                   district, state, country, pincode, is_default AS isDefault
            FROM customer_addresses WHERE owner_key = ? ORDER BY is_default DESC, id DESC
        `).all(account.ownerKey);
        sendJson(response, 200, { addresses });
        return;
    }
    if (request.method === "POST" && pathname === "/api/account/addresses") {
        const body = await readJsonBody(request);
        const parsed = normalizeAddress(body);
        if (parsed.error) {
            sendJson(response, 400, { error: parsed.error });
            return;
        }
        let addressId;
        database.exec("BEGIN IMMEDIATE");
        try {
            const existingCount = database.prepare(
                "SELECT COUNT(*) AS count FROM customer_addresses WHERE owner_key = ?"
            ).get(account.ownerKey).count;
            if (existingCount >= 20) {
                const error = new Error("You can save up to 20 addresses.");
                error.statusCode = 409;
                throw error;
            }
            const makeDefault = body.isDefault === true || existingCount === 0;
            if (makeDefault) {
                database.prepare("UPDATE customer_addresses SET is_default = 0 WHERE owner_key = ?")
                    .run(account.ownerKey);
            }
            const address = parsed.address;
            const result = database.prepare(`
                INSERT INTO customer_addresses (
                    owner_key, label, recipient_name, mobile, line1, street, city,
                    district, state, country, pincode, is_default
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            `).run(account.ownerKey, address.label, address.recipientName, address.mobile,
                address.line1, address.street, address.city, address.district, address.state,
                address.country, address.pincode, makeDefault ? 1 : 0);
            addressId = Number(result.lastInsertRowid);
            database.exec("COMMIT");
        } catch (error) {
            database.exec("ROLLBACK");
            throw error;
        }
        sendJson(response, 201, { id: addressId, saved: true });
        return;
    }
    if (!addressMatch) {
        sendJson(response, 404, { error: "Address not found." });
        return;
    }
    const addressId = Number(addressMatch[1]);
    const address = database.prepare(
        "SELECT id, is_default FROM customer_addresses WHERE id = ? AND owner_key = ?"
    ).get(addressId, account.ownerKey);
    if (!address) {
        sendJson(response, 404, { error: "Address not found." });
        return;
    }
    if (addressMatch[2] && request.method === "PATCH") {
        database.exec("BEGIN IMMEDIATE");
        try {
            database.prepare("UPDATE customer_addresses SET is_default = 0 WHERE owner_key = ?")
                .run(account.ownerKey);
            database.prepare(`
                UPDATE customer_addresses SET is_default = 1, updated_at = CURRENT_TIMESTAMP
                WHERE id = ? AND owner_key = ?
            `).run(addressId, account.ownerKey);
            database.exec("COMMIT");
        } catch (error) {
            database.exec("ROLLBACK");
            throw error;
        }
        sendJson(response, 200, { saved: true });
        return;
    }
    if (request.method === "PUT" && !addressMatch[2]) {
        const body = await readJsonBody(request);
        const parsed = normalizeAddress(body);
        if (parsed.error) {
            sendJson(response, 400, { error: parsed.error });
            return;
        }
        const makeDefault = body.isDefault === true || Boolean(address.is_default);
        database.exec("BEGIN IMMEDIATE");
        try {
            if (makeDefault) {
                database.prepare("UPDATE customer_addresses SET is_default = 0 WHERE owner_key = ?")
                    .run(account.ownerKey);
            }
            const item = parsed.address;
            database.prepare(`
                UPDATE customer_addresses SET label = ?, recipient_name = ?, mobile = ?, line1 = ?,
                    street = ?, city = ?, district = ?, state = ?, country = ?, pincode = ?,
                    is_default = ?, updated_at = CURRENT_TIMESTAMP
                WHERE id = ? AND owner_key = ?
            `).run(item.label, item.recipientName, item.mobile, item.line1, item.street, item.city,
                item.district, item.state, item.country, item.pincode, makeDefault ? 1 : 0,
                addressId, account.ownerKey);
            database.exec("COMMIT");
        } catch (error) {
            database.exec("ROLLBACK");
            throw error;
        }
        sendJson(response, 200, { saved: true });
        return;
    }
    if (request.method === "DELETE" && !addressMatch[2]) {
        database.exec("BEGIN IMMEDIATE");
        try {
            database.prepare("DELETE FROM customer_addresses WHERE id = ? AND owner_key = ?")
                .run(addressId, account.ownerKey);
            if (address.is_default) {
                database.prepare(`
                    UPDATE customer_addresses SET is_default = 1, updated_at = CURRENT_TIMESTAMP
                    WHERE id = (
                        SELECT id FROM customer_addresses WHERE owner_key = ? ORDER BY id DESC LIMIT 1
                    )
                `).run(account.ownerKey);
            }
            database.exec("COMMIT");
        } catch (error) {
            database.exec("ROLLBACK");
            throw error;
        }
        sendJson(response, 200, { deleted: true });
        return;
    }
    sendJson(response, 405, { error: "Method not allowed." });
}

async function handleCustomerOrderRequests(request, response) {
    const account = getCustomerMobileFromSession(request, response);
    if (!account) return;
    if (request.method === "GET") {
        const requests = database.prepare(`
            SELECT r.id, o.order_number AS orderNumber, r.request_type AS type, r.reason,
                   r.request_status AS status, r.refund_status AS refundStatus,
                   r.pickup_status AS pickupStatus, r.created_at AS createdAt
            FROM account_order_requests r
            JOIN orders o ON o.id = r.order_id
            WHERE r.customer_mobile = ?
            ORDER BY r.created_at DESC, r.id DESC
        `).all(account.mobile);
        sendJson(response, 200, { requests });
        return;
    }
    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }
    const body = await readJsonBody(request);
    const orderNumber = typeof body.orderNumber === "string" ? body.orderNumber.trim() : "";
    const type = typeof body.type === "string" ? body.type : "";
    const reason = typeof body.reason === "string" ? body.reason.trim() : "";
    if (!/^ZK-[A-F0-9]{8}$/.test(orderNumber) ||
        !["cancellation", "return"].includes(type) ||
        reason.length < 3 || reason.length > 500) {
        sendJson(response, 400, { error: "Choose an order and request type, and enter a reason of 3 to 500 characters." });
        return;
    }
    const order = database.prepare(`
        SELECT id, status FROM orders WHERE order_number = ? AND customer_mobile = ?
    `).get(orderNumber, account.mobile);
    if (!order) {
        sendJson(response, 404, { error: "Order not found in your account." });
        return;
    }
    const eligibleStatuses = type === "cancellation" ? ["received", "packing"] : ["delivered"];
    if (!eligibleStatuses.includes(order.status)) {
        sendJson(response, 409, { error: type === "cancellation"
            ? "Cancellation requests are available only before an order ships."
            : "A return request can be submitted after delivery for eligibility review." });
        return;
    }
    try {
        database.prepare(`
            INSERT INTO account_order_requests (order_id, customer_mobile, request_type, reason)
            VALUES (?, ?, ?, ?)
        `).run(order.id, account.mobile, type, reason);
    } catch (error) {
        if (error.errcode === 2067) {
            sendJson(response, 409, { error: `A ${type} request has already been submitted for this order.` });
            return;
        }
        throw error;
    }
    sendJson(response, 201, { submitted: true, status: "submitted" });
}

async function handleCustomerSupport(request, response) {
    const account = getAccountSession(request);
    if (!account) {
        sendJson(response, 401, { error: "Sign in to view or raise a support ticket." });
        return;
    }
    if (request.method === "GET") {
        const tickets = database.prepare(`
            SELECT support_tickets.id, support_tickets.category, support_tickets.subject,
                   support_tickets.message, support_tickets.status,
                   support_tickets.created_at AS createdAt, support_tickets.product_id AS productId,
                   products.name AS productName, administrators.username AS sellerName
            FROM support_tickets
            LEFT JOIN products ON products.id = support_tickets.product_id
            LEFT JOIN administrators ON administrators.id = support_tickets.admin_id
            WHERE support_tickets.owner_key = ? ORDER BY support_tickets.id DESC
        `).all(account.ownerKey);
        sendJson(response, 200, { tickets });
        return;
    }
    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }
    const body = await readJsonBody(request);
    const categories = new Set(["order", "return", "delivery", "payment", "account", "product_issue", "other"]);
    const category = typeof body.category === "string" ? body.category : "";
    const subject = typeof body.subject === "string" ? body.subject.trim() : "";
    const message = typeof body.message === "string" ? body.message.trim() : "";
    const productId = body.productId === undefined || body.productId === ""
        ? null
        : Number(body.productId);
    if (!categories.has(category) || subject.length < 3 || subject.length > 120 ||
        message.length < 10 || message.length > 2000) {
        sendJson(response, 400, { error: "Choose a support topic, a subject of 3 to 120 characters, and a message of 10 to 2,000 characters." });
        return;
    }
    if (category === "product_issue" &&
        (!Number.isSafeInteger(productId) || productId < 1)) {
        sendJson(response, 400, { error: "Choose the product related to this issue." });
        return;
    }
    let seller = null;
    if (productId !== null) {
        const product = database.prepare("SELECT id, owner_key FROM products WHERE id = ?").get(productId);
        const customerMobile = account.ownerKey.startsWith("customer:")
            ? normalizePhone(account.ownerKey.slice("customer:".length))
            : null;
        const orderedProduct = customerMobile && database.prepare(`
            SELECT 1
            FROM orders
            JOIN order_items ON order_items.order_id = orders.id
            WHERE orders.customer_mobile = ? AND order_items.product_id = ?
            LIMIT 1
        `).get(customerMobile, productId);
        if (!orderedProduct) {
            sendJson(response, 403, { error: "Product complaints can only be raised for a product in your order history." });
            return;
        }
        const ownerMatch = product && product.owner_key.match(/^admin:(\d+)$/);
        seller = ownerMatch
            ? database.prepare("SELECT id FROM administrators WHERE id = ?").get(Number(ownerMatch[1]))
            : null;
        if (!product || !seller) {
            sendJson(response, 400, { error: "The selected product does not have an active seller account." });
            return;
        }
    }
    const requesterName = (account.displayName || "").slice(0, 120);
    let requesterContact = "";
    if (account.ownerKey.startsWith("customer:")) {
        requesterContact = normalizePhone(account.ownerKey.slice("customer:".length)) || "";
    } else if (account.ownerKey.startsWith("google:")) {
        const googleAccount = database.prepare("SELECT email FROM google_accounts WHERE google_sub = ?")
            .get(account.ownerKey.slice("google:".length));
        requesterContact = googleAccount ? googleAccount.email : "";
    }
    const result = database.prepare(`
        INSERT INTO support_tickets (
            owner_key, category, subject, message, product_id, admin_id, requester_name, requester_contact
        ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
    `).run(
        account.ownerKey,
        category,
        subject,
        message,
        productId,
        seller ? seller.id : null,
        requesterName,
        requesterContact
    );
    sendJson(response, 201, {
        id: Number(result.lastInsertRowid),
        status: "open",
        routedToSeller: Boolean(seller)
    });
}

function handleAdminProductTickets(request, response) {
    const session = getAdminSession(request);
    if (!session) {
        sendJson(response, 401, { error: "Sign in with the seller account to view product tickets." });
        return;
    }
    if (request.method !== "GET") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }
    const tickets = database.prepare(`
        SELECT support_tickets.id, support_tickets.category, support_tickets.subject,
               support_tickets.message, support_tickets.status,
               support_tickets.requester_name AS requesterName,
               support_tickets.requester_contact AS requesterContact,
               support_tickets.created_at AS createdAt,
               products.name AS productName, support_tickets.product_id AS productId
        FROM support_tickets
        LEFT JOIN products ON products.id = support_tickets.product_id
        WHERE support_tickets.admin_id = ?
        ORDER BY support_tickets.id DESC
    `).all(session.adminId);
    sendJson(response, 200, { tickets });
}

function escapeHtml(value) {
    return String(value).replace(/[&<>"']/g, (character) => ({
        "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;"
    })[character]);
}

function handleCustomerInvoice(request, response, orderNumber) {
    if (request.method !== "GET") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }
    const account = getCustomerMobileFromSession(request, response);
    if (!account) return;
    const order = database.prepare(`
        SELECT id, order_number, customer_name, customer_mobile, shipping_address, payment_method,
               payment_status, status, total_paise, created_at
        FROM orders WHERE order_number = ? AND customer_mobile = ?
    `).get(orderNumber, account.mobile);
    if (!order) {
        sendJson(response, 404, { error: "Order not found in your account." });
        return;
    }
    const items = database.prepare(`
        SELECT product_name AS name, unit_price_paise AS unitPricePaise, quantity
        FROM order_items WHERE order_id = ? ORDER BY id
    `).all(order.id);
    const formatInvoiceMoney = (paise) =>
        `₹${(paise / 100).toLocaleString("en-IN", { minimumFractionDigits: 2, maximumFractionDigits: 2 })}`;
    const formatInvoiceLabel = (value) => String(value).replace(/_/g, " ")
        .replace(/\b[a-z]/g, (letter) => letter.toUpperCase());
    const rows = items.map((item) => `
        <tr>
            <td class="invoice-item-name">${escapeHtml(item.name)}</td>
            <td class="invoice-quantity">${escapeHtml(item.quantity)}</td>
            <td class="invoice-money">${formatInvoiceMoney(item.unitPricePaise)}</td>
            <td class="invoice-money">${formatInvoiceMoney(item.unitPricePaise * item.quantity)}</td>
        </tr>`).join("");
    const html = `<!doctype html>
<html lang="en">
<head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>ZeuKart invoice · ${escapeHtml(order.order_number)}</title>
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
    <link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&display=swap" rel="stylesheet">
    <style>
        :root {
            --zk-navy: #162b5b;
            --zk-teal: #0e6a7a;
            --zk-orange: #ffb155;
            --zk-orange-strong: #ff8f2f;
            --zk-ink: #1b2b4d;
            --zk-muted: #64748b;
            --zk-border: #e7edf5;
        }

        * { box-sizing: border-box; }

        body {
            min-height: 100vh;
            margin: 0;
            padding: 28px 16px;
            background: #f5f7fb;
            color: var(--zk-ink);
            font: 15px/1.55 Inter, Poppins, "Segoe UI", sans-serif;
            -webkit-print-color-adjust: exact;
            print-color-adjust: exact;
        }

        .invoice-shell {
            width: min(920px, 100%);
            margin: 0 auto;
            padding: 24px;
            border: 1px solid #edf1f7;
            border-radius: 28px;
            background: #fff;
            box-shadow: 0 18px 50px #162b5b12;
        }

        .invoice-hero {
            position: relative;
            display: grid;
            min-height: 250px;
            grid-template-columns: minmax(0, 1fr) 230px;
            align-items: center;
            gap: 20px;
            overflow: hidden;
            padding: 32px 38px;
            border-radius: 24px;
            background:
                radial-gradient(circle at 85% 22%, #ffb15555, transparent 26%),
                linear-gradient(120deg, var(--zk-navy), #1e3a5f 60%, var(--zk-teal));
            color: #fff;
        }

        .invoice-brand {
            display: inline-flex;
            align-items: center;
            gap: 10px;
            margin-bottom: 22px;
            color: #fff;
            font-size: 17px;
            font-weight: 800;
            letter-spacing: -.3px;
        }

        .invoice-brand svg {
            width: 30px;
            height: 30px;
            fill: none;
            stroke: var(--zk-orange);
            stroke-linecap: round;
            stroke-linejoin: round;
            stroke-width: 2;
        }

        .invoice-eyebrow {
            margin: 0 0 5px;
            color: var(--zk-orange);
            font-size: 12px;
            font-weight: 800;
            letter-spacing: 1.4px;
            text-transform: uppercase;
        }

        .invoice-hero h1 {
            margin: 0;
            font-size: clamp(32px, 5vw, 46px);
            letter-spacing: -1.5px;
            line-height: 1.08;
        }

        .invoice-hero-copy > p:last-child {
            max-width: 460px;
            margin: 12px 0 0;
            color: #dbeafe;
        }

        .invoice-hero-art {
            position: relative;
            display: grid;
            min-height: 180px;
            place-items: center;
        }

        .invoice-hero-art::before,
        .invoice-hero-art::after {
            position: absolute;
            width: 210px;
            height: 210px;
            border: 1px solid #ffffff3b;
            border-radius: 50%;
            content: "";
        }

        .invoice-hero-art::after {
            width: 154px;
            height: 154px;
        }

        .invoice-bag {
            position: relative;
            z-index: 1;
            display: grid;
            width: 112px;
            height: 112px;
            place-items: center;
            transform: rotate(-7deg);
            border-radius: 32px;
            background: linear-gradient(145deg, var(--zk-orange), var(--zk-orange-strong));
            box-shadow: 0 18px 42px #08152d55;
        }

        .invoice-bag svg {
            width: 48px;
            height: 48px;
            fill: none;
            stroke: #fff;
            stroke-linecap: round;
            stroke-linejoin: round;
            stroke-width: 2.4;
        }

        .invoice-meta {
            display: grid;
            grid-template-columns: repeat(3, minmax(0, 1fr));
            gap: 12px;
            margin: 16px 0 22px;
        }

        .invoice-meta-card {
            min-width: 0;
            padding: 15px 17px;
            border-radius: 16px;
        }

        .invoice-meta-card:nth-child(1) { background: #fff0dc; color: #8d3c1b; }
        .invoice-meta-card:nth-child(2) { background: #e5efff; color: #28488d; }
        .invoice-meta-card:nth-child(3) { background: #fce8f2; color: #922b59; }

        .invoice-meta-card span,
        .invoice-detail-label {
            display: block;
            margin-bottom: 4px;
            color: var(--zk-muted);
            font-size: 11px;
            font-weight: 700;
            letter-spacing: .45px;
            text-transform: uppercase;
        }

        .invoice-meta-card strong {
            display: block;
            overflow-wrap: anywhere;
            font-size: 14px;
        }

        .invoice-panel {
            margin-top: 18px;
            padding: 22px;
            border: 1px solid var(--zk-border);
            border-radius: 20px;
            background: #fff;
        }

        .invoice-panel h2 {
            margin: 0 0 16px;
            color: var(--zk-navy);
            font-size: 18px;
            letter-spacing: -.3px;
        }

        .invoice-customer-grid {
            display: grid;
            grid-template-columns: repeat(2, minmax(0, 1fr));
            gap: 16px 24px;
        }

        .invoice-detail-value {
            display: block;
            overflow-wrap: anywhere;
            font-weight: 600;
        }

        .invoice-address {
            grid-column: 1 / -1;
        }

        .invoice-address .invoice-detail-value {
            white-space: pre-line;
        }

        .invoice-table-wrap {
            overflow-x: auto;
            border: 1px solid var(--zk-border);
            border-radius: 16px;
        }

        .invoice-table {
            width: 100%;
            border-collapse: collapse;
            text-align: left;
        }

        .invoice-table th,
        .invoice-table td {
            padding: 13px 15px;
            border-bottom: 1px solid var(--zk-border);
        }

        .invoice-table th {
            background: #f8fafc;
            color: #51627e;
            font-size: 11px;
            font-weight: 700;
            letter-spacing: .6px;
            text-transform: uppercase;
        }

        .invoice-table tr:last-child td { border-bottom: 0; }
        .invoice-item-name { font-weight: 600; }
        .invoice-quantity { width: 70px; text-align: center; }
        .invoice-money { white-space: nowrap; }

        .invoice-summary {
            display: flex;
            align-items: center;
            justify-content: space-between;
            gap: 20px;
            margin-top: 18px;
            padding: 18px 20px;
            border-radius: 18px;
            background: #f8fafc;
        }

        .invoice-payment-label,
        .invoice-total-label {
            display: block;
            color: var(--zk-muted);
            font-size: 12px;
            font-weight: 600;
        }

        .invoice-payment strong { display: block; margin-top: 3px; }

        .invoice-payment-status {
            display: inline-block;
            margin-top: 8px;
            padding: 4px 9px;
            border-radius: 999px;
            background: #fff0dc;
            color: #8d3c1b;
            font-size: 11px;
            font-weight: 700;
        }

        .invoice-total { text-align: right; }
        .invoice-total strong {
            display: block;
            margin-top: 2px;
            color: var(--zk-navy);
            font-size: 24px;
            letter-spacing: -.5px;
        }

        .invoice-footer {
            padding: 20px 8px 4px;
            color: var(--zk-muted);
            font-size: 12px;
            text-align: center;
        }

        @media (max-width: 640px) {
            body { padding: 12px; }
            .invoice-shell { padding: 12px; border-radius: 20px; }
            .invoice-hero {
                min-height: 0;
                grid-template-columns: 1fr;
                padding: 25px 22px;
                border-radius: 18px;
            }
            .invoice-brand { margin-bottom: 18px; }
            .invoice-hero-art { display: none; }
            .invoice-meta { grid-template-columns: 1fr; gap: 8px; }
            .invoice-meta-card { padding: 12px 14px; }
            .invoice-customer-grid { grid-template-columns: 1fr; gap: 13px; }
            .invoice-address { grid-column: auto; }
            .invoice-panel { padding: 17px 14px; }
            .invoice-table th,
            .invoice-table td { padding: 11px 8px; font-size: 12px; }
            .invoice-summary { align-items: flex-start; flex-direction: column; }
            .invoice-total { width: 100%; text-align: left; }
        }

        @page { margin: 12mm; }

        @media print {
            body { min-height: 0; padding: 0; background: #fff; }
            .invoice-shell {
                width: 100%;
                margin: 0;
                padding: 0;
                border: 0;
                border-radius: 0;
                box-shadow: none;
            }
            .invoice-panel,
            .invoice-meta,
            .invoice-summary { break-inside: avoid; }
            .invoice-table-wrap { overflow: visible; }
        }
    </style>
</head>
<body>
    <main class="invoice-shell">
        <header class="invoice-hero">
            <div class="invoice-hero-copy">
                <div class="invoice-brand">
                    <svg viewBox="0 0 24 24" aria-hidden="true"><path d="M5 8h14l1 13H4L5 8Zm4 0V6a3 3 0 0 1 6 0v2"></path></svg>
                    <span>ZeuKart</span>
                </div>
                <p class="invoice-eyebrow">Your order, all in one place</p>
                <h1>Order invoice</h1>
                <p>Thank you for shopping with ZeuKart. Here are the details for your order.</p>
            </div>
            <div class="invoice-hero-art" aria-hidden="true">
                <div class="invoice-bag">
                    <svg viewBox="0 0 24 24"><path d="M5 8h14l1 13H4L5 8Zm4 0V6a3 3 0 0 1 6 0v2"></path></svg>
                </div>
            </div>
        </header>

        <section class="invoice-meta" aria-label="Order summary">
            <div class="invoice-meta-card"><span>Order ID</span><strong>${escapeHtml(order.order_number)}</strong></div>
            <div class="invoice-meta-card"><span>Order date</span><strong>${escapeHtml(order.created_at)}</strong></div>
            <div class="invoice-meta-card"><span>Order status</span><strong>${escapeHtml(formatInvoiceLabel(order.status))}</strong></div>
        </section>

        <section class="invoice-panel" aria-labelledby="invoiceCustomerHeading">
            <h2 id="invoiceCustomerHeading">Customer details</h2>
            <div class="invoice-customer-grid">
                <div><span class="invoice-detail-label">Name</span><span class="invoice-detail-value">${escapeHtml(order.customer_name)}</span></div>
                <div><span class="invoice-detail-label">Mobile</span><span class="invoice-detail-value">${escapeHtml(order.customer_mobile)}</span></div>
                <div class="invoice-address"><span class="invoice-detail-label">Delivery address</span><span class="invoice-detail-value">${escapeHtml(order.shipping_address)}</span></div>
            </div>
        </section>

        <section class="invoice-panel" aria-labelledby="invoiceItemsHeading">
            <h2 id="invoiceItemsHeading">Items</h2>
            <div class="invoice-table-wrap">
                <table class="invoice-table">
                    <thead><tr><th>Item</th><th class="invoice-quantity">Qty</th><th>Price</th><th>Amount</th></tr></thead>
                    <tbody>${rows}</tbody>
                </table>
            </div>
            <div class="invoice-summary">
                <div class="invoice-payment">
                    <span class="invoice-payment-label">Payment method</span>
                    <strong>${escapeHtml(formatInvoiceLabel(order.payment_method))}</strong>
                    <span class="invoice-payment-status">${escapeHtml(formatInvoiceLabel(order.payment_status))}</span>
                </div>
                <div class="invoice-total">
                    <span class="invoice-total-label">Order total</span>
                    <strong>${formatInvoiceMoney(order.total_paise)}</strong>
                </div>
            </div>
        </section>

        <footer class="invoice-footer">Thank you for choosing ZeuKart · Keep this invoice for your records.</footer>
    </main>
    <script>window.addEventListener("load", () => window.print());</script>
</body>
</html>`;
    response.writeHead(200, {
        "Content-Type": "text/html; charset=utf-8",
        "Content-Disposition": `attachment; filename="ZeuKart-${order.order_number}-invoice.html"`
    });
    response.end(html);
}

async function handleProductReviews(request, response, productId) {
    if (!Number.isSafeInteger(productId) || productId < 1 ||
        !database.prepare("SELECT id FROM products WHERE id = ?").get(productId)) {
        sendJson(response, 404, { error: "Product not found." });
        return;
    }

    if (request.method === "GET") {
        const summary = database.prepare(`
            SELECT AVG(rating) AS averageRating, COUNT(*) AS reviewCount
            FROM product_reviews
            WHERE product_id = ?
        `).get(productId);
        const reviews = database.prepare(`
            SELECT reviewer_name AS reviewerName, rating, comment, created_at AS createdAt
            FROM product_reviews
            WHERE product_id = ?
            ORDER BY id DESC
            LIMIT 50
        `).all(productId);
        sendJson(response, 200, {
            averageRating: summary.averageRating || 0,
            reviewCount: summary.reviewCount,
            reviews
        });
        return;
    }

    if (request.method !== "POST") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }
    const session = getAccountSession(request);
    if (!session) {
        sendJson(response, 401, { error: "Sign in to leave a product review." });
        return;
    }
    const body = await readJsonBody(request);
    const comment = typeof body.comment === "string" ? body.comment.trim() : "";
    const rating = Number(body.rating);
    const reviewerName = typeof session.displayName === "string" ? session.displayName.trim() : "";
    if (!reviewerName || reviewerName.length > 80 ||
        !Number.isSafeInteger(rating) || rating < 1 || rating > 5 ||
        comment.length < 3 || comment.length > 1000) {
        sendJson(response, 400, { error: "Enter a rating from 1 to 5 and a review of 3 to 1,000 characters." });
        return;
    }
    try {
        database.prepare(`
            INSERT INTO product_reviews (product_id, reviewer_key, reviewer_name, rating, comment)
            VALUES (?, ?, ?, ?, ?)
        `).run(productId, session.ownerKey, reviewerName, rating, comment);
    } catch (error) {
        if (error.errcode === 2067 || error.code === "ERR_SQLITE_CONSTRAINT_UNIQUE") {
            sendJson(response, 409, { error: "You have already reviewed this product." });
            return;
        }
        throw error;
    }
    sendJson(response, 201, { saved: true });
}

async function handleAdminOrders(request, response, pathname) {
    const session = getAdminSession(request);
    if (!session) {
        sendJson(response, 401, { error: "Sign in with the separate admin account to manage orders." });
        return;
    }
    if (pathname === "/api/admin/orders" && request.method === "GET") {
        const orders = database.prepare(`
            SELECT orders.*
            FROM orders
            WHERE EXISTS (
                SELECT 1 FROM order_items
                WHERE order_items.order_id = orders.id AND order_items.owner_key = ?
            )
            AND NOT EXISTS (
                SELECT 1 FROM order_items
                WHERE order_items.order_id = orders.id AND order_items.owner_key <> ?
            )
            ORDER BY orders.created_at DESC, orders.id DESC
        `).all(session.ownerKey, session.ownerKey);
        sendJson(response, 200, {
            orders: orders.map((order) => getOrderWithItems(order, session.ownerKey))
        });
        return;
    }

    const orderId = Number(pathname.slice("/api/admin/orders/".length));
    if (!Number.isSafeInteger(orderId) || orderId < 1) {
        sendJson(response, 404, { error: "Order not found." });
        return;
    }
    if (request.method !== "PATCH") {
        sendJson(response, 405, { error: "Method not allowed." });
        return;
    }

    const body = await readJsonBody(request);
    const statuses = new Set(["received", "packing", "shipped", "delivered", "cancelled"]);
    const order = database.prepare(`
        SELECT orders.*
        FROM orders
        WHERE orders.id = ?
          AND EXISTS (
              SELECT 1 FROM order_items
              WHERE order_items.order_id = orders.id AND order_items.owner_key = ?
          )
          AND NOT EXISTS (
              SELECT 1 FROM order_items
              WHERE order_items.order_id = orders.id AND order_items.owner_key <> ?
          )
    `).get(orderId, session.ownerKey, session.ownerKey);
    if (!order) {
        sendJson(response, 404, { error: "Order not found." });
        return;
    }
    const status = typeof body.status === "string" ? body.status : "";
    const paymentStatus = typeof body.paymentStatus === "string" ? body.paymentStatus : order.payment_status;
    const trackingNumber = typeof body.trackingNumber === "string" ? body.trackingNumber.trim() : "";
    const paymentStatuses = new Set(["pending", "paid"]);
    const allowedTransitions = {
        received: ["packing", "cancelled"],
        packing: ["shipped", "cancelled"],
        shipped: ["delivered"],
        delivered: [],
        cancelled: []
    };
    if (!statuses.has(status) || !paymentStatuses.has(paymentStatus) || trackingNumber.length > 100) {
        sendJson(response, 400, { error: "Choose a valid order status, payment status, and tracking number." });
        return;
    }
    if (status !== order.status && !allowedTransitions[order.status].includes(status)) {
        sendJson(response, 409, { error: `Order status cannot move from ${order.status} to ${status}.` });
        return;
    }
    if (paymentStatus === "paid" && order.payment_method !== "cash_on_delivery") {
        sendJson(response, 400, { error: "Demo online payment orders cannot be marked paid because no payment was processed." });
        return;
    }
    if (paymentStatus === "paid" && status !== "delivered") {
        sendJson(response, 400, { error: "Cash-on-delivery orders can be marked paid after delivery." });
        return;
    }

    database.exec("BEGIN IMMEDIATE");
    try {
        database.prepare(`
            UPDATE orders
            SET status = ?, payment_status = ?, tracking_number = ?, updated_at = CURRENT_TIMESTAMP
            WHERE id = ?
        `).run(status, paymentStatus, trackingNumber, orderId);
        if (status === "cancelled" && order.status !== "cancelled") {
            const items = database.prepare("SELECT product_id, quantity FROM order_items WHERE order_id = ?").all(orderId);
            const restoreStock = database.prepare(
                "UPDATE products SET stock = stock + ?, updated_at = CURRENT_TIMESTAMP WHERE id = ?"
            );
            for (const item of items) {
                restoreStock.run(item.quantity, item.product_id);
            }
        }
        database.exec("COMMIT");
    } catch (error) {
        database.exec("ROLLBACK");
        throw error;
    }
    const updatedOrder = database.prepare("SELECT * FROM orders WHERE id = ?").get(orderId);
    sendJson(response, 200, { order: getOrderWithItems(updatedOrder, session.ownerKey) });
}

const server = createServer(async (request, response) => {
    const requestUrl = new URL(request.url, `http://${request.headers.host || "localhost"}`);

    if (request.method === "GET" &&
        (requestUrl.pathname === "/health" || requestUrl.pathname === "/api/health")) {
        try {
            database.prepare("SELECT 1").get();
            sendJson(response, 200, { status: "ok" });
        } catch (error) {
            console.error("Health check failed:", error.message);
            sendJson(response, 503, { status: "unavailable" });
        }
        return;
    }

    if (request.method === "GET" && requestUrl.pathname === "/api/config") {
        loadLocalEnvironment();
        sendJson(response, 200, {
            googleClientId: process.env.GOOGLE_CLIENT_ID || "",
            googleMapsApiKey: process.env.GOOGLE_MAPS_API_KEY || ""
        });
        return;
    }

    if (requestUrl.pathname === "/api/translations") {
        try {
            await handleUiTranslations(request, response);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 502, {
                    error: error.statusCode ? error.message : "The translation service is temporarily unavailable."
                });
            }
            if (!error.statusCode) {
                console.error("UI translation failed:", error.message);
            }
        }
        return;
    }

    if (requestUrl.pathname === "/api/account/addresses" ||
        requestUrl.pathname.startsWith("/api/account/addresses/")) {
        try {
            await handleCustomerAddresses(request, response, requestUrl.pathname);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "Saved addresses could not be updated."
                });
            }
            if (!error.statusCode) console.error("Customer address request failed:", error.message);
        }
        return;
    }

    if (requestUrl.pathname === "/api/account/requests") {
        try {
            await handleCustomerOrderRequests(request, response);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "Your order request could not be saved."
                });
            }
            if (!error.statusCode) console.error("Customer order request failed:", error.message);
        }
        return;
    }

    if (requestUrl.pathname === "/api/account/support") {
        try {
            await handleCustomerSupport(request, response);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "The support request could not be saved."
                });
            }
            if (!error.statusCode) console.error("Customer support request failed:", error.message);
        }
        return;
    }

    const invoiceMatch = requestUrl.pathname.match(/^\/api\/account\/orders\/(ZK-[A-F0-9]{8})\/invoice$/);
    if (invoiceMatch) {
        try {
            handleCustomerInvoice(request, response, invoiceMatch[1]);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "The invoice could not be generated."
                });
            }
            if (!error.statusCode) console.error("Customer invoice request failed:", error.message);
        }
        return;
    }

    if (request.method === "GET" && requestUrl.pathname === "/api/products") {
        const products = database.prepare("SELECT * FROM products ORDER BY id").all();
        sendJson(response, 200, { products: products.map(formatProduct) });
        return;
    }

    const productViewMatch = requestUrl.pathname.match(/^\/api\/products\/(\d+)\/view$/);
    if (productViewMatch) {
        if (request.method !== "POST") {
            sendJson(response, 405, { error: "Method not allowed." });
            return;
        }
        const productId = Number(productViewMatch[1]);
        const update = database.prepare(
            "UPDATE products SET view_count = view_count + 1 WHERE id = ?"
        ).run(productId);
        if (update.changes === 0) {
            sendJson(response, 404, { error: "Product not found." });
            return;
        }
        const product = database.prepare("SELECT view_count FROM products WHERE id = ?").get(productId);
        sendJson(response, 200, { viewCount: product.view_count });
        return;
    }

    const productReviewsMatch = requestUrl.pathname.match(/^\/api\/products\/(\d+)\/reviews$/);
    if (productReviewsMatch) {
        await handleProductReviews(request, response, Number(productReviewsMatch[1]));
        return;
    }

    if (requestUrl.pathname.startsWith("/api/orders/")) {
        try {
            handleTrackOrder(request, response, requestUrl.pathname, requestUrl.searchParams);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "The order status could not be loaded."
                });
            }
            if (!error.statusCode) {
                console.error("Order status request failed:", error.message);
            }
        }
        return;
    }

    if (requestUrl.pathname === "/api/account/orders") {
        try {
            handleCustomerOrders(request, response);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "Your order history could not be loaded."
                });
            }
            if (!error.statusCode) {
                console.error("Customer order history request failed:", error.message);
            }
        }
        return;
    }

    if (requestUrl.pathname === "/api/orders") {
        try {
            await handleCreateOrder(request, response);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "The order could not be placed."
                });
            }
            if (!error.statusCode) {
                console.error("Order placement failed:", error.message);
            }
        }
        return;
    }

    if (requestUrl.pathname === "/api/admin/register" ||
        requestUrl.pathname === "/api/admin/login" ||
        requestUrl.pathname === "/api/admin/google") {
        try {
            if (requestUrl.pathname === "/api/admin/register") {
                await handleAdminRegistration(request, response);
            } else if (requestUrl.pathname === "/api/admin/google") {
                await handleAdminGoogleAuth(request, response);
            } else {
                await handleAdminLogin(request, response);
            }
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "Admin authentication is temporarily unavailable."
                });
            }
            if (!error.statusCode) {
                console.error("Admin authentication request failed:", error.message);
            }
        }
        return;
    }

    if (requestUrl.pathname === "/api/admin/tickets") {
        try {
            handleAdminProductTickets(request, response);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "Product support tickets could not be loaded."
                });
            }
            if (!error.statusCode) console.error("Admin product ticket request failed:", error.message);
        }
        return;
    }

    if (requestUrl.pathname === "/api/admin/products" ||
        requestUrl.pathname.startsWith("/api/admin/products/")) {
        try {
            await handleAdminProducts(request, response, requestUrl.pathname);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "Product management is temporarily unavailable."
                });
            }
            if (!error.statusCode) {
                console.error("Admin product request failed:", error.message);
            }
        }
        return;
    }

    if (requestUrl.pathname === "/api/admin/orders" ||
        requestUrl.pathname.startsWith("/api/admin/orders/")) {
        try {
            await handleAdminOrders(request, response, requestUrl.pathname);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "Order management is temporarily unavailable."
                });
            }
            if (!error.statusCode) {
                console.error("Admin order request failed:", error.message);
            }
        }
        return;
    }

    const accountPagePaths = new Set([
        "/orders", "/returns", "/addresses", "/rewards", "/payments", "/profile", "/support"
    ]);
    if (request.method === "GET" &&
        (requestUrl.pathname === "/" || requestUrl.pathname === "/project1.html" ||
            accountPagePaths.has(requestUrl.pathname))) {
        try {
            const html = await readFile(path.join(projectDirectory, "project1.html"));
            response.writeHead(200, { "Content-Type": "text/html; charset=utf-8" });
            response.end(html);
        } catch (error) {
            console.error("Unable to load the storefront page:", error.message);
            sendJson(response, 500, { error: "Unable to load the storefront page." });
        }
        return;
    }

    if (requestUrl.pathname === "/api/auth/google") {
        try {
            await handleGoogleAuth(request, response);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "Google sign-in is temporarily unavailable."
                });
            }
            if (!error.statusCode) {
                console.error("Google sign-in verification failed:", error.message);
            }
        }
        return;
    }

    if (requestUrl.pathname === "/api/auth/register" ||
        requestUrl.pathname === "/api/auth/login" ||
        requestUrl.pathname === "/api/auth/reset-password") {
        const handlers = {
            "/api/auth/register": handleRegister,
            "/api/auth/login": handleLogin,
            "/api/auth/reset-password": handlePasswordReset
        };
        try {
            await handlers[requestUrl.pathname](request, response);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "The account service is temporarily unavailable."
                });
            }
            if (!error.statusCode) {
                console.error("Account request failed:", error.message);
            }
        }
        return;
    }

    if (requestUrl.pathname === "/api/otp/send" ||
        requestUrl.pathname === "/api/auth/password-reset/send") {
        try {
            await handleApiRequest(request, response, requestUrl.pathname);
        } catch (error) {
            if (!response.headersSent) {
                sendJson(response, error.statusCode || 500, {
                    error: error.statusCode ? error.message : "The verification service is temporarily unavailable."
                });
            }
            if (!error.statusCode) {
                console.error("OTP request failed:", error.message);
            }
        }
        return;
    }

    sendJson(response, 404, { error: "Not found." });
});

initializeDatabase().then(() => {
    server.listen(port, host, () => {
        console.log(`ZeuKart is running at http://${host}:${port}`);
    });
}).catch((error) => {
    console.error("Unable to initialize the customer database:", error.message);
    process.exitCode = 1;
});
