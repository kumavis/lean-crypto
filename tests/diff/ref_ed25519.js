#!/usr/bin/env node
// Reference Ed25519 implementation driver.
//
// Reads one command per line from stdin and writes one response per line
// to stdout, mirroring `Tests.DiffCli`. Uses Node 22's built-in Ed25519
// via the `crypto` module (RFC 8032 strict mode — no ZIP-215 variant).
//
// Commands:
//   ed25519-pubkey <sk-hex>                       → 32-byte pk hex
//   ed25519-sign <sk-hex> <msg-hex>               → 64-byte sig hex
//   ed25519-verify <pk-hex> <sig-hex> <msg-hex>   → "true" or "false"

const crypto = require('node:crypto');
const readline = require('node:readline');

const PKCS8_PREFIX = Buffer.from('302e020100300506032b657004220420', 'hex'); // 16 bytes
const SPKI_PREFIX  = Buffer.from('302a300506032b6570032100', 'hex');         // 12 bytes

function privKeyFromSeed(skHex) {
  const seed = Buffer.from(skHex, 'hex');
  if (seed.length !== 32) throw new Error(`bad sk length ${seed.length}`);
  const pkcs8 = Buffer.concat([PKCS8_PREFIX, seed]);
  return crypto.createPrivateKey({ key: pkcs8, format: 'der', type: 'pkcs8' });
}

function pubKeyFromRaw(pkHex) {
  const raw = Buffer.from(pkHex, 'hex');
  if (raw.length !== 32) throw new Error(`bad pk length ${raw.length}`);
  const spki = Buffer.concat([SPKI_PREFIX, raw]);
  return crypto.createPublicKey({ key: spki, format: 'der', type: 'spki' });
}

function derivePubkeyRaw(skHex) {
  const priv = privKeyFromSeed(skHex);
  const pub = crypto.createPublicKey(priv);
  const spkiDer = pub.export({ type: 'spki', format: 'der' });
  return spkiDer.slice(12).toString('hex'); // strip SPKI prefix
}

function sign(skHex, msgHex) {
  const priv = privKeyFromSeed(skHex);
  const msg = Buffer.from(msgHex, 'hex');
  return crypto.sign(null, msg, priv).toString('hex');
}

function verify(pkHex, sigHex, msgHex) {
  const pub = pubKeyFromRaw(pkHex);
  const msg = Buffer.from(msgHex, 'hex');
  const sig = Buffer.from(sigHex, 'hex');
  try {
    return crypto.verify(null, msg, pub, sig) ? 'true' : 'false';
  } catch {
    return 'false';
  }
}

function respond(line) {
  const parts = line.split(' ');
  try {
    switch (parts[0]) {
      case 'ed25519-pubkey': return derivePubkeyRaw(parts[1]);
      case 'ed25519-sign':   return sign(parts[1], parts[2]);
      case 'ed25519-verify': return verify(parts[1], parts[2], parts[3]);
      default: return `ERR unknown-cmd: ${line}`;
    }
  } catch (e) {
    return `ERR ${e.message}`;
  }
}

const rl = readline.createInterface({ input: process.stdin, terminal: false });
rl.on('line', (line) => {
  if (line.length === 0) return;
  process.stdout.write(respond(line) + '\n');
});
