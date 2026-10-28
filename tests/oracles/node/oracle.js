// The Node oracle: path.posix.normalize and path.posix.join.
//
// It reads requests on standard input, one per line, as `path serve`
// does (see the header of Main.lean):
//
//   clean HEX      prints  OK and the hex of path.posix.normalize
//   join HEX...    prints  OK and the hex of path.posix.join
//
// A path is the hex of its UTF-8 octets, and the empty path is `-`.
// Anything else prints `n/a`.
'use strict';
const path = require('path');

function field(f) {
  if (f === '-') return '';
  if (f === '' || f.length % 2 !== 0 || !/^[0-9a-f]*$/.test(f)) return null;
  const b = Buffer.from(f, 'hex');
  const s = b.toString('utf8');
  // Only valid UTF-8 is asked; refuse anything that does not round-trip.
  if (!Buffer.from(s, 'utf8').equals(b)) return null;
  return s;
}

function out(s) {
  return s === '' ? '-' : Buffer.from(s, 'utf8').toString('hex');
}

function answer(line) {
  const fs = line.split(' ');
  if (fs[0] === 'clean' && fs.length === 2) {
    const p = field(fs[1]);
    return p === null ? 'n/a' : 'OK ' + out(path.posix.normalize(p));
  }
  if (fs[0] === 'join') {
    const es = fs.slice(1).map(field);
    if (es.some((e) => e === null)) return 'n/a';
    return 'OK ' + out(path.posix.join(...es));
  }
  return 'n/a';
}

let buf = '';
const outBuf = [];
process.stdin.setEncoding('latin1');
process.stdin.on('data', (chunk) => {
  buf += chunk;
  let i;
  while ((i = buf.indexOf('\n')) >= 0) {
    let line = buf.slice(0, i);
    buf = buf.slice(i + 1);
    if (line.endsWith('\r')) line = line.slice(0, -1);
    outBuf.push(answer(line));
    if (outBuf.length >= 4096) {
      process.stdout.write(outBuf.join('\n') + '\n');
      outBuf.length = 0;
    }
  }
});
process.stdin.on('end', () => {
  if (buf.length > 0) {
    let line = buf;
    if (line.endsWith('\r')) line = line.slice(0, -1);
    outBuf.push(answer(line));
  }
  if (outBuf.length > 0) process.stdout.write(outBuf.join('\n') + '\n');
});
