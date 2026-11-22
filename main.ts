// interpreter for the tiny stack bytecode (wrapping i32, traps 2-11)
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const IN = process.env.MAKEFUN_INPUT_DIR || '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR || '/output';
// per opcode: [immediate bytes, pops, pushes]
const T: Record<number, [number, number, number]> = {
  0: [0, 0, 0], 1: [1, 0, 1], 2: [4, 0, 1], 3: [0, 1, 0], 4: [0, 1, 2], 5: [0, 2, 2], 6: [0, 2, 3], 7: [0, 3, 3],
  16: [0, 2, 1], 17: [0, 2, 1], 18: [0, 2, 1], 19: [0, 2, 1], 20: [0, 2, 1], 21: [0, 2, 1], 22: [0, 2, 1],
  23: [0, 1, 1], 24: [0, 2, 1], 25: [0, 2, 1], 26: [0, 2, 1], 27: [0, 1, 1], 28: [0, 2, 1], 29: [0, 2, 1],
  30: [0, 2, 1], 32: [0, 2, 1], 33: [0, 2, 1], 34: [0, 2, 1], 48: [2, 0, 0], 49: [2, 1, 0], 50: [2, 1, 0],
  51: [2, 0, 0], 52: [0, 0, 0], 64: [0, 1, 1], 65: [0, 2, 0], 80: [0, 1, 0], 81: [0, 1, 0], 82: [0, 0, 1],
  83: [0, 1, 0],
};
function run(code: Uint8Array, feed: Uint8Array) {
  const vs = new Int32Array(256), rs = new Int32Array(64), mm = new Int32Array(256), ob = new Uint8Array(65536);
  let h = 0, d = 0, w = 0, c = 0, pc = 0, n = 0;
  const len = code.length;
  const end = (s: number) => ({ out: ob.slice(0, w), s });
  for (;;) {
    if (n >= 1000000) return end(10);
    if (pc < 0 || pc >= len) return end(9);
    const op = code[pc], m = T[op];
    if (m === undefined) return end(5);
    if (pc + m[0] >= len) return end(9);
    n++;
    const nx = pc + 1 + m[0];
    if (h < m[1]) return end(2);
    if (h - m[1] + m[2] > 256) return end(3);
    pc = nx;
    if (op === 0) return end(0);
    else if (op === 1) vs[h++] = (code[nx - 1] << 24) >> 24;
    else if (op === 2) vs[h++] = code[nx - 4] | (code[nx - 3] << 8) | (code[nx - 2] << 16) | (code[nx - 1] << 24);
    else if (op === 3) h--;
    else if (op === 4) { vs[h] = vs[h - 1]; h++; }
    else if (op === 5) { const t = vs[h - 1]; vs[h - 1] = vs[h - 2]; vs[h - 2] = t; }
    else if (op === 6) { vs[h] = vs[h - 2]; h++; }
    else if (op === 7) { const t = vs[h - 3]; vs[h - 3] = vs[h - 2]; vs[h - 2] = vs[h - 1]; vs[h - 1] = t; }
    else if (op === 23) vs[h - 1] = (-vs[h - 1]) | 0;
    else if (op === 27) vs[h - 1] = ~vs[h - 1];
    else if (op >= 48 && op <= 50) {
      const rel = ((code[nx - 2] | (code[nx - 1] << 8)) << 16) >> 16;
      let go = op === 48;
      if (!go) { const v = vs[--h]; go = op === 49 ? v === 0 : v !== 0; }
      if (go) pc = nx + rel;
    } else if (op === 51) {
      if (d >= 64) return end(7);
      rs[d++] = nx;
      pc = code[nx - 2] | (code[nx - 1] << 8);
    } else if (op === 52) {
      if (d === 0) return end(8);
      pc = rs[--d];
    } else if (op === 64) {
      const a = vs[h - 1];
      if (a < 0 || a >= 256) return end(6);
      vs[h - 1] = mm[a];
    } else if (op === 65) {
      const a = vs[h - 1];
      if (a < 0 || a >= 256) return end(6);
      mm[a] = vs[h - 2];
      h -= 2;
    } else if (op === 80) {
      const s = String(vs[h - 1]);
      if (w + s.length > 65536) return end(11);
      h--;
      for (let i = 0; i < s.length; i++) ob[w++] = s.charCodeAt(i);
    } else if (op === 81) {
      if (w + 1 > 65536) return end(11);
      ob[w++] = vs[--h] & 255;
    } else if (op === 82) vs[h++] = c < feed.length ? feed[c++] : -1;
    else if (op === 83) return end(vs[--h] & 255);
    else {
      const b = vs[h - 1], a = vs[h - 2];
      let r: number;
      if (op === 16) r = (a + b) | 0;
      else if (op === 17) r = (a - b) | 0;
      else if (op === 18) r = Math.imul(a, b);
      else if (op === 19) { if (b === 0) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
      else if (op === 20) { if (b === 0) return end(4); r = b === -1 ? 0 : (a % b) | 0; }
      else if (op === 21) { if (b === 0) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 22) { if (b === 0) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (op === 24) r = a & b;
      else if (op === 25) r = a | b;
      else if (op === 26) r = a ^ b;
      else if (op === 28) r = a << (b & 31);
      else if (op === 29) r = a >> (b & 31);
      else if (op === 30) r = (a >>> (b & 31)) | 0;
      else if (op === 32) r = a === b ? 1 : 0;
      else if (op === 33) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      h -= 2;
      vs[h++] = r;
    }
  }
}
for (const id of readdirSync(IN).sort()) {
  const res = run(readFileSync(join(IN, id, 'program.bin')), readFileSync(join(IN, id, 'input.bin')));
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'stdout.bin'), res.out);
  writeFileSync(join(OUT, id, 'exit.txt'), res.s + '\n');
}
