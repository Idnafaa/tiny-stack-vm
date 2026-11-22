// Tiny st-machine interpreter for make.fun's st ISA v1.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const IDIR = process.env.MAKEFUN_INPUT_DIR ?? '/inp', ODIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DC = 256, CC = 64, MW = 256;
const SC = 1_000_000, OC = 65_536, IMN = -2147483648;
// [opcode, immediate bytes, popped, pushed] per instruction.
const OPS: [number, number, number, number][] = [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0],
  [0x04, 0, 1, 2], [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1],
  [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1],
  [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1],
  [0x21, 0, 2, 1], [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0],
  [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0], [0x40, 0, 1, 1],
  [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1],
  [0x53, 0, 1, 0],
];
const IMM = new Int8Array(256).fill(-1);
const POPS = new Int8Array(256);
const PUSHES = new Int8Array(256);
for (const [c, i, p, q] of OPS) { IMM[c] = i; POPS[c] = p; PUSHES[c] = q; }
function run(prog: Uint8Array, inp: Uint8Array) {
  const st = new Int32Array(DC), cs = new Int32Array(CC);
  const mem = new Int32Array(MW), sink = new Uint8Array(OC);
  let sp = 0, dp = 0, wr = 0, read = 0, pc = 0, stp = 0;
  const size = prog.length;
  const fin = (code: number) => ({ bytes: sink.slice(0, wr), code });
  for (;;) {
    if (stp >= SC) return fin(10);
    if (pc < 0 || pc >= size) return fin(9);
    const op = prog[pc];
    const il = IMM[op];
    if (il < 0) return fin(5);
    if (pc + il >= size) return fin(9);
    stp++;
    const after = pc + 1 + il;
    const pops = POPS[op];
    if (sp < pops) return fin(2);
    if (sp - pops + PUSHES[op] > DC) return fin(3);
    pc = after;
    switch (op) {
      case 0x00: return fin(0);
      case 0x01: st[sp++] = (prog[after - 1] << 24) >> 24; break;
      case 0x02:
        st[sp++] = prog[after - 4] | (prog[after - 3] << 8) |
          (prog[after - 2] << 16) | (prog[after - 1] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: st[sp] = st[sp - 1]; sp++; break;
      case 0x05: {
        const hold = st[sp - 1];
        st[sp - 1] = st[sp - 2]; st[sp - 2] = hold;
        break;
      }
      case 0x06: st[sp] = st[sp - 2]; sp++; break;
      case 0x07: {
        const bottom = st[sp - 3];
        st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = bottom;
        break;
      }
      case 0x17: st[sp - 1] = -st[sp - 1] | 0; break;
      case 0x1b: st[sp - 1] = ~st[sp - 1]; break;
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[after - 2] | (prog[after - 1] << 8)) << 16) >> 16;
        let go = op === 0x30;
        if (!go) { const v = st[--sp]; go = op === 0x31 ? v === 0 : v !== 0; }
        if (go) pc = after + rel;
        break;
      }
      case 0x33:
        if (dp >= CC) return fin(7);
        cs[dp++] = after;
        pc = prog[after - 2] | (prog[after - 1] << 8);
        break;
      case 0x34:
        if (dp === 0) return fin(8);
        pc = cs[--dp];
        break;
      case 0x40: {
        const addr = st[sp - 1];
        if (addr < 0 || addr >= MW) return fin(6);
        st[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = st[sp - 1];
        if (addr < 0 || addr >= MW) return fin(6);
        mem[addr] = st[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: {
        const text = String(st[sp - 1]);
        if (wr + text.length > OC) return fin(11);
        sp--;
        for (let i = 0; i < text.length; i++) sink[wr++] = text.charCodeAt(i);
        break;
      }
      case 0x51:
        if (wr + 1 > OC) return fin(11);
        sink[wr++] = st[--sp] & 255;
        break;
      case 0x52: st[sp++] = read < inp.length ? inp[read++] : -1; break;
      case 0x53: return fin(st[--sp] & 255);
      default: {
        const b = st[sp - 1], a = st[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return fin(4);
            r = a === IMN && b === -1 ? IMN : Math.trunc(a / b) | 0;
            break;
          case 0x14:
            if (b === 0) return fin(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15:
            if (b === 0) return fin(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16:
            if (b === 0) return fin(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2;
        st[sp++] = r;
        break;
      }
    }
  }
}
for (const id of readdirSync(IDIR).sort()) {
  const prog2 = readFileSync(join(IDIR, id, 'program.bin'));
  const inp = readFileSync(join(IDIR, id, 'input.bin'));
  const res = run(prog2, inp);
  mkdirSync(join(ODIR, id), { recursive: true });
  writeFileSync(join(ODIR, id, 'stdout.bin'), res.bytes);
  writeFileSync(join(ODIR, id, 'exit.txt'), `${res.code}\n`);
}
