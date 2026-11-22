// A small interpreter for make.fun's tiny stack ISA, version 1.
// For each program in /input/<id>/ it runs the bytecode on its input bytes
// and writes /output/<id>/stdout.bin plus /output/<id>/exit.txt.
// Node 22, standard library only, no network, no clock, fully deterministic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const OUT_CAP = 65536;
const STEP_CAP = 1000000;

// Per opcode: [bytes of immediate, values popped, values pushed].
const META: { [op: number]: [number, number, number] } = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x10: [0, 2, 1], 0x11: [0, 2, 1], 0x12: [0, 2, 1], 0x13: [0, 2, 1],
  0x14: [0, 2, 1], 0x15: [0, 2, 1], 0x16: [0, 2, 1], 0x17: [0, 1, 1],
  0x18: [0, 2, 1], 0x19: [0, 2, 1], 0x1a: [0, 2, 1], 0x1b: [0, 1, 1],
  0x1c: [0, 2, 1], 0x1d: [0, 2, 1], 0x1e: [0, 2, 1],
  0x20: [0, 2, 1], 0x21: [0, 2, 1], 0x22: [0, 2, 1],
  0x30: [2, 0, 0], 0x31: [2, 1, 0], 0x32: [2, 1, 0], 0x33: [2, 0, 0],
  0x34: [0, 0, 0], 0x40: [0, 1, 1], 0x41: [0, 2, 0],
  0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1], 0x53: [0, 1, 0],
};

// Run one program to its end. Returns [bytes written, exit code].
// A trap ends the run at once; its code is the exit code and the bytes
// written before it are kept.
function runProgram(prog: Uint8Array, input: Uint8Array): [number[], number] {
  const stack = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const out: number[] = [];
  let sp = 0;
  let cp = 0;
  let pc = 0;
  let ip = 0;
  for (let step = 0; ; step++) {
    if (step === STEP_CAP) return [out, 10];
    if (pc < 0 || pc >= prog.length) return [out, 9];
    const op = prog[pc];
    const meta = META[op];
    if (meta === undefined) return [out, 5];
    const imm = meta[0];
    if (pc + imm >= prog.length) return [out, 9];
    const next = pc + 1 + imm;
    if (sp < meta[1]) return [out, 2];
    if (sp - meta[1] + meta[2] > 256) return [out, 3];
    pc = next;
    switch (op) {
      case 0x00:
        return [out, 0];
      case 0x01:
        stack[sp++] = (prog[pc - 1] << 24) >> 24;
        break;
      case 0x02:
        stack[sp++] = prog[pc - 4] | (prog[pc - 3] << 8) | (prog[pc - 2] << 16) | (prog[pc - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        stack[sp] = stack[sp - 1];
        sp++;
        break;
      case 0x05: {
        const top = stack[sp - 1];
        stack[sp - 1] = stack[sp - 2];
        stack[sp - 2] = top;
        break;
      }
      case 0x06:
        stack[sp] = stack[sp - 2];
        sp++;
        break;
      case 0x07: {
        const bottom = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2];
        stack[sp - 2] = stack[sp - 1];
        stack[sp - 1] = bottom;
        break;
      }
      case 0x17:
        stack[sp - 1] = (-stack[sp - 1]) | 0;
        break;
      case 0x1b:
        stack[sp - 1] = ~stack[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x18: case 0x19: case 0x1a:
      case 0x1c: case 0x1d: case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = stack[sp - 1];
        const a = stack[sp - 2];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        stack[sp - 2] = r;
        sp--;
        break;
      }
      case 0x13: case 0x14: case 0x15: case 0x16: {
        const b = stack[sp - 1];
        const a = stack[sp - 2];
        if (b === 0) return [out, 4];
        let r = 0;
        if (op === 0x13) r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
        else if (op === 0x14) r = b === -1 ? 0 : (a % b) | 0;
        else if (op === 0x15) r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        else r = ((a >>> 0) % (b >>> 0)) | 0;
        stack[sp - 2] = r;
        sp--;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[pc - 2] | (prog[pc - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (op !== 0x30) {
          const v = stack[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (cp === 64) return [out, 7];
        calls[cp++] = pc;
        pc = prog[pc - 2] | (prog[pc - 1] << 8);
        break;
      case 0x34:
        if (cp === 0) return [out, 8];
        pc = calls[--cp];
        break;
      case 0x40: {
        const addr = stack[sp - 1];
        if (addr < 0 || addr > 255) return [out, 6];
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = stack[sp - 1];
        const v = stack[sp - 2];
        if (addr < 0 || addr > 255) return [out, 6];
        mem[addr] = v;
        sp -= 2;
        break;
      }
      case 0x50: {
        const text = String(stack[sp - 1]);
        if (out.length + text.length > OUT_CAP) return [out, 11];
        sp--;
        for (let i = 0; i < text.length; i++) out.push(text.charCodeAt(i));
        break;
      }
      case 0x51:
        if (out.length + 1 > OUT_CAP) return [out, 11];
        out.push(stack[--sp] & 255);
        break;
      case 0x52:
        stack[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 0x53:
        return [out, stack[--sp] & 255];
    }
  }
}

// Answer every instance of the set in one run.
const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN_DIR).sort()) {
  const [bytes, code] = runProgram(
    readFileSync(join(IN_DIR, id, 'program.bin')),
    readFileSync(join(IN_DIR, id, 'input.bin')),
  );
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), Uint8Array.from(bytes));
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), code + '\n');
}
