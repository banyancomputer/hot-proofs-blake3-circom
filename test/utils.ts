import blake3compress from "./blake3_utils/compressions";

export class LCG {
  seed: number;
  a: number;
  c: number;
  m: number;

  constructor(seed: number) {
    this.seed = seed;
    this.a = 1664525;
    this.c = 1013904223;
    this.m = Math.pow(2, 32);
  }

  next() {
    this.seed = (this.a * this.seed + this.c) % this.m;
    return this.seed;
  }
}

export function dec2bin(dec: number) {
  return ("0".repeat(32) + (dec >>> 0).toString(2)).slice(-32);
}

export const IV = [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c,
  0x1f83d9ab, 0x5be0cd19,
];

type Chunk = ReturnType<typeof genRandomChunk>;

export const genRandomChunk = (
  lcg: LCG,
  b = 1,
  d = 0,
  t0 = 0,
  t1 = 0,
  h = IV
) => {
  // Generate a pseudo-random 32-bit number
  const randomNumber = lcg.next();
  console.log(randomNumber);
  return {
    h,
    m: Array(16).fill(0), // .map((_, i) => lcg.next()),
    b,
    d,
    t: [t0, t1],
  };
};

export const blake3Compress = (chunk: Chunk) => {
  const tConcat = dec2bin(chunk.t[1]) + dec2bin(chunk.t[0]);
  console.log(tConcat, tConcat.length);
  // TODO: wrap in utils
  const compressed = blake3compress(
    chunk.h.map(dec2bin),
    chunk.m.map(dec2bin),
    tConcat,
    dec2bin(chunk.b),
    dec2bin(chunk.d)
  ).map((x) => parseInt(x, 2));
  return compressed;
};
