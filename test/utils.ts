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
