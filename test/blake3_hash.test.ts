import { IV, LCG, blake3Compress, dec2bin, genRandomChunk } from "./utils";
import path from "path";
//@ts-ignore
import blake3compress from "./blake3_utils/compressions";
import chai from "chai";
import { Circomkit, WitnessTester } from "circomkit";

const F1Field = require("ffjavascript").F1Field;
const Scalar = require("ffjavascript").Scalar;
exports.p = Scalar.fromString(
  "21888242871839275222246405745257275088548364400416034343698204186575808495617"
);
const Fr = new F1Field(exports.p);
const assert = chai.assert;
const lcg = new LCG(6429);

describe("blake3 compression circuit, validate with blake3 js", function () {
  this.timeout(5000);

  let circuit: WitnessTester<["in"], ["out"]>;

  before(async () => {
    const circomkit = new Circomkit();
    circuit = await circomkit.WitnessTester("blake3_compression_test", {
      file: "circuits/blake3_compression",
      template: "CompressionF",
    });
  });

  it("check a blake3 regular hash with one message block (512 bits/ 64 bytes)", async () => {
    const sampleInput = genRandomChunk(lcg);

    const compressed = blake3Compress(sampleInput);

    //@ts-ignore
    await circuit.expectPass(sampleInput, { out: compressed });
  });

  it("check a random set of blake3 compression hashes", async () => {
    const N_ITS = 5;

    const randU32 = () => lcg.next();
    // const proms = Array(N_ITS)
    //   .fill(0)
    //   .map(() => {
    for (let i = 0; i < N_ITS; i++) {
      const b = (randU32() % 16) * 4;
      // Keep d = 2^0 + 2^1 for now (For block start and block end)
      const d = 3;
      const t0 = randU32();
      const t1 = randU32();

      const sampleInput = genRandomChunk(lcg, b, d, t0, t1);
      const compressed = blake3Compress(sampleInput);

      //@ts-ignore
      await circuit.expectPass(sampleInput, { out: compressed });
    }
  });
});
