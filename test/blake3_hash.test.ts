import { LCG, dec2bin, genRandomChunk } from "./utils";
import path from "path";
//@ts-ignore
import blake3compress from "./blake3_utils/compressions";
import chai from "chai";
import { Circomkit, WitnessTester } from "circomkit";

//@ts-ignore
import { wasm as wasm_tester, c as c_tester } from "circom_tester";

const F1Field = require("ffjavascript").F1Field;
const Scalar = require("ffjavascript").Scalar;
exports.p = Scalar.fromString(
  "21888242871839275222246405745257275088548364400416034343698204186575808495617"
);
const Fr = new F1Field(exports.p);
const assert = chai.assert;

describe("blake3 compression circuit, validate with blake3 js", function () {
  this.timeout(5000);

  let circuit: WitnessTester<["in"], ["out"]>;

  const sanityCheck = true;

  before(async () => {
    const circomkit = new Circomkit();
    circuit = await circomkit.WitnessTester("blake3_compression_test", {
      file: "circuits/blake3_compression",
      template: "CompressionF",
    });

    // circuit = await wasm_tester(
    //   path.join(__dirname, "test_circuits/blake3_compression_test.circom")
    // );
  });

  it("check a blake3 regular hash with one message block (512 bits/ 64 bytes)", async () => {
    const lcg = new LCG(6429);
    const sampleInput = genRandomChunk(lcg);

    // TODO: wrap in utils
    const compressed = blake3compress(
      sampleInput.h.map(dec2bin),
      sampleInput.m.map(dec2bin),
      dec2bin((sampleInput.t[1] << 32) + sampleInput.t[0]),
      dec2bin(sampleInput.b),
      dec2bin(sampleInput.d)
    ).map((x) => parseInt(x, 2));

    console.log(compressed)
    //@ts-ignore
    await circuit.expectPass(sampleInput, {out: compressed});
  });

  xit("has expected witness values", async () => {
    // const witness = await circuit.calculateLabeledWitness(
    //   sampleInput,:q
    //   sanityCheck
    // );
    // assert.propertyVal(witness, "main.x1", sampleInput.x1);
    // assert.propertyVal(witness, "main.x2", sampleInput.x2);
    // assert.propertyVal(witness, "main.x3", sampleInput.x3);
    // assert.propertyVal(witness, "main.x4", sampleInput.x4);
    // assert.propertyVal(witness, "main.y1", undefined);
    // assert.propertyVal(witness, "main.y2", undefined);
    // assert.propertyVal(witness, "main.out", "3");
  });

  xit("has the correct output", async () => {
    // const expected = { out: 3 };
    // const witness = await circuit.calculateWitness(sampleInput, sanityCheck);
    // await circuit.assertOut(witness, expected);
  });
});

// TODO:
// Weir
