import { LCG } from "./utils";
import path from "path";
import chai from "chai";
import { CircuitTestUtils } from "hardhat-circom";
//@ts-ignore
import { wasm as wasm_tester, c as c_tester } from "circom_tester";

const F1Field = require("ffjavascript").F1Field;
const Scalar = require("ffjavascript").Scalar;
exports.p = Scalar.fromString(
  "21888242871839275222246405745257275088548364400416034343698204186575808495617"
);
const Fr = new F1Field(exports.p);
const assert = chai.assert;

const initVector = [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c,
  0x1f83d9ab, 0x5be0cd19,
];

const genRandomChunk = (
  lcg: LCG,
  b = 1,
  d = 0,
  t0 = 0,
  t1 = 0,
  h = initVector
) => {
  // Generate a pseudo-random 32-bit number
  const randomNumber = lcg.next();
  console.log(randomNumber);
  return {
    h,
    m: Array(16)
      .fill(0)
      .map((_, i) => lcg.next()),
    b,
    d,
    t: [t0, t1],
  };
};

describe("blake3 compression circuit, validate with blake3 js", () => {
  let circuit: CircuitTestUtils;
  const sanityCheck = true;

  before(async () => {
    circuit = await wasm_tester(
      path.join(__dirname, "test_circuits/blake3_compression_test.circom")
    );
  });

  it("check a blake3 regular hash with one message block (512 bits/ 64 bytes)", async () => {
    const lcg = new LCG(6429);
    const sampleInput = genRandomChunk(lcg);
    
    const witness = await circuit.calculateWitness(sampleInput, sanityCheck);
    await circuit.checkConstraints(witness);
    console.log(witness);
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