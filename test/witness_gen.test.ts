import { IV, LCG, blake3Compress, dec2bin, genRandomChunk } from "./utils";
//@ts-ignore
import chai from "chai";
import { Circomkit, WitnessTester } from "circomkit";
import { writeFileSync } from "fs";

function execShellCommand(cmd: string) {
  const exec = require("child_process").exec;
  return new Promise((resolve, reject) => {
    exec(cmd, (error: any, stdout: any, stderr: any) => {
      if (error) {
        console.warn(error);
      }
      resolve(stdout ? stdout : stderr);
    });
  });
}

const F1Field = require("ffjavascript").F1Field;
const Scalar = require("ffjavascript").Scalar;
exports.p = Scalar.fromString(
  "21888242871839275222246405745257275088548364400416034343698204186575808495617"
);
const Fr = new F1Field(exports.p);
const assert = chai.assert;
const lcg = new LCG(6429);

describe("blake3 compression circuit, validate with blake3 js", function () {
  this.timeout(10000);

  before(async () => {});

  it("Use CLI to generate a witness for a blake3 compression function", async () => {
    const circuitName = "blake3_compression";
    const inputName = `testInp`;
    const inp = genRandomChunk(lcg);
    writeFileSync(
      `inputs/blake3_compression/${inputName}.json`,
      JSON.stringify(inp)
    );
    const cmd = `npx circomkit witness ${circuitName} ${inputName}`;
		console.log("Running command: ", cmd);
		let start = Date.now()
    await execShellCommand(cmd);
		console.log("Witness generation takes ", Date.now() - start, "ms");

		const proveCmd = `npx circomkit prove ${circuitName} ${inputName}`;
		start = Date.now()
		await execShellCommand(proveCmd);
		console.log("Proving takes: ", Date.now() - start, "ms");
  });
});
