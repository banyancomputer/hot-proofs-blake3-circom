import "hardhat-circom";

/**
 * @type import('hardhat/config').HardhatUserConfig
 */
module.exports = {
  solidity: {
    compilers: [
      {
        version: "0.6.11",
      },
      {
        version: "0.8.9",
      },
    ],
  },
  // circom: {
  //   inputBasePath: "./circuits",
  //   ptau: "https://hermez.s3-eu-west-1.amazonaws.com/powersOfTau28_hez_final_15.ptau",
  //   circuits: [
  //     {
  //       name: "blake3_compression_test",
  //       circuit: "test_circuits/blake3_compression_test.circom",
  //       // protocol: "plonk",
  //       // No protocol, so it defaults to groth16
  //     },
  //   ],
  // },
};
