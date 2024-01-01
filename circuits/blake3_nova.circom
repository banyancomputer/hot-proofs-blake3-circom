/*
	Circuit for verifying a path from a leaf to the root of a (Blake3) Merkle tree. 
  Documentation for Blake3 are at https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf
*/
pragma circom 2.1.6;

include "blake3_common.circom";
include "blake3_compression.circom";
include "circomlib/circuits/comparators.circom";

template Blake3Nova(
	D_FLAGS
) {
	// TODO: is it allowed to just set your own flags?
	// It feels like for **verification** purposes this should be fine
	// TODO: put this in the email comments...
	// It is not fine though if trying to prove standardization
	// Public input within z_i
	// TODO: this is the bad boy bellow
	signal input additional_flags;
	signal input n_blocks;
	signal input block_count;
  signal input  h[8];         // the state (8 words)
	// TODO: check that n_blocks <= 16

	//  Auxilary (private) input within w
  signal input  m[16];        // the message block (16 words)
	//  TODO: check on b? Hmrmm
  signal input b;

	/**
	* We have to ensure that the **public** outputs are the same as public inputs
	*/
	// Public output for z_{i + 1}
	signal output additional_flags_out;
	signal output n_blocks_out;
	signal output block_count_out;
	signal output h_out[8];

 	component check_block_counts[2]; check_block_counts[0] = IsEqual(); check_block_counts[1] = IsEqual();
	check_block_counts[0].in[0] <== block_count;
	check_block_counts[1].in[0] <== block_count;

	// Check if the block is the first block
	check_block_counts[0].in[1] <== 0;
	// Check if the block is the last block
	check_block_counts[1].in[1] <== n_blocks - 1;

	//  TODO: stuff with PARENT or not and ROOT or not
	// Set d flag according to the block count. 2^0 for first block, 2^1 for last block
	signal d <== D_FLAGS + (check_block_counts[0].out * 1) + (check_block_counts[1].out * 2) + additional_flags;

	component blake3Compression = Blake3Compression();
	blake3Compression.h <== h;
	blake3Compression.m <== m;
	blake3Compression.d <== d;
	blake3Compression.b <== b;
	// As we always only output one chunk, the output chunk counter is always 0
	blake3Compression.t[0] <== 0; blake3Compression.t[1] <== 0;
	
	// Set Blake3 output
	for (var i = 0; i < 8; i++) { h_out[i] <== blake3Compression.out[i]; }
	block_count_out <== block_count + 1;
	n_blocks_out <== n_blocks;
	// TODO:! THIS IS NOT CORRECT> I HAVE TO FIX THIS
	additional_flags_out <== additional_flags;
}

	

// template BlockToChunkHash(
// ) {
// 	var MAX_BLOCKS_PER_CHUNK = 16;
// 	var N_DATA_32_BIT_WORDS = 16 * MAX_BLOCKS_PER_CHUNK;

// 	input signal block_data[MAX_BLOCKS_PER_CHUNK];
// 	input signal ms[N_DATA_32_BIT_WORDS];
// 	input signal n_blocks;

// 	// Check that 0 <= n_blocks <= MAX_BLOCKS_PER_CHUNK
	

// 	component blake3Compressions[MAX_BLOCKS_PER_CHUNK];
// 	signal past_n_blocks[MAX_BLOCKS_PER_CHUNK];

// 	for (var i = 0; i < MAX_BLOCKS_PER_CHUNK; i++) {
// 		// TODO: hrmmm
// 		past_n_blocks[i] <== (n_blocks - i);
// 		blake3Compressions[i] = Blake3Compression();

// 		// We are only producing one chunk and thus t (the output counter) is fixed to 0
// 		blake3Compressions[i].t[0] <== 0;
// 		blake3Compressions[i].t[1] <== 0;

// 		blake3Compressions[i].hash <== ms[i];
// 		for (var x = 0; x < 16; x++) {
// 			// Take the 32 words here
// 			blake3Compressions[i].m[x] <== ms[16 * i + x];
// 		}
	
// 	}
// }

// template ChunkTreePath(
// 	N_LEVELS
// ) {
// 	input signal leaf_hash;
// 	input signal[N_LEVELS - 1] siblings;
// 	input signal root;
// 	input signal paths[N_LEVELS - 1];

// 	//  Input constraints
// 	for (var i = 0; i < N_LEVELS - 1; i++) {
// 		// Assert that the path is a valid bit string
// 		paths[i] * (paths[i] - 1) === 0;
// 	}

// 	Blake3Compression(N_LEVELS - 1);
// 	signal[N_LEVELS - 1] hashes;
// 	component blake3Compressions[N_LEVELS - 1];
// 	for (var i = 0; i < N_LEVELS - 1; i++) {
// 		blake3Compressions[i] = Blake3Compression();
// 		blake3Compressions[i].leaf_hash <== leaf_hash;
// 		blake3Compressions[i].siblings <== siblings[i];
// 		blake3Compressions[i].hash <== hashes[i];
// 		blake3Compressions[i].path <== paths[i];
// 	}
// }

