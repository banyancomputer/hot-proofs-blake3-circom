/*
	Circuit for verifying a path from a leaf to the root of a (Blake3) Merkle tree. 
  Documentation for Blake3 are at https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf
*/
pragma circom 2.1.6;

include "blake3_common.circom";
include "blake3_compression.circom";
include "circomlib/circuits/comparators.circom";
include "circomlib/circuits/gates.circom";

// template Blake3Nova(
// 	D_FLAGS
// ) {
// 	var ROOT_FLAG = 8;
// 	var LAST_BLOCK_FLAG = 2;
// 	var FIRST_BLOCK_FLAG = 1;
// 	// TODO: is it allowed to just set your own flags?
// 	// It feels like for **verification** purposes this should be fine
// 	// TODO: put this in the email comments...
// 	// It is not fine though if trying to prove standardization
// 	// Public input within z_i
// 	// TODO: this is the bad boy bellow
// 	signal input n_blocks;
// 	signal input block_count;
//   signal input  h[8];         // the state (8 words)
// 	// TODO: check that n_blocks <= 16

// 	//  Auxilary (private) input within w
//   signal input  m[16];        // the message block (16 words)
// 	//  TODO: check on b? Hmrmm
//   signal input b;

// 	/**
// 	* We have to ensure that the **public** outputs are the same as public inputs
// 	*/
// 	// Public output for z_{i + 1}
// 	signal output n_blocks_out;
// 	signal output block_count_out;
// 	signal output h_out[8];

//  	component check_block_counts[2]; check_block_counts[0] = IsEqual(); check_block_counts[1] = IsEqual();
// 	check_block_counts[0].in[0] <== block_count;
// 	check_block_counts[1].in[0] <== block_count;

// 	// Check if the block is the first block
// 	check_block_counts[0].in[1] <== 0;
// 	// Check if the block is the last block
// 	check_block_counts[1].in[1] <== n_blocks - 1;

// //  TODO: root and not.. For now root if we have last block
// 	//  TODO: stuff with PARENT or not and ROOT or not
// 	// Set d flag according to the block count. 2^0 for first block, 2^1 for last block
// 	signal d <== D_FLAGS + (check_block_counts[0].out * FIRST_BLOCK_FLAG) + (check_block_counts[1].out * LAST_BLOCK_FLAG) + (check_block_counts[1].out * ROOT_FLAG);

// 	component blake3Compression = Blake3Compression();
// 	blake3Compression.h <== h;
// 	blake3Compression.m <== m;
// 	blake3Compression.d <== d;
// 	blake3Compression.b <== b;
// 	// As we always only output one chunk, the output chunk counter is always 0
// 	blake3Compression.t[0] <== 0; blake3Compression.t[1] <== 0;
	
// 	// Set Blake3 output
// 	for (var i = 0; i < 8; i++) { h_out[i] <== blake3Compression.out[i]; }
// 	block_count_out <== block_count + 1;
// 	n_blocks_out <== n_blocks;
// 	// TODO:! THIS IS NOT CORRECT> I HAVE TO FIX THIS
// }

template Blake3NovaTreePath_CheckDepth() {
	signal input depth;
	signal input total_depth;
	signal output is_root;
	signal output is_parent;

	component check_root = IsEqual(); 
	check_root.in[0] <== depth;
	check_root.in[1] <== 0;
	// Set root out
	check_root.out ==> is_root;

	component check_parent = LessThan(8); // Max depth is 64
	check_parent.in[0] <== depth;
	check_parent.in[1] <== total_depth - 1;

	// TODO: arghies... watch out for when there is some **non-uniromity in the tree**
	// Then we have to check if if we are a depth D or D+1 via a comparison to leaf position
	// If  depth < total_depth - 1, we are a parent
	check_parent.out ==> is_parent;

	// If distance from depth >= total_depth, we have something illegal
	component exceed_depth = GreaterEqThan(8);
	exceed_depth.in[0] <== depth;
	exceed_depth.in[1] <== total_depth;
	exceed_depth.out === 0;
}

template Blake3Nova(
	D_FLAGS
) {
	var FIRST_BLOCK_FLAG = 1;
	var LAST_BLOCK_FLAG = 2;
	var PARENT_FLAG = 4;
	var ROOT_FLAG = 8;
	
	// Public input
	signal input n_blocks;
	signal input block_count;
  signal input  h[8];         // the state (8 words)
	// Bound total_depth max is 64 as per Blake3 spec (max input size is 2 ^ 64)
	signal input total_depth;
	// From [0, total_depth). Depth is 0 indexed. Leaf is depth total_depth - 1, root is 0
	signal input depth;
	// TODO: check that n_blocks <= 16

	//  Auxilary (private) input within w
  signal input  m[16];        // the message block (16 words)
	//  TODO: check on b? Hmrmm
  signal input b;
	// TODO: public or private??
	// TODO: move to public
	signal input override_h_to_IV;

	/**
	* We have to ensure that the **public** outputs are the same as public inputs
	*/
	// TODO: seperate component?
	// Public output for z_{i + 1}
	signal output n_blocks_out;
	signal output block_count_out;
	signal output h_out[8];
	signal output total_depth_out;
	signal output depth_out;

	/************************* Set Flages ***********************/
	component check_depth = Blake3NovaTreePath_CheckDepth();
	check_depth.depth <== depth;
	check_depth.total_depth <== total_depth;

 	component check_block_counts[2]; check_block_counts[0] = IsEqual(); check_block_counts[1] = IsEqual();
	// Check if the block is the first block
	check_block_counts[0].in[0] <== block_count;
	check_block_counts[0].in[1] <== 0;
	// Check if the block is the last block
	check_block_counts[1].in[0] <== block_count;
	check_block_counts[1].in[1] <== n_blocks - 1;

	component not_parent = NOT(); not_parent.in <== check_depth.is_parent;
	component not_root = NOT(); not_root.in <== check_depth.is_root;

	//  TODO: flags to seperate component
	component first_block_flag_set = AND(); first_block_flag_set.a <== check_block_counts[0].out; first_block_flag_set.b <== not_parent.out;
	component last_block_flag_set = AND(); last_block_flag_set.a <== check_block_counts[1].out; last_block_flag_set.b <== not_parent.out;

	
	// We use root flag if we have a standalone chunk (without a tree path) and are on the last block
	// **OR** we are in the root of a >1 depth tree (non-trivial tree)
	component use_root_flag_tmp = OR(); use_root_flag_tmp.a <== check_depth.is_parent; use_root_flag_tmp.b <== check_block_counts[1].out;
	signal use_root_flag <== use_root_flag_tmp.out * check_depth.is_root;

	// Set d flag according to the block count. 2^0 for first block, 2^1 for last block if we are a leaf
	signal d <== D_FLAGS 
												+ FIRST_BLOCK_FLAG * (first_block_flag_set.out) // Need (not parent) && first block
												+ LAST_BLOCK_FLAG * (last_block_flag_set.out)
												+ ROOT_FLAG * use_root_flag // ROOT
												+ (check_depth.is_parent * PARENT_FLAG); // TODO: what with BAO

	/************************* Compute Compression Function Flages ***********************/
	component iv = IV();
	component blake3Compression = Blake3Compression();
	signal tmpIV[8];
	for (var i = 0; i < 8; i++) {
		tmpIV[i] <== iv.out[i] * override_h_to_IV;
		blake3Compression.h[i] <== h[i] * (1 - override_h_to_IV) + tmpIV[i];
	}
	blake3Compression.m <== m;
	blake3Compression.d <== d;
	blake3Compression.b <== b;
	// As we always only output one chunk, the output chunk counter is always 0
	blake3Compression.t[0] <== 0; blake3Compression.t[1] <== 0;
	
	// Set Blake3 output
	for (var i = 0; i < 8; i++) { h_out[i] <== blake3Compression.out[i]; }
	
	// Only update if we are not a parent
	block_count_out <== block_count + 1 * not_parent.out;
	n_blocks_out <== n_blocks;

	component check_decr_depth = OR();
	check_decr_depth.a <== check_block_counts[1].out;
	check_decr_depth.b <== check_depth.is_parent;

	signal decr_depth <== check_decr_depth.out * not_root.out; // Decr if (chunk end or is parent) and (not root)
	// Only updated depth if we have read until the final block of a chunk or
	// we are already at a parent
	depth_out <== depth - 1 * decr_depth;
	total_depth_out <== total_depth;
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

