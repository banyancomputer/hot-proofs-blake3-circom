/*
	Circuit for verifying a path from a leaf to the root of a (Blake3) Merkle tree. 
  Documentation for Blake3 are at https://github.com/BLAKE3-team/BLAKE3-specs/blob/master/blake3.pdf
*/
pragma circom 2.1.6;

include "blake3_common.circom";
include "blake3_compression.circom";
include "circomlib/circuits/comparators.circom";
include "circomlib/circuits/gates.circom";
include "circomlib/circuits/bitify.circom";

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

template Blake3GetDownLeftPath() {
	var GO_LEFT = 1;

	signal input depth;
	signal input leaf_idx;
	signal input is_parent;

	signal output out;

	component n2b = Num2Bits(65); // Max depth is 64 and so leaf max is 2^64. Pad with 1 for 65
	n2b.in <== leaf_idx;

	// If we are a leaf, we are always on the left path, but it does not really matter
	// We do 1 - n2b.out[depth] as we want to go left if the bit is 0
	out <== GO_LEFT * (1 - is_parent) + GO_LEFT * is_parent * (1 - n2b.out[depth]);
}

template Blake3GetFinal_m() {
	signal input h[8];
	signal input m[16];
	signal input is_parent;
	// TODO: hrmm
	signal input depth;
	signal input chunk_idx;

	signal output out_m[16];

	//  Set to 1 if the child path towards the leaf goes down to the leaf
	//  0 otherwise
	// TODO:
	component down_left_path = Blake3GetDownLeftPath(); down_left_path.depth <== depth; down_left_path.leaf_idx <== chunk_idx; down_left_path.is_parent <== is_parent;

	signal m_is_leaf[16];
	signal m_is_parent[16];

	for (var i = 0; i < 16; i++) {
		m_is_leaf[i] <== m[i] * (1 - is_parent);

		if (i < 8) { // For the left child
			// If the path goes to the right, we fill the left child with aux CV
			m_is_parent[i] <== m[i] * (1 - down_left_path.out) + h[i] * down_left_path.out;
		} else { // For the right child
			m_is_parent[i] <== m[i - 8] * down_left_path.out + h[i - 8] * (1 - down_left_path.out);
		}
		out_m[i] <== m_is_leaf[i] * (1 - is_parent) + m_is_parent[i] * is_parent;
	}

}

template Blake3GetFlag(D_FLAGS) {
	var FIRST_BLOCK_FLAG = 1;
	var LAST_BLOCK_FLAG = 2;
	var PARENT_FLAG = 4;
	var ROOT_FLAG = 8;

	signal input is_parent;
	signal input is_root;
	signal input block_count;
	signal input n_blocks;

	signal output out;
	signal output is_last_block;

	component not_root = NOT(); not_root.in <== is_root;
	component not_parent = NOT(); not_parent.in <== is_parent;

 	component check_block_counts[2]; check_block_counts[0] = IsEqual(); check_block_counts[1] = IsEqual();
	// Check if the block is the first block
	check_block_counts[0].in[0] <== block_count;
	check_block_counts[0].in[1] <== 0;
	// Check if the block is the last block
	check_block_counts[1].in[0] <== block_count;
	check_block_counts[1].in[1] <== n_blocks - 1;

	is_last_block <== check_block_counts[1].out * not_parent.out;

	//  TODO: flags to seperate component
	component first_block_flag_set = AND(); first_block_flag_set.a <== check_block_counts[0].out; first_block_flag_set.b <== not_parent.out;
	component last_block_flag_set = AND(); last_block_flag_set.a <== check_block_counts[1].out; last_block_flag_set.b <== not_parent.out;

	
	// We use root flag if we have a standalone chunk (without a tree path) and are on the last block
	// **OR** we are in the root of a >1 depth tree (non-trivial tree)
	component use_root_flag_tmp = OR(); use_root_flag_tmp.a <== is_parent; use_root_flag_tmp.b <== check_block_counts[1].out;
	signal use_root_flag <== use_root_flag_tmp.out * is_root;

	// Set d flag according to the block count. 2^0 for first block, 2^1 for last block if we are a leaf
	out <== D_FLAGS
					+ FIRST_BLOCK_FLAG * first_block_flag_set.out // Need (not parent) && first block
					+ LAST_BLOCK_FLAG * last_block_flag_set.out
					+ ROOT_FLAG * use_root_flag // ROOT
					+ is_parent * PARENT_FLAG; // TODO: what with BAO
}

template Blake3Nova(
	D_FLAGS
) {
	/************************* Public Input ***********************/
	signal input n_blocks;
	signal input block_count;
  signal input  h[8];         // the block state (8 words) input
	signal input chunk_idx;

	// Bound total_depth max is 64 as per Blake3 spec (max input size is 2 ^ 64)
	signal input total_depth;
	// From [0, total_depth). Depth is 0 indexed. Leaf is depth total_depth - 1, root is 0
	signal input depth;
	// TODO: check that n_blocks <= 16

	/************************* Auxilary (private) Input ***********************/
	// If we are a parent node, we use the first 8 words as the chaining value
	// Of the child which is not on the path towards the leaf
  signal input  m[16];        // the message block (16 words)
  signal input b;

	/************************* Public Outputs ***********************/
	// We have to ensure that the **public** outputs are the same shape as public inputs
	signal output n_blocks_out;
	signal output block_count_out;
	signal output h_out[8];
	signal output total_depth_out;
	signal output depth_out;
	signal output chunk_idx_out;

	/************************* Get depth ***********************/
	component check_depth = Blake3NovaTreePath_CheckDepth();
	check_depth.depth <== depth;
	check_depth.total_depth <== total_depth;

	/************************* Get flags ***********************/
	component comp_d = Blake3GetFlag(D_FLAGS);
	comp_d.is_parent <== check_depth.is_parent;
	comp_d.is_root <== check_depth.is_root;
	comp_d.block_count <== block_count;
	comp_d.n_blocks <== n_blocks;

	/************************* Compute Compression func ***********************/
	component iv = IV();
	component blake3Compression = Blake3Compression();
	signal tmpIV[8];
	for (var i = 0; i < 8; i++) {
		// If we are a parent, we override the h values with the default IV
		// as h goes into the m
		tmpIV[i] <== iv.out[i] * check_depth.is_parent;
		blake3Compression.h[i] <== h[i] * (1 - check_depth.is_parent) + tmpIV[i];
	}
	blake3Compression.m <== m;
	blake3Compression.d <== comp_d.out;
	blake3Compression.b <== b;
	// As we always only output one chunk, the output chunk counter is always 0
	blake3Compression.t[0] <== 0; blake3Compression.t[1] <== 0;
	
	// Set Blake3 output
	for (var i = 0; i < 8; i++) { h_out[i] <== blake3Compression.out[i]; }
	
	// Only update if we are not a parent
	block_count_out <== block_count + (1 - check_depth.is_parent);
	n_blocks_out <== n_blocks;

	component check_decr_depth = OR();
	check_decr_depth.a <== comp_d.is_last_block;
	check_decr_depth.b <== check_depth.is_parent;

	//  TODO: is 1 - OK?
	signal decr_depth <== check_decr_depth.out * (1 - check_depth.is_root); // Decr if (chunk end or is parent) and (not root)
	// Only updated depth if we have read until the final block of a chunk or
	// we are already at a parent
	depth_out <== depth - 1 * decr_depth;
	total_depth_out <== total_depth;
	chunk_idx_out <== chunk_idx;
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

