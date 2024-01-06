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
	signal input total_depth;

	signal output out;

	component n2b = Num2Bits(65); // Max depth is 64 and so leaf max is 2^64. Pad with 1 for 65
	n2b.in <== leaf_idx;

	//  Here 0 and i are associated to depth
	signal tmp[65];
	component eqs[65];
	eqs[0] = IsEqual(); eqs[0].in[0] <== depth; eqs[0].in[1] <== total_depth - 0 - 1;
	tmp[0] <== (1 - n2b.out[0]) * eqs[0].out;

	for (var i = 1; i < 65; i++) {
		eqs[i] = IsEqual(); eqs[i].in[0] <== depth; eqs[i].in[1] <== total_depth - i - 1;
		tmp[i] <== tmp[i - 1] + (1 - n2b.out[i]) * eqs[i].out;
	}

	// TODO: S'hizer. We need to loop over all bits and filter by index

	// If we are a leaf, we are always on the left path, but it does not really matter
	// We do 1 - n2b.out[..] as we want to go left if the bit is 0
	// We use total_depth - depth - 1 because:
	// A) -1 is due to 0 indexing offset
	// B) The biggest value bit (and bitify is big endian) is at the end of the array
	out <== GO_LEFT * (1 - is_parent) + GO_LEFT * is_parent * (tmp[64]);
}

template Blake3GetFinal_m() {
	signal input h[8];
	signal input m[16];
	signal input is_parent;
	// TODO: hrmm
	signal input depth;
	signal input total_depth;
	signal input chunk_idx;

	signal output out_m[16];

	//  Set to 1 if the child path towards the leaf goes down to the leaf
	//  0 otherwise
	// TODO:
	component down_left_path = Blake3GetDownLeftPath();
	down_left_path.depth <== depth;
	down_left_path.leaf_idx <== chunk_idx;
	down_left_path.is_parent <== is_parent;
	down_left_path.total_depth <== total_depth;

	signal m_is_parent[16];
	signal tmp_down[16];
	signal tmp_is_par[16];
	for (var i = 0; i < 16; i++) {
		if (i < 8) { // For the left child
		 	tmp_down[i] <== h[i] * down_left_path.out;
			// If the path goes to the right, we fill the left child with aux CV
			m_is_parent[i] <== m[i] * (1 - down_left_path.out) + tmp_down[i];
		} else { // For the right child
		 	tmp_down[i] <== h[i - 8] * (1 - down_left_path.out);
			m_is_parent[i] <== m[i - 8] * down_left_path.out + tmp_down[i];
		}
		tmp_is_par[i] <== m_is_parent[i] * is_parent;
		out_m[i] <== m[i] * (1 - is_parent) + tmp_is_par[i];
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
					+ is_parent * PARENT_FLAG;
	// out <== 3;
	log("D_FLAGS: ", D_FLAGS);
}

template Blake3Nova(
	D_FLAGS
) {
	/************************* Public Input ***********************/
	signal input n_blocks;
	signal input block_count;
  signal input h[8];         // the block state (8 words) input
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
	component final_m = Blake3GetFinal_m();
	signal tmpIV[8];
	signal final_h[8];
	for (var i = 0; i < 8; i++) { 
		tmpIV[i] <== iv.out[i] * check_depth.is_parent;
		final_h[i] <== h[i] * (1 - check_depth.is_parent) + tmpIV[i];
	}
	final_m.h <== final_h;
	final_m.m <== m;
	final_m.is_parent <== check_depth.is_parent;
	final_m.depth <== depth;
	final_m.total_depth <== total_depth;
	final_m.chunk_idx <== chunk_idx;

	component blake3Compression = Blake3Compression();
	blake3Compression.m <== final_m.out_m;
	blake3Compression.h <== final_h;
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
