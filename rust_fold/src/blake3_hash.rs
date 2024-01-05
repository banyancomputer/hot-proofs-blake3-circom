use std::{
    cmp::min,
    io::Read,
    path::{self, Path},
};

use blake3::{hash, Hash};
use num_traits::Float;

use crate::{
    blake3_circuit::{PathDirection, PathNode},
    utils::get_depth_from_n_leaves,
    MAX_BYTES_PER_CHUNK,
};

pub(crate) fn hash_with_path(
    input: &[u8],
    leaf: usize,
) -> Result<(Hash, Vec<PathNode>), std::io::Error> {
    let n_chunks = (input.len() + MAX_BYTES_PER_CHUNK - 1) / MAX_BYTES_PER_CHUNK;
    debug_assert!(leaf < n_chunks);
    // TODO: remove later
    assert!(
        n_chunks.count_ones() == 1,
        "n_chunks must be a power of 2 for now"
    );

    // Storage provider keeps this in memory? idk...
    // TODO: we simply need to store and load encoded file
    let (encoded, hash) = bao::encode::encode(input);

    // These parameters are multiples of the chunk size, which avoids unnecessary overhead.
    let slice_start = (leaf * MAX_BYTES_PER_CHUNK) as u64;
    // TODO: what happens if smaller?
    let slice_len = min(MAX_BYTES_PER_CHUNK, input.len() - slice_start as usize) as u64;

    let encoded_cursor = std::io::Cursor::new(&encoded);
    let mut extractor = bao::encode::SliceExtractor::new(encoded_cursor, slice_start, slice_len);
    // Bytes [0..8]: Header. We can throw this away
    // Bytes: [-(slice_len):] the data of the chunk itself
    //
    let mut slice = Vec::new();
    extractor.read_to_end(&mut slice)?;

    let mut decoded = Vec::new();

    let mut decoder = bao::decode::SliceDecoder::new(&*slice, &hash, slice_start, slice_len);

    decoder.read_to_end(&mut decoded)?;
    // decoder.shared.state;

    let mut path_nodes = Vec::new();
    let parent_cvs = &slice[8..(slice.len() - slice_len as usize)];
    let path_len = parent_cvs.len() / 64;

    let mut path_dir = vec![];

    for i in 0..path_len {
        let dir = if leaf & (1 << i) == 0 {
            PathDirection::Left
        } else {
            PathDirection::Right
        };
        path_dir.push(dir);
    }

    // // TODO: WHAT IS GOING WITH 64?
    for (i, chunk) in parent_cvs.chunks(64).into_iter().enumerate() {
        let dir = &path_dir[i];
        println!("Parent CV: {:?}", chunk);
        // TODO: IDK IF LEFT VS RIGHT IS CORRECT HERE
        let chunk_array = if dir == &PathDirection::Left {
            let mut chunk_array = [0u8; 32];
            // Get the right child as we descend left
            chunk_array.copy_from_slice(&chunk[32..64]);
            chunk_array
        } else {
            // Get the left child as we descend right
            let mut chunk_array = [0u8; 32];
            chunk_array.copy_from_slice(&chunk[0..32]);
            chunk_array
        };
        // Wait, its either 0..32 or 32..64 depending on left or right
        debug_assert!(chunk.len() == 64);
        path_nodes.push(PathNode::new(dir.clone(), chunk_array));
    }

    // println!("slice: {:?} {}", slice, slice.len());
    // println!("hash: {:?}", hash.as_bytes());
    // TODO: document are change convention
    // Reverse the path nodes as we consider a path from root to the leaf
    path_nodes.reverse();
    Ok((hash, path_nodes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_with_path() {
        // Two full chunks
        // Two levels, 64
        // Three levels, 128
        // Four, 192
        let input = [3 as u8; 1_024 * 8];
        let (hash, path_nodes) = hash_with_path(&input, 1).unwrap();
        println!("path_nodes: {:?}", path_nodes);
        // assert!(path_nodes.len() == 1);
    }
}
