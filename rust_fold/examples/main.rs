use blake3_fold::prove_chunk_hash;
use blake3::hash;

fn main() {
    // prove_chunk_hash(bytes)
    let data = vec![0 as u8; 1];
    let hash = hash(&data);
    println!("Hash: {:?}", hash);
		assert!(prove_chunk_hash(data).is_ok());
    println!("Hash: {:?}", hash);
}