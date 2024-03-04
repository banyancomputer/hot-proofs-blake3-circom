
# Blake3 HOT Proofs

## Outline

1. Overview
	a. Why Blake3
	b. Why its hard
	c. What we can do about it

2. The Magic of Folding and Compression Functions

3. Preliminary Performance

4. Cryptographic note: why can we hide almost everything?

## Overview
The last few years has seen an explosion of data-availability proof schemes. Unfortunately, most do not use standard hash-function which can "plug and play" with existing checksums. Blake3, on the other hand, is gaining wide spread adoption due to robustness and high speed and low overhead hashing.

Still, adopting Blake3 for data-availability is not a straightforward matter because
1.  Solidity does not have a native Blake3 opcode
2.  The smallest chunk size is 1,024 bytes instead of the more normal 256 bits. The larger chunk size contributes to faster speed and less overhead though.
3. 	Blake3 works over the binary representation of data. I.e. we cannot simply use the arithmetic representation of data. As such, arithmetic proving systems (such as R1CS, Plonkish, CCS, etc.) incur a substantial overhead.

So, to cope with the above, we use cryptographic technique known as folding (TODO: ) to create the proofs. Thusly, we can break up proof production into manageable chunks.


## Hash Functions: Blake3 vs the Rest
Blake3 is the latest in the line of the BLAKE family of cryptographic hash functions. The BLAKE family of hash functions are based on stream ciphers. Blake2, the predecessor to Blake3, is used broadly in industry.
TODO: EXAMPLES

Still, Blake2 has a relatively high overhead and different off-shoots with slightly different functionalities for different use-cases. Blake3 is designed to be a general-purpose hash function which is optimized for speed and robustness. It is also designed to be used in a wide variety of applications, including data-availability proofs.

<!-- TODO: fill in -->
For example, producing a Blake3 hash of a 1,024 byte chunk of data takes about BLAH BLAH BLAH on a modern CPU. This is about BLAH BLAH BLAH faster than the next fastest hash function, SHA-256. This is a substantial improvement in speed and robustness.

Blake3 is specifically designed to be efficient on binary-based CPU architectures. This design choice improves security and efficacy. However, it also means that Blake3 is not as efficient on arithmetic-based proving systems, such as R1CS, Plonkish, CCS, etc. Current data availability proof schemes, such as File-Coin's, use arithmetic hash functions such as Poseidon (TODO: idk if correct, fill this in). While efficient in practice, algebriac hash functions are a relative novelty in the world of cryptography. As such, their robustness is not as well understood and are not as widely used as binary hash functions.

### How Blake3 Works
TODO: flesh out
diagrams and such

<!-- TODO: flesh out -->
## Enter Folding
Folding is a cryptographic technique introduced in (TODO: put here). Based off of ideas from Proof Carrying Data (PCD), folding allows us to break up the proof production process into manageable chunks. Rather than produce a proof of the entire data-availbility proof at once, we can create a proof of one-chunk at a time.

As seen above (TODO: link), computing a Blake3 hash can be thought of as the chaining of compression functions.

If we have at most 1024 bytes of data, we chain linearly, computing one after another
(TODO: picture)

If we have more data, we form a tree of compression functions, in a very similar manner to a Merkle tree.
