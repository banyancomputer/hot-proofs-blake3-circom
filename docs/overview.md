
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

So, to cope with the above, we use proof folding (TODO: ) to create the proofs. Thusly, we can break up proof production into manageable chunks.

<!-- TODO: verification of what exactly here.... markdown or nah? -->