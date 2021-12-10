Verkle Tree
===========

Pure erlang implementation of pedersen-commitment based verkle trees.

This software seems to basically work, but it still has some inefficiencies.
See the todo list for what needs to be done still.

a verkle tree database based on pedersen commitments over the secp256k1 elliptic curve.
Written in pure erlang.

learn about verkle trees here:
https://vitalik.ca/general/2021/06/18/verkle.html

Techniques used in this software:
https://dankradfeist.de/ethereum/2021/06/18/pcs-multiproofs.html

Installation
=============

You need to install erlang first to use this database.

To run the software: ```sh start.sh```

Then, to run the benchmark: `benchmark:doit(1).`

Benchmark.
===========

I loaded 5000 elements into the database. I made a proof of all 5000 of them, and then verified that proof.

Loading took 7.0 seconds.

Making the proof with 1 cpu took 6.5 seconds.

Verifying took 3.4 seconds.

to run the benchmark test `test_trie:test().`
time is measured in millionths of a second. 6 decimals.

[you can see the code of the benchmark.](src/benchmark.erl)

benchmark of 20k elements. (it takes 5.5 seconds to load a normal merkle tree with this many elements)

loading: 16

making proof: 16

verifying: 6.9

40k

loading: 26

proving: 33

verifying: 11

80k

loading: 180

proving: 88

verifying: 23

It is also possible to run the database in RAM instead of the hard drive, but it doesn't seem to make it any faster. The bottleneck is on CPU computation of the cryptography, not on accessing memory.


benchmark hard drive usage.
=================

After loading 20k elements into a merkle tree, memory usage is 13 megabytes.

after loading 20k into a verkle tree, memory is 1.8 megabytes.

Crypto used
==============

[secp256k1 is the same elliptic curve as is used in bitcoin](src/crypto/secp256k1.erl)
Includes the bucket algorithm for efficiently calculating multi-exponents.
Stores elliptic points in jacobian format for efficiency.
Includes a function for batch simplifying jacobian points, to set their Z values to 1.

[pedersen commitments and inner product arguments on top of secp256k1](src/crypto/ipa.erl)

[polynomial library for polynomials stored in evaluation format, as recommended by Dankrad Feist](src/crypto/poly.erl)

[a multiproof system for pedersen commitments](src/crypto/multiproof.erl)

