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

Speed comparison.
===========

Here is a calculator to get an idea for how much it should cost to do different things with the verkle tree and libraries.

https://docs.google.com/spreadsheets/d/1740XUDJ89aSRE-4HBD44brjGake_MRAqC4YF7YcEScE/edit

Lets look at how this software is falling short of the ideal.

to use this calculator to get an idea of tree proof speed, im plugging in 20 000 branch accesses, 60 000 chunk accesses, 20 000 branches updated, 60 000 chunks updated, and 60 000 chunks newly created.
The calculator gives: prover time, verify proof, verify updates.

To test out this 20k example, slightly modify the benchmark so that it uses sequential instead of random keys for the leaves. then do a benchmark of 20k

finite field multiplication is estimated in secp256k1.erl, test 15.

elliptic multiplication is estimated in secp256k1:test(9). speedup in context of ipa is measured in ipa:test(4).

| Operation | should be | is | how many times slower this is than the ideal |
|----------|-------------|-------|------|
| field multiplication | 3*10^-8 | 5.1*10^-7 | 17 |
| elliptic multiplication | 4*10^-5 | 2.6*10^-3 | 65 |
| elliptic multiplication fixed base | 5*10^-6 | 2.6*10^-4 | 52 |
| prover time | 4.22 | 15 | 3.4 |
| verify proof | 0.572 | 8.0 | 14 |
| verify updates | 0.766 | 6.4 | 8.4 |


Benchmark.
===========

I loaded 5000 elements into the database. I made a proof of all 5000 of them, and then verified that proof.

Loading took 4.5 seconds.

Making the proof with 1 cpu took 6.0 seconds.

Verifying took 3.0 seconds.

to run the benchmark `benchmark:doit(1).`
time is measured in millionths of a second. 6 decimals.

[you can see the code of the benchmark.](src/benchmark.erl)

benchmark of 20k elements. (it takes 5.5 seconds to load a normal merkle tree with this many elements)

loading: 25 

making proof: 18  

verifying: 7.3

40k

loading: 73

proving: 37

verifying: 12.5

80k

loading: 173

proving: 89

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

