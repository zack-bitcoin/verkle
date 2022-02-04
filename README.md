Verkle Tree
===========

Pedersen-commitment based verkle trees using the jubjub elliptic curve.

This software seems to basically work, but it still has some inefficiencies.
See the todo list for what needs to be done still.

a verkle tree database based on pedersen commitments over the jubjub elliptic curve.

learn about verkle trees here:
https://vitalik.ca/general/2021/06/18/verkle.html

Techniques used in this software:
https://dankradfeist.de/ethereum/2021/07/27/inner-product-arguments.html
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

to use this calculator to get an idea of tree proof speed, im plugging in 20 000 branch accesses, 60 000 chunk accesses, 20 000 branches updated, 60 000 chunks updated, and 60 000 chunks newly created. and I changed the number of elements to 20 000

I changed the field multiplication speed to 6*10^-8, because that is how fast the bitcoin core secp256k1 benchmarks run on my computer. I similarly halved the elliptic curve speed to 8*10-5, because it is bottlenecked by finite field multiplications.


The calculator gives: prover time, verify proof, verify updates.

To test out this 20k example, slightly modify the benchmark so that it uses sequential instead of random keys for the leaves. then do a benchmark of 20k

finite field multiplication is estimated in fq2:test(9).

elliptic multiplication is estimated in fq2:test(22). speedup in context of ipa is measured in ipa:test(4).

| Operation | should be | is | how many times slower this is than the ideal |
|----------|-------------|-------|------|
| field multiplication | 6*10^-8 | 1.5*10^-7 | 2.5 |
| elliptic multiplication | 8*10^-5 | 6*10^-5 | 0.75 |
| elliptic multiplication fixed base | 1*10^-5 | 2.8*10^-5 | 2.8 |
| prover time | 5.726 | 7.9 | 1.38 |
| verify proof | 0.531 | 1.45 | 2.7 |
| verify updates | 1.09 | 3.5 | 3.2 |


Benchmark.
===========

I loaded 5000 elements into the database. I made a proof of all 5000 of them, and then verified that proof.

Loading took 2.6 seconds.

Making the proof with 1 cpu took 2.4 seconds.

Verifying took 0.41 seconds.

to run the secp256k1 benchmark `benchmark:doit(1).`
to run the jubjub benchmark `benchmark:doit(2).`
This page is recording results from the jubjub benchmark.
time is measured in millionths of a second. 6 decimals.

[you can see the code of the benchmark.](src/benchmark.erl)

benchmark of 20k elements. (it takes 5.5 seconds to load a normal merkle tree with this many elements)

loading: 11.3 

making proof: 11.8 

verifying: 2.2

40k

loading: 42

proving: 24

verifying: 5.0

80k

loading: 99

proving: 51

verifying: 14.3

It is also possible to run the database in RAM instead of the hard drive, but it doesn't seem to make it any faster. The bottleneck is on CPU computation of the cryptography, not on accessing memory.


benchmark hard drive usage.
=================

After loading 20k elements into a merkle tree, memory usage is 13 megabytes.

after loading 20k into a verkle tree, memory is 1.8 megabytes.

Crypto used in jubjub version
===========

[jubjub is the same elliptic curve as is used in bitcoin](src/crypto/jubjub.erl)

[the finite field for exponents of jubjub points](src/crypto/fr.erl) [parts of it are written in C](src/crypto/fr.c)

[the finite field for implementing jubjub points](src/crypto/fq2.erl) [parts of it are in C](src/crypto/fq2.c)

[multi-exponentiation of jubjub points](src/crypto/multi_exponent.erl)

[pedersen commitments and inner product arguments](src/crypto/ipa2.erl)

[precomputed bucket algorithm for efficient storage is in here](src/store2.erl)

[polynomial libraries for using polynomials in evaluation format](src/crypto/poly2.erl)

[for combining inner product arguments into a single small proof, based on bullet proof method](src/crypto/multiproof2.erl)

Crypto used in Secp256k1 version
==============

[secp256k1 is the same elliptic curve as is used in bitcoin](src/crypto/secp256k1.erl)
Includes the bucket algorithm for efficiently calculating multi-exponents.
Stores elliptic points in jacobian format for efficiency.
Includes a function for batch simplifying jacobian points, to set their Z values to 1.

[pedersen commitments and inner product arguments on top of secp256k1](src/crypto/ipa.erl)

[polynomial library for polynomials stored in evaluation format, as recommended by Dankrad Feist](src/crypto/poly.erl)

[for combining pedersen commitments into a single constant sized proof](src/crypto/multiproof.erl)

