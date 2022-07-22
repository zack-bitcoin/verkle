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

I changed the field multiplication speed to 1.5*10^-7, because that is how fast I got it to run on my computer. I similarly decreased the elliptic curve speed to 6*10-5, because that is the speed I can get it to run.


The calculator gives: prover time, verify proof, verify updates.

To test out this 20k example, slightly modify the benchmark so that it uses sequential instead of random keys for the leaves. then do a benchmark of 20k

finite field multiplication is estimated in fq2:test(9).

elliptic multiplication is estimated in fq2:test(22). speedup in context of ipa is measured in ipa:test(4).

| Operation | should be | is | how many times slower this is than the ideal |
|----------|-------------|-------|------|
| field multiplication | 6*10^-8 | 1.5*10^-7 | 2.5 |
| elliptic multiplication | 8*10^-5 | 6*10^-5 | 0.75 |
| elliptic multiplication fixed base | 1*10^-5 | 2.8*10^-5 | 2.8 |
| prover time | 14.3 | 6.5 | 0.45 |
| verify proof | 0.55 | 1.6 | 2.9 |
| verify updates | 0.81 | 1.7225 | 2.1 |


Benchmark.
===========



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

