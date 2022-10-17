Verkle Tree
===========

Pedersen-commitment based verkle trees using the ed25519 elliptic curve.

learn about verkle trees here:
https://vitalik.ca/general/2021/06/18/verkle.html

Techniques used in this software:


How big are the proofs?
==============

The verkle tree has a radix of 256. So, if there are N elements in the tree, then a proof for a single element would be log_256(N) steps long.
If you are proving more than one thing, then they share steps. So if you are proving 1000 things, the proof is more like 1000*(log_256(N) - 1) steps long.
For each step we need to store a 32 byte compressed elliptic curve point.

We also need to store some fixed sized data.

There are 2 different formats for the proofs. Sometimes we want the proof to be very small, and are willing to put extra effort in. In that case, we use the bullet proof method, and the extra data is only 17 elliptic curve points, each 32 bytes. So, 544 bytes total.

If we want to generate the proof very quickly, we can skip the bullet proof step, and the proof ends up being longer. It needs to have 256 finite field elements, each 32 bytes long. So, 8192 bytes total.

If the Tree has N elements, and you want to prove M of them.

Fast: 8192 + (32*M*(log_256(N) - 1)).

Small: 544 + (32*M*(log_256(N) - 1)).

Small proofs are usually better if we are proving many things, and fast proofs are usually better if we are proving very few things.

In the context of a blockchain, we use the fast proofs for light nodes, and the small proofs in blocks.

Speed tests, and results on a lenovo thinkpad 2017 laptop.
===========

units are in microseconds (millionths of a second) unless otherwise specified.

finite field speed tests: `fr:test(8).`
(if you run this test several times, it speeds up. I think there is some caching involved.)

multiplication: 0.1

subtraction: 0.08

additions: 0.1


elliptic point multiplication speed test `ed:test(6).`: 235

elliptic point doubling speed test `ed:test(17).` : 0.9

elliptic point doubling speed test `ed:test(18).` : 1.15


proving 3 things. 'test_trie:test(1).`

load 10 000 elements: 2.36 seconds

make a small proof: 0.97 seconds

verify the small proof: 0.2 seconds

make a fast proof: 0.075 seconds

verify the fast proof: 0.066 seconds


Load a db with 10 000 elements, and prove 3000 of them with a small proof.

loading the db: 5.7 seconds

making the proof: 2.2 seconds

verifying the proof: 0.57 seconds

calculating the root hash after the update: 3.3 seconds

storing the updated data in the database: 0.35 seconds


Installation
=============

You need to install erlang first to use this database.

To run the software: ```sh start.sh```

to turn off the software, and save everything
```verkle_sup:stop(ID).```

where ID is the name of the database (this allows for multiple databases.)

The test database is `trie01`.


Tests that the software works.
============

To do all integration tests: `test_trie:test().`

If you know which integration test you want to do: `test_trie:test(3).`

replace the `3` with the number of the test you wan to do.

Many modules have their own unit tests. They are located at the bottom of the page in the same module that they are testing. You can run all of the unit tests like this: `unit_tests:doit(0).`

Speed comparison.
===========

Here is a calculator to get an idea for how much it should cost to do different things with the verkle tree and libraries.

https://docs.google.com/spreadsheets/d/1740XUDJ89aSRE-4HBD44brjGake_MRAqC4YF7YcEScE/edit

Cryptography used 
===========

inner product argument bullet proofs: https://dankradfeist.de/ethereum/2021/07/27/inner-product-arguments.html

polynomial multiproofs: https://dankradfeist.de/ethereum/2021/06/18/pcs-multiproofs.html

Ed25519 https://en.wikipedia.org/wiki/EdDSA#Ed25519
It is defined like this.
The prime for the finite field: `q = 2^255 - 19`
Curve equation: `-x^2 + y^2 = 1 - ((121665/121666) * x^2 * y^2 )`
These are the algorithms we can use for operations on the elliptic curve: http://hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html

[ed25519 elliptic curve](src/crypto/ed.erl)
[algorithms for elliptic curve operations in C.](/src/crypto/ed25519.c)

[multi exponentiation with bucket method.](src/crypto/multi_exponent.erl)
[precomputed multi exponentiation with bucket method.](src/crypto/precomputed_multi_exponent.erl)

[bulletproofs inner product using pedersen commitments.](src/crypto/ipa.erl)
[polynomials in evaluation format.](src/crypto/poly.erl)
[polynomials multiproofs.](src/crypto/multiproof.erl)

