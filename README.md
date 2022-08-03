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

I changed the field multiplication speed to 1.5*10^-7, because that is how fast I got it to run on my computer. ```fq:test(8).``` (test results in millionths of a second)
  I similarly decreased the elliptic curve speed to 6*10-5, because that is the speed I can get it to run. ```fq:test(22).```
  
For my test, I loaded the tree with 130 000 elements. so I edited the "Number of Elements" variable in the calculator page.

The calculator gives: prover time, verify proof, verify updates.

```
prover time: 2.96 seconds
verify proof: 0.175 seconds
verify updates: 0.215 seconds
```

To run the benchmark, use these commands:
```Loc = test_trie:load_db(130000).```
This loads up the database with 130k dummy elements.

then do:
```test_trie:proof_test(Loc, 6000).```
This creates a proof of 6000 elements, calculates a new root if they are all updated, and then merges the changes to the database.

The results I get are:
 making the proof: 5.3155 seconds
 verifying proof: 3.8292 seconds
 root hash of the updated proof: 5.0938 seconds

So, making the proof is 80% slower than optimal.
verifying the proof is 22x slower than optimal.
calculating the root hash is 24x slower than optimal.




Crypto used 
===========

Ed25519 https://en.wikipedia.org/wiki/EdDSA#Ed25519
It is defined like this.
The prime for the finite field: `q = 2^255 - 19`
Curve equation: `-x^2 + y^2 = 1 - ((121665/121666) * x^2 * y^2 )`
So, these are the algorithms we can use for operations on the elliptic curve: http://hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html

finite field in q.
finite field in r.
elliptic curve operations.
multi exponentiation library.
pedersen commitments library.
inner product library.
precomputed bucket algorithm.
polynomials in evaluation format library.
bulletproofs for inner product arguments.

