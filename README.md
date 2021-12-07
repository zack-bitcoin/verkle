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

Benchmark.
===========

I loaded 5000 elements into the database. I made a proof of all 5000 of them, and then verified that proof.

Loading took 7 seconds.

Making the proof with 1 cpu took 22 seconds.

Verifying took 3.9 seconds.

Installation
=============

You need to install erlang first to use this database.

To run the software: ```sh start.sh```
