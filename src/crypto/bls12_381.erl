-module(bls12_381).
-export([]).

%u = -0xd201000000010000

%k = 12

%q = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

%r = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

%E(Fq) := y^2 = x^3 + 4

%Fq2 := Fq[i]/(x^2 + 1)

%E'(Fq2) := y^2 = x^3 + 4(i + 1)

