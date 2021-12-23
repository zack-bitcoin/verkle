-module(fq).
-export([
         mul/2, add/2, sub/2, sub2/2, inverse/1,
         encode/1, decode/1,
         setup/1,
         test/1
        ]).
-on_load(init/0).
init() ->
    ok = erlang:load_nif("./ebin/fq", 0),
    setup(0),
    ok.

%This is the finite field on top of BLS12-381
%jubjub is implemented on this curve.

%uses montgomery notation for faster modular multiplication.

%q = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
-define(q, 52435875175126190479447740508185965837690552500527637822603658699938581184513).
-define(qb, <<115,237,167,83,41,157,125,72,51,57,216,8,9,161,216,5,83,189,164,2,255,254,91,254,255,255,255,255,0,0,0,1>>).
-define(q_bits, 256).
-define(q_bits2, 512).

-define(iq, 27711634432943687283656245953990505159342029877880134060146103271536583507967).
-define(iqb, 
<<61,68,58,176,215,191,40,57,24,27,44,23,0,4,236,
  6,83,186,91,255,255,254,91,253,255,255,255,254,
  255,255,255,255>>).

%2^256
-define(r, 115792089237316195423570985008687907853269984665640564039457584007913129639936).
%2^256 rem n
-define(r1, 10920338887063814464675503992315976177888879664585288394250266608035967270910).
-define(r1b, 
<<24,36,177,89,172,197,5,111,153,140,79,239,236,
  188,79,245,88,132,183,250,0,3,72,2,0,0,0,1,255,
  255,255,254>>).
%r*r rem n
-define(r2, 
        3294906474794265442129797520630710739278575682199800681788903916070560242797).
-define(r2b, 
<<7,72,217,217,159,89,255,17,5,211,20,150,114,84,
  57,143,43,108,237,203,135,146,92,35,201,153,233,
  144,243,242,156,109>>).
%r*r*r rem n
-define(r3, 
        49829253988540319354550742249276084460127446355315915089527227471280320770991).
-define(r3b,
<<110,42,91,185,200,219,51,233,115,209,60,113,199,
  181,244,24,27,62,13,24,140,240,105,144,198,44,
  24,7,67,155,115,175>>).

%1/r rem n
-define(ir, 
        12549076656233958353659347336803947287922716146853412054870763148006372261952).
-define(irb,
<<27,190,134,147,48,0,157,87,114,4,7,138,79,119,
  38,106,171,111,202,143,9,220,112,95,19,247,91,
  105,254,117,192,64>>).

check_constants() -> 
    ?iq = prime_reverse(?q),
    true = ?r > ?q,
    1 = (?q rem 2),
    true = power_of_2(?r),
    ?r1 = (?r rem ?q),
    ?r2 = ((?r * ?r) rem ?q),
    ?ir = ff:inverse(?r, ?q),
    ?qb = <<(?q):256>>,
    ?iqb = <<(?iq):256>>,
    ?r1b = <<(?r1):256>>,
    ?r2b = <<(?r2):256>>,
    ?irb = <<(?ir):256>>,
    ok.
prime_reverse(N) ->
    %Used to calculate the IN input for redc.
    (?r - 1)*ff:inverse(N, ?r) rem ?r.
power_of_2(1) -> true;
power_of_2(N) when ((N rem 2) == 0) -> 
    power_of_2(N div 2);
power_of_2(_) -> false.

redc(<<T:?q_bits2>>) ->
    redc(?qb, ?iqb, <<T:?q_bits2>>).
redc(<<Q:?q_bits>>, <<IQ:?q_bits>>, <<T:?q_bits2>>) ->
    <<Tb:?q_bits>> = <<T:?q_bits>>,
    <<M:?q_bits>> = <<(Tb*IQ):?q_bits>>,
    <<T2:?q_bits, _/binary>> = <<(T + (M*Q)):?q_bits2>>,
    R = if
            (T2 >= Q) -> T2 - Q;
            true -> T2
        end,
    <<R:256>>.
mul(<<A:?q_bits>>, <<B:?q_bits>>) ->
    redc(<<(A*B):?q_bits2>>).
add(<<A:?q_bits>>, <<B:?q_bits>>) ->
    C = A+B,
    D = if
            C > ?q -> C-?q;
            true -> C
        end,
    <<D:?q_bits>>.
sub(<<A:?q_bits>>, <<B:?q_bits>>) ->
    %this version is defined in C.
    ok.
sub2(<<A:?q_bits>>, <<B:?q_bits>>) ->
    C = if
            B > A -> A + (?q - B);
            true -> A - B
        end,
    <<C:?q_bits>>.
-define(sub3(A, B),
    if
        B>A -> A + ?q - B;
        true -> A - B
    end).
sub3(A, B) ->
    ?sub3(A, B).
                
inverse(<<A:?q_bits>>) ->
    I = ff:inverse(A, ?q),
    redc(<<(I*?r3):512>>).
   
encode(A) when ((A < ?q) and (A > -1)) -> 
    redc(<<(?r2 * A):?q_bits2>>).
decode(<<A:256>>) ->
    mul(<<A:256>>, <<1:256>>).

setup(_) ->
    ok.



many(_, 0) -> [];
many(X, N) when N > 0 -> 
    [X|many(X, N-1)].

range(N, N) -> [N];
range(A, B) when (A < B) -> 
    [A|range(A+1, B)].
test(1) ->
    check_constants();
test(2) ->
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    A1 = A0 rem ?q,
    B1 = B0 rem ?q,
    A = encode(A1),
    B = encode(B1),
    %setup(0),
    true = sub(A, B) == sub2(A, B),
    {A, B,
     sub(A, B),
     sub2(A, B)};
test(3) ->
    <<A0:256>> = crypto:strong_rand_bytes(32),
    A1 = A0 rem ?q,
    A = encode(A1),
    A = inverse(inverse(A));
test(4) ->
    %speed test
    %setup(0),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    %A1 = (A0 div 1) rem ?q,

    %todo. when A<B, the C version is faster. otherwise, the erlang version is faster.

    Many = 100000,
    B1 = (B0 div 1) rem ?q,
    A1 = (B1 - (Many div 2)) rem ?q,
    A = encode(A1),
    B = encode(B1),
    Ar = fq2:encode(A1),
    Br = fq2:encode(B1),
    T1 = erlang:timestamp(),
    R = range(B1, Many+B1),
    R2 = lists:map(fun(I) -> <<I:256>> end, R),
    lists:map(fun(I) ->
                      sub(A, I)
              %end, R2),
              end, []),
    T2 = erlang:timestamp(),
    lists:map(fun(I) ->
                      sub2(A, I)
              %end, R2),
              end, []),
    T3 = erlang:timestamp(),
    lists:map(fun(I) ->
                      ?sub3(A1, I)
              end, R),
    T4 = erlang:timestamp(),
    lists:map(fun(I) ->
                      fq2:sub(Ar, I)
              end, R2),
    T5 = erlang:timestamp(),
    {
      %{c, timer:now_diff(T2, T1)/Many},%0.36
    %{erlang, timer:now_diff(T3, T2)/Many},%0.6
     {erl_int, timer:now_diff(T4, T3)/Many},
      {c_rev, timer:now_diff(T5, T4)/Many}
    }.%0.16

%sub is 0.11 from secp256k1.
% is 0.524 here.


    

    
    
