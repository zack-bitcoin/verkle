-module(fq2).
-export([
         mul/2, 
         add/2, 
         sub/2, %inverse/1,
         encode/1, decode/1,
         setup/1,
         test/1
        ]).
-on_load(init/0).
init() ->
    ok = erlang:load_nif("./ebin/fq2", 0),
    setup(0),
    ok.

setup(_) ->
    %defined in C.
    ok.

%This is the finite field on top of BLS12-381
%jubjub is implemented on this curve.

%uses montgomery notation for faster modular multiplication.

%binaries store bytes in reverse order in comparison to normal erlang binaries. This way when we pass the binaries to C, the bytes are already in order to fit into bigger registers.

%q = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
-define(q, 52435875175126190479447740508185965837690552500527637822603658699938581184513).
-define(q_bits, 256).
-define(q_bits2, 512).

-define(iq, 27711634432943687283656245953990505159342029877880134060146103271536583507967).

%2^256
-define(r, 115792089237316195423570985008687907853269984665640564039457584007913129639936).

%2^256 rem q
-define(r1, 10920338887063814464675503992315976177888879664585288394250266608035967270910).

%r*r rem q
-define(r2, 3294906474794265442129797520630710739278575682199800681788903916070560242797).

%r*r*r rem n
-define(r3, 49829253988540319354550742249276084460127446355315915089527227471280320770991).

%1/r rem n
-define(ir, 12549076656233958353659347336803947287922716146853412054870763148006372261952).

check_constants() -> 
    ?iq = prime_reverse(?q),
    true = ?r > ?q,
    1 = (?q rem 2),
    true = power_of_2(?r),
    ?r1 = (?r rem ?q),
    ?r2 = ((?r * ?r) rem ?q),
    ?ir = ff:inverse(?r, ?q),
    ok.
prime_reverse(N) ->
    %Used to calculate the IN input for redc.
    (?r - 1)*ff:inverse(N, ?r) rem ?r.
power_of_2(1) -> true;
power_of_2(N) when ((N rem 2) == 0) -> 
    power_of_2(N div 2);
power_of_2(_) -> false.

%todo. binary:encode_unsigned(X, little) is probably faster.
reverse_bytes(X) ->
    reverse_bytes(X, <<>>).
reverse_bytes(<<A, B/binary>>, R) ->
    reverse_bytes(B, <<A, R/binary>>);
reverse_bytes(<<>>, R) -> R.

encode(A) when ((A < ?q) and (A > -1)) ->
    B = fq:encode(A),
    reverse_bytes(B).
decode(<<A:256>>) ->
    %<<A:256>> = reverse_bytes(B),
    %fq:mul(<<A:256>>, <<1:256>>).
    ok.
   
%these functions are defined in c. 
add(_, _) -> ok.
sub(_, _) -> ok.
mul(_, _) -> ok.

-define(sub3(A, B),
    if
        B>A -> A + ?q - B;
        true -> A - B
    end).

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
    Af = fq:encode(A1),
    Bf = fq:encode(B1),
    <<A2:256>> = Af,
    <<B2:256>> = Bf,
%    true = reverse_bytes(sub(A, B)) ==
%        fq:sub(Af, Bf),
    S1 = reverse_bytes(sub(A, B)),
    S2 = fq:sub(Af, Bf),
    {
      Af > Bf,
      S1 == S2,
      S1,
      S2,
      fq:sub2(Af, Bf),
      <<(?sub3(A2, B2)):256>>};
%    true = sub(A, B) == reverse_bytes(fq:sub(A, B)),
%    success;
test(3) ->
    <<A0:256>> = crypto:strong_rand_bytes(32),
    A1 = A0 rem ?q,
    A = encode(A1),
    A1 = decode(A);
%A = inverse(inverse(A));
test(4) ->
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    A1 = (A0 div 1) rem ?q,
    B1 = (B0 div 1) rem ?q,
    A = encode(A1),
    B = encode(B1),
    T1 = erlang:timestamp(),
    Many = 50000,
    lists:map(fun(_) ->
                      sub(A, B)
              end, range(0, Many)),
    T2 = erlang:timestamp(),
    {c, timer:now_diff(T2, T1)/Many};
test(5) ->
    %testing addition.
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    A1 = A0 rem ?q,
    B1 = B0 rem ?q,
    A = encode(A1),
    B = encode(B1),
    Af = fq:encode(A1),
    Bf = fq:encode(B1),
    <<A2:256>> = Af,
    <<B2:256>> = Bf,
    S1 = reverse_bytes(add(A, B)),
    S2 = fq:add2(Af, Bf),
    {S1 == S2, S1, S2};
test(6) ->
    %testing multiplication.
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    %A0 = 2,
    %B0 = 3,
    A1 = A0 rem ?q,
    B1 = B0 rem ?q,
    A = encode(A1),
    B = encode(B1),
    Af = fq:encode(A1),
    Bf = fq:encode(B1),
    <<A2:256>> = Af,
    <<B2:256>> = Bf,
    S1 = reverse_bytes(mul(A, B)),
    S2 = fq:mul(Af, Bf),
    {S1 == S2, S1, S2, fq:decode(S1)}.

