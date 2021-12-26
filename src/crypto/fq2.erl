-module(fq2).
-export([
         mul/2, 
         add/2, 
         sub/2, %inverse/1,
         encode/1, decode/1,
         setup/1,
         test/1,
         ctest/1
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
decode(C) ->
    B = reverse_bytes(C),
    A = fq:decode(B),
    A.
    %<<A:256>> = reverse_bytes(B),
    %fq:mul(<<A:256>>, <<1:256>>).
    %ok.
   
%these functions are defined in c. 
add(_, _) -> ok.
sub(_, _) -> ok.
mul(_, _) -> ok.

-define(sub3(A, B),
    if
        B>A -> A + ?q - B;
        true -> A - B
    end).

ctest(_) ->
    ok.

range(N, N) -> [N];
range(A, B) when (A < B) -> 
    [A|range(A+1, B)].
test(1) ->
    check_constants();
test(2) ->
    io:fwrite("subtract test\n"),
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
      %Af > Bf,
      S1 == S2,
      S1
      %S2,
      %fq:sub2(Af, Bf),
      %<<(?sub3(A2, B2)):256>>
    };
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
    io:fwrite("addition test\n"),
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
    %add(<<0:256>>, <<0:256>>),
    S1 = reverse_bytes(add(A, B)),
    S2 = fq:add2(Af, Bf),
    {S1 == S2, S1, S2};
test(6) ->
    %testing multiplication.
    io:fwrite("multiply test \n"),
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
    Bool = S1 == S2,
    if
        not(Bool) -> 
            io:fwrite("test failed"),
            {A, B, S1, S2};
        true ->
            {S1 == S2, S1, S2, fq:decode(S1)}
    end;
test(7) ->
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    A1 = (A0 div 1) rem ?q,
    B1 = (B0 div 1) rem ?q,
    A = encode(A1),
    B = encode(B1),
    Many = 50000,
    R = range(B0, B0 + Many),
    R2 = lists:map(
           fun(X) -> encode(X rem ?q) end, R),
    T1 = erlang:timestamp(),
    lists:map(fun(I) ->
                      mul(A, I)
              end, R2),
    T2 = erlang:timestamp(),
    lists:map(fun(I) ->
                      C0 = (A0 * I) rem ?q
              end, R),
    T3 = erlang:timestamp(),
    io:fwrite("multiply speed test \n"),
    {{c, timer:now_diff(T2, T1)/Many},
     {erl, timer:now_diff(T3, T2)/Many}};
test(8) ->
    %more accurate multiplication speed test.
    Many = 100000,
    R = lists:map(fun(_) ->
                          <<A0:256>> = crypto:strong_rand_bytes(32),
                          <<B0:256>> = crypto:strong_rand_bytes(32),
                          {A0 rem ?q,
                           B0 rem ?q}
                  end, range(0, Many)),
    R2 = lists:map(fun({X, Y}) ->
                           {encode(X),
                            encode(Y)}
                   end, R),
    T1 = erlang:timestamp(),
    lists:foldl(fun({X, Y}, _) ->
                      (X*Y) rem ?q,
                        0
                end, 0, R),
    T2 = erlang:timestamp(),
    lists:foldl(fun({X, Y}, _) ->
                        mul(X, Y),
                        0
                end, 0, R2),
    T3 = erlang:timestamp(),
    %erl sub
    lists:foldl(fun({X, Y}, _) ->
                      if
                          X > Y -> X - Y;
                          true -> ?q - Y + X
                      end,
                        0
                end, 0, R),
    T4 = erlang:timestamp(),
    %c sub
    lists:foldl(fun({X, Y}, _) ->
                        sub(X, Y)
                end, 0, R2),
    T5 = erlang:timestamp(),
    lists:foldl(fun({X, Y}, _) ->
                      C = X+Y,
                      if
                          C > ?q -> C - ?q;
                          true -> C
                      end,
                        0
                end, 0, R),
    T6 = erlang:timestamp(),
    lists:foldl(fun({X, Y}, _) ->
                  add(X, Y),
                  0
          end, 0, R2),
    T7 = erlang:timestamp(),
    lists:foldl(fun(A, B) -> 0 end, 0, R2),
    T8 = erlang:timestamp(),
    Empty = timer:now_diff(T8, T7),
    MERL = timer:now_diff(T2, T1),
    MC = timer:now_diff(T3, T2),
    SERL = timer:now_diff(T4, T3),
    SC = timer:now_diff(T5, T4),
    AERL = timer:now_diff(T6, T5),
    AC = timer:now_diff(T7, T6),

    {{empty, Empty/Many},
     {mul, {erl, (MERL - Empty)/Many},
      {c, (MC - Empty)/Many}},
     {sub, {erl, (SERL - Empty)/Many},
      {c, (SC - Empty)/Many}},
     {add, {erl, (AERL - Empty)/Many},
      {c, (AC - Empty)/Many}}};
test(9) ->
    %multiplication bug
    A = <<163,111,88,19,242,144,5,56,171,153,103,125,198,
   159,249,154,223,13,25,194,47,169,14,84,131,68,
   162,240,108,177,197,59>>,
    B = <<168,169,122,20,250,154,42,13,18,192,244,200,78,
      125,170,150,60,139,147,21,249,194,146,233,147,
      181,70,152,48,94,173,79>>,
    A1 = decode(A),
    B1 = decode(B),
    Af = fq:encode(A1),
    Bf = fq:encode(B1),
    S1 = reverse_bytes(mul(A, B)),
    S2 = fq:mul(Af, Bf),
    <<C1:256>> = <<(A1*B1):256>>,

    <<NA:256>> = A,
    <<NB:256>> = B,
    C = <<((NA*NB) rem ?q):256>>,

    {S1 == S2, S1, S2, fq:encode((A1*B1) rem ?q)};
test(10) ->
    A = crypto:strong_rand_bytes(32),
    test(A).

    
                          


