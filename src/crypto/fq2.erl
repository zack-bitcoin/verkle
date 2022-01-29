-module(fq2).
-export([
         mul/2, 
         add/2, 
         neg/1,
         sub/2, %inverse/1,
         inv/1,
         square/1,
         pow/2,
         short_pow/2,
         encode/1, decode/1,
         encode_extended/1, decode_extended/1,
         setup/1,
         test/1,
         ctest/1,
         reverse_bytes/1,
         prime/0,
         sqrt/1,

         e_double/1,
         e_add/2,
         %e_mul/2,
         e_mul1/2,
         e_mul2/2,
         e_zero/0,
         eq/2,
         batch_inverse/1,
         e_simplify_batch/1,
         pow_/2,
         e_neg/1,

         gen_point/0,
         gen_point/1,

         extended2extended_niels/1,
         extended_niels2extended/1,
         is_zero/1,
         extended2affine/1,
         to_affine_batch/1
        ]).
-on_load(init/0).
-record(extended_point, {u, v, z, t1, t2}).
-record(extended_niels_point, 
        {v_plus_u, v_minus_u, t2d, z}).

% -(10240/10241)
-define(D, <<176,246,116,185,85,36,82,42,179,202,154,13,239,
             201,108,252,209,40,118,194,148,251,8,122,46,38,
             14,254,168,246,248,87>>).

% 2 * D
-define(D2, <<95,237,233,114,172,72,164,84,103,57,55,27,219,
              239,27,165,158,121,74,123,33,31,216,192,20,207,
              126,210,254,69,4,60>>).

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

%-define(i2, 26217937587563095239723870254092982918845276250263818911301829349969290592257).
-define(i2, 
<<255,255,255,255,0,0,0,0,1,164,1,0,253,91,66,172,
  250,39,94,246,247,39,198,204,183,130,98,214,172,
  88,18,12>>).

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

prime() -> ?q.

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

encode(0) -> <<0:256>>;
encode(1) ->
<<254,255,255,255,1,0,0,0,2,72,3,0,250,183,132,88,
  245,79,188,236,239,79,140,153,111,5,197,172,89,
  177,36,24>>;
encode(A) when ((A < ?q) and (A > -1)) ->
    mul(reverse_bytes(<<A:256>>),
        reverse_bytes(<<?r2:256>>)).

decode(C) ->
    X = mul(C, reverse_bytes(<<1:256>>)),
    <<Y:256>> = reverse_bytes(X),
    Y.
    %binary:decode_unsigned(X, little).
   

encode_extended(
  #extended_point{
    u = U, v = V, z = Z, t1 = T1, t2 = T2
   }) ->
    Ue = encode(U),
    Ve = encode(V),
    Ze = encode(Z),
    T1e = encode(T1),
    T2e = encode(T2),
    <<Ue/binary, Ve/binary, Ze/binary,
      T1e/binary, T2e/binary>>.

decode_extended(<<U2:256, V2:256, Z2:256,
      T12:256, T22:256>>) ->
    #extended_point{
                 u = decode(<<U2:256>>),
                 v = decode(<<V2:256>>),
                 z = decode(<<Z2:256>>),
                 t1 = decode(<<T12:256>>),
                 t2 = decode(<<T22:256>>)}.
encode_extended_niels(
  #extended_niels_point{
     v_plus_u = VPU,
     v_minus_u = VMU,
     t2d = T2D,
     z = Z}) ->
    VPUe = encode(VPU),
    VMUe = encode(VMU),
    T2De = encode(T2D),
    Ze = encode(Z),
    <<VPUe/binary, VMUe/binary, T2De/binary,
      Ze/binary>>.
decode_extended_niels(
  <<VPU:256, VMU:256, T2D:256, Z:256>>) ->
    #extended_niels_point
        {v_plus_u = decode(<<VPU:256>>),
         v_minus_u = decode(<<VMU:256>>),
         t2d = decode(<<T2D:256>>),
         z = decode(<<Z:256>>)}.

sqrt_C(S) ->
    <<X0:256>> = crypto:strong_rand_bytes(32),
    C = X0 rem prime(),
    EC = encode(C),
    if
        (C < 2) -> sqrt_C(S);
        true ->
        
            %C0 = basics:rlpow(C, basics:rlpow(2, S-1, P), P),
            %Power = decode(pow_(encode(2),
            %                   S-1)),
            Power = 2147483648,
            C0 = decode(pow_(EC, Power)),
            if
                C0 < 2 -> sqrt_C(S);
                true -> C0
            end
    end.
factors_of_two(0) -> 1=2;
factors_of_two(X) when ((X rem 2) == 0) ->
    1 + factors_of_two(X div 2);
factors_of_two(_) -> 0.
sqrt(A) ->    
    1=2,
    %currently does not work. use the jubjub version.
    %fpow(A, (?q + 1) div 4).%this strategy doesn't work, because ?q+1 is not divisible by 4.
    %using tonelli-shanks. page 12 algorithm 5. https://eprint.iacr.org/2012/685.pdf
    %?q - 1 has 2^32 as a factor.
    %?q - 1 = t*2^S.
    %S = 32,
    %T = 12208678567578594777604504606729831043093128246378069236549469339647,
    S = factors_of_two(prime() - 1),%s is an integer, everything else is fr encoded.
    %T = (P - 1) div basics:rlpow(2, S, P),
    N1 = neg(encode(1)),
    T = mul(N1, inv(pow_(encode(2), S))),
    true = (decode(T) rem 2) == 1,
    %P = (T * basics:rlpow(2, S, P)) + 1,
    N1 = mul(T, pow_(encode(2), S)),

    %everything before this line could be a pre-compute.

    C = sqrt_C(S),
    %Z = basics:rlpow(C, T, P),
    Z = pow_(encode(C), decode(T)),
    %io:fwrite({C, decode(T), decode(Z)}),
    %W = basics:rlpow(A, (T-1) div 2, P),
    W = pow_(A, (decode(T)-1) div 2),
    WW = mul(W, W),
    WWA = mul(WW, A),
    %WW = (W*W) rem P,
    %WWA = (WW*A) rem P,
    %A0 = basics:rlpow(WWA, basics:rlpow(2, S-1, P), P),
    %Power = decode(pow_(encode(2),
    %                   S-1)),
    Power = 2147483648,
    A0 = pow_(WWA, Power),
    Bool = (A0 == N1),
    if
        Bool ->
            no_sqrt;
        true ->
            V = S,
            %X = (A * W) rem P,
            X = mul(A, W),
            %B = (X * W) rem P,
            B = mul(X, W),
            sqrt2(A, V, X, B, W, Z)
    end.
sqrt_k(B, K) ->
    %C = basics:rlpow(B, basics:rlpow(2, K, P), P),
    C = pow_(B, decode(pow_(encode(2), K))),
    case decode(C) of
        1 -> K;
        _ -> sqrt_k(B, K+1)
    end.
sqrt2(A, V, X, B, W, Z) ->
    K = sqrt_k(B, 0),
    VK1 = V - K - 1,
    if
        (VK1 < 0) -> sqrt(A);
        true ->
    %W2 = basics:rlpow(Z, basics:rlpow(2, VK1, P), P),
    W2 = pow_(Z, decode(pow_(encode(2), VK1))),
    %Z2 = (W2 * W2) rem P,
    Z2 = mul(W2, W2),
    %B2 = (B * Z2) rem P,
    B2 = mul(B, Z2),
    %X2 = (X * W2) rem P,
    X2 = mul(X, W2),
    V2 = K,
            io:fwrite("VK1: "),
            io:fwrite(integer_to_list(VK1)),
            io:fwrite("\n"),
            io:fwrite("W2: "),
            io:fwrite(integer_to_list(decode(W2))),
            io:fwrite("\n"),
            io:fwrite("Z2: "),
            io:fwrite(integer_to_list(decode(Z2))),
            io:fwrite("\n"),
            io:fwrite("B: "),
            io:fwrite(integer_to_list(decode(B))),
            io:fwrite("\n"),
            io:fwrite("B2: "),
            io:fwrite(integer_to_list(decode(B2))),
            io:fwrite("\n"),
    case decode(B2) of
        1 -> X2;
        _ -> sqrt2(A, V2, X2, B2, W2, Z2)
    end
    end.
pow_(X, Y) when is_integer(Y) ->
    pow(X, reverse_bytes(<<Y:256>>)).
    
   
%these functions are defined in c. 
add(_, _) -> ok.
neg(_) -> ok.
sub(_, _) -> ok.
mul(_, _) -> ok.
square(_) -> ok.
inv(X) -> encode(ff:inverse(decode(X), ?q)).
pow(_, _) -> ok.
short_pow(_, _) -> ok.
e_double(_) -> ok.
e_add(_extended, _niels) -> ok.
e_mul(_, _) -> ok.%unused, accepts a 8 byte exponent as an integer.
e_mul1(_, _) -> 
    %input 2 is a 32 byte integer as a little endian binary.
    ok.
e_mul2(Fq, Fr) ->
    %the exponent is montgomery encoded.
    case fr:decode(Fr) of
        0 -> e_zero();
        R2 ->
            R3 = fr:reverse_bytes(<<R2:256>>),
            e_mul1(Fq, R3)
    end.
e_neg(<<U:256, VZ:512, T1:256, T2:256>>) ->
    %neg U and T1
    NU = neg(<<U:256>>),
    NT1 = neg(<<T1:256>>),
    <<NU/binary, VZ:512, NT1/binary, T2:256>>.

    

pis([], _) -> [];
pis([H|T], A) -> 
    X = mul(H, A),
    [X|pis(T, X)].
batch_inverse(Vs) ->
    [All|V2] = lists:reverse(pis(Vs, encode(1))),%[v16, v15, v14, v13, v12, v1]
    AllI = encode(ff:inverse(decode(All), ?q)),%i16
    VI = lists:map(
           fun(V) -> mul(AllI, V) end,
           V2), %[i6, i56, i46, i36, i26]
    V3 = lists:reverse(pis(lists:reverse(Vs), encode(1))),%[v16, v26, v36, v46, v56, v6]
    V4 = tl(V3)++[encode(1)],%[v26, v36, v46, v56, v6, 1]
    VI2 = [AllI|lists:reverse(VI)],%[i16, i26, i36, i46, i56, i6]
    lists:zipwith(fun(A, B) ->
                          mul(A, B)
                  end, V4, VI2).

e_simplify_batch(Es) ->
    Zs = lists:map(fun(<<_:512, Z:256, _:512>>) ->
                           <<Z:256>> end, Es),
    false = (decode(hd(Zs)) == 0),

    IZs = batch_inverse(Zs),
    lists:zipwith(fun(E, IZ) ->
                          simplify(E, IZ)
                  end, Es, IZs).
simplify(<<U:256, V:256, _/binary>>, IZ) ->
    U2 = mul(<<U:256>>, IZ),
    V2 = mul(<<V:256>>, IZ),
    <<U2/binary, V2/binary, (encode(1))/binary, 
      U2/binary, V2/binary>>.
extended2affine(E) ->
    [E2] = e_simplify_batch([E]),
    <<A:256, B:256, _/binary>> = E2,
    <<A:256, B:256>>.

to_affine_batch(L) ->
    L2 = e_simplify_batch(L),
    lists:map(fun(<<U:256, V:256, _/binary>>) ->
                      <<U:256, V:256>>
              end, L2).
    
    
        

eq(A, B) ->
    jubjub:eq(
      decode_extended(A), 
      decode_extended(B)).

e_zero() ->
    A = #extended_point
        {u = 0, v = 1, z = 1, t1 = 0, t2 = 0},
    encode_extended(A).

is_zero(
  <<U:256, V:256, Z:256, _:256, _:256>>
 ) ->
    (U == 0) and (V == Z);
is_zero(
  <<VPU:256, VMU:256, T2D:256, Z:256>>
) ->
    (VPU == VMU) and (VPU == Z).


extended2extended_niels([]) -> [];
extended2extended_niels([H|T]) -> 
    [extended2extended_niels(H)|
     extended2extended_niels(T)];
extended2extended_niels(
  A = <<U:256, V:256, Z:256, T1:256, T2:256>>
 ) ->
%    B = is_zero(A),
%    if
%        B -> 
%            <<(encode(1))/binary,
%              (encode(1))/binary,
%              (encode(0))/binary,
%              (encode(1))/binary>>;
%        true ->
            UV = mul(<<U:256>>, <<V:256>>),
            T3 = mul(<<T1:256>>, <<T2:256>>),
            VPU = add(<<U:256>>, <<V:256>>),
            VMU = sub(<<V:256>>, <<U:256>>),
            T2D = mul(T3, ?D2),
            <<VPU/binary, VMU/binary, 
              T2D/binary, Z:256>>.
%    end.

extended_niels2extended([]) -> [];
extended_niels2extended([H|T]) ->
    [extended_niels2extended(H)|
     extended_niels2extended(T)];
extended_niels2extended(
  N = <<VPU:256, VMU:256, T2D:256, Z:256>>
) ->
    e_add(e_zero(), N).
affine2extended(
  <<U:256, V:256>>) ->
    Z = encode(1),
    <<U:256, V:256, Z/binary, U:256, V:256>>.
    

-define(sub3(A, B),
    if
        B>A -> A + ?q - B;
        true -> A - B
    end).

ctest(_) ->
    ok.

gen_point() ->
    G = jubjub:affine2extended(
          jubjub:gen_point()),
    encode_extended(G).
gen_point(X) ->
    fq2:encode_extended(
      jubjub:affine2extended(
        jubjub:gen_point(X))).
    

points_list(Many) ->
    G = jubjub:affine2extended(
          jubjub:gen_point()),
    G1 = jubjub:multiply(4327409, G),
    points_list2(Many, G1).
points_list2(0, _) -> [];
points_list2(N, G) -> 
    E = encode_extended(G),
    [{G, E}|
     points_list2(
       N-1, jubjub:multiply(9320472034, G))].

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
    S = decode(sub(A, B)),
    S = ((A1 - B1) + ?q) rem ?q,
    success;
test(3) ->
    io:fwrite("encode decode test\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    %A1 = A0 rem ?q,
    A1 = 2,
    A = encode(A1),
    A1 = decode(A);
%A = inverse(inverse(A));
test(5) ->
    %testing addition.
    io:fwrite("addition test\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    %A0 = 5,
    %B0 = 7,
    A1 = A0 rem ?q,
    B1 = B0 rem ?q,
    A = encode(A1),
    B = encode(B1),
    
    S = decode(add(A, B)),
    S = (A1 + B1) rem ?q,
    success;

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
    S3 = (A1 * B1) rem ?q,
    S3 = decode(mul(A, B)),
    success;
test(8) ->
    io:fwrite("more accurate multiplication speed test.\n"),
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
    lists:foldl(fun(_, _) -> 0 end, 0, R2),
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
test(10) ->
    io:fwrite("square test\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    %A0 = 3,
    A = A0 rem ?q,
    S1 = decode(square(encode(A))),
    S2 = (A*A rem ?q),
    B = S1 == S2,
    {B, S1, S2};
test(11) ->
    io:fwrite("inverse test\n"),
    %fails.
    <<A0:256>> = crypto:strong_rand_bytes(32),
    A = A0 rem ?q,
    A1 = encode(A),
    IA = inv(A1),
    A1 = inv(IA),
    A = decode(A1),
   %A = decode(inv(inv(encode(A)))),
    %IA = decode(inv(encode(A))),
    {A, IA};
test(12) ->
    io:fwrite("inverse speed test\n"),
    Many = 1000,
    R = range(0, Many),
    R2 = lists:map(
           fun(_) -> 
                   <<N0:256>> = 
                       crypto:strong_rand_bytes(
                         32),
                   N0 rem ?q
           end, R),
    R3 = lists:map(
           fun(X) -> encode(X) end, R2),
    T1 = erlang:timestamp(),
    lists:map(fun(I) -> inv(I) end, R3),
    T2 = erlang:timestamp(),
    lists:map(fun(I) ->
                        basics:inverse(I, ?q)
                end, R2),
    T3 = erlang:timestamp(),
    {{c, timer:now_diff(T2, T1)/Many},
     {erl, timer:now_diff(T3, T2)/Many}};
test(13) ->
    io:fwrite("jubjub double test\n"),
    P0 = jubjub:affine2extended(
           jubjub:gen_point()),
    B = encode_extended(P0),
    P = decode_extended(e_double(B)),
    P = decode_extended(e_double(B)),
    P2 = jubjub:double(P0),
    P2b = decode_extended(
            extended_niels2extended(
              extended2extended_niels(
                encode_extended(P2)))),
    P2c = jubjub:extended_niels2extended(
            jubjub:extended2extended_niels(P2)),
    P0 = jubjub:extended_niels2extended(
            jubjub:extended2extended_niels(P0)),
    true = jubjub:is_on_curve(
             jubjub:extended2affine(P0)),
    true = jubjub:is_on_curve(
             jubjub:extended2affine(P2)),
    true = jubjub:eq(P, P2),
    true = jubjub:eq(P2, P2c),
    true = jubjub:eq(P2, P2b),
    success;
test(14) ->
    io:fwrite("jubjub double speed test\n"),
    Many = 10000,
    R = range(0, Many),
    R2 = points_list(Many),
    io:fwrite("made points\n"),
    T1 = erlang:timestamp(),
    lists:foldl(fun({P, _}, _) ->
                        jubjub:double(jubjub:double(jubjub:double(P)))
                end, 0, R2),
    T2 = erlang:timestamp(),
    lists:foldl(fun({_, P}, _) ->
                        e_double(e_double(e_double(P)))
                end, 0, R2),
    T3 = erlang:timestamp(),
    {{erl, timer:now_diff(T2, T1)/Many/3},
     {c, timer:now_diff(T3, T2)/Many/3}};
test(15) ->
    io:fwrite("jubjub add\n"),
    E0 = jubjub:affine2extended(
           jubjub:gen_point()),
    E = encode_extended(E0),
    E0 = decode_extended(E),
    N0 = jubjub:affine_niels2extended_niels(
           jubjub:affine2affine_niels(
             jubjub:gen_point())),
    N = encode_extended_niels(N0),
    E3 = jubjub:add(E0, N0),
    E2 = decode_extended(e_add(E, N)),
    E2 = decode_extended(e_add(E, N)),

    N2 = extended2extended_niels(e_add(E, N)),
    E4 = decode_extended(e_add(E, N2)),

    true = jubjub:eq(E2, E3),
    true = jubjub:is_on_curve(
             jubjub:extended2affine(E2)),
    true = jubjub:is_on_curve(
             jubjub:extended2affine(E3)),
    true = jubjub:is_on_curve(
             jubjub:extended2affine(E4)),
    success;
test(16) ->
    io:fwrite("jubjub add speed\n"),
    Many = 10000,
    R = range(0, Many),
    R2 = points_list(Many),
    N0 = jubjub:affine_niels2extended_niels(
           jubjub:affine2affine_niels(
             jubjub:gen_point())),
    N = encode_extended_niels(N0),
    T1 = erlang:timestamp(),
    lists:foldl(fun({P, _}, _) ->
                        jubjub:add(P, N0)
                end, 0, R2),
    T2 = erlang:timestamp(),
    lists:foldl(fun({_, P}, _) ->
                        e_add(P, N)
                end, 0, R2),
    T3 = erlang:timestamp(),
    {{erl, timer:now_diff(T2, T1)/Many},
     {c, timer:now_diff(T3, T2)/Many}};
test(17) ->
    io:fwrite("test pow\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    %A0 = 2,
    A = A0 rem ?q,
    <<B0:256>> = crypto:strong_rand_bytes(32),
    %B0 = 2,
    B = B0 rem ?q,
    AE = encode(A),
    New = decode(pow(AE, 
                     reverse_bytes(<<B:256>>))),
    AE = encode(A),
    Old = basics:rlpow(A, B, ?q),
    New = Old,
    success;
test(18) ->
    io:fwrite("test pow speed\n"),
    Many = 100,
    R = range(0, Many),
    R2 = lists:map(
           fun(_) ->
                   <<A0:256>> = crypto:strong_rand_bytes(32),
                   <<B0:256>> = crypto:strong_rand_bytes(32),
                   A = A0 rem ?q,
                   B = B0 rem ?q,
                   Ae = encode(A),
                   Be = reverse_bytes(<<B:256>>),
                   {A, B, Ae, Be}
           end, R),
    T1 = erlang:timestamp(),
    lists:foldl(fun({A, B, _, _}, _) ->
                        basics:rlpow(A, B, ?q)
                end, 0, R2),
    T2 = erlang:timestamp(),
    lists:foldl(fun({_, _, A, B}, _) ->
                        pow(A, B)
                end, 0, R2),
    T3 = erlang:timestamp(),
    {{erl, timer:now_diff(T2, T1)/Many},
     {c, timer:now_diff(T3, T2)/Many}};
test(19) ->
    io:fwrite("test short_pow\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    A = A0 rem ?q,
    <<B:16>> = crypto:strong_rand_bytes(2),
    C = decode(short_pow(encode(A), B)),
    D = basics:rlpow(A, B, ?q),
    C = D,
    %{A, B, C},
    success;
test(20) ->
    io:fwrite("test neg\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    A = A0 rem ?q,
    NA = ?q - A,
    NA = decode(neg(encode(A)));
test(21) ->
    io:fwrite("testing elliptic multiplication\n"),
    N0 = jubjub:affine_niels2extended_niels(
           jubjub:affine2affine_niels(
             jubjub:gen_point())),
    N = encode_extended_niels(N0),
    <<B:64>> = crypto:strong_rand_bytes(8),
    %B = 2,
    %B = B0 rem ?q,
    %Be = reverse_bytes(<<B:64>>),
    %size(e_mul(N, Be)).
    <<One:256>> = encode(1),
    Me =  e_mul(N, B),
    M = jubjub:multiply(B, N0),
    M2 = decode_extended(Me),
    %jubjub:eq(M, M2),
    true = jubjub:eq(M, M2),
    success;
test(22) ->
    io:fwrite("elliptic multiplication speed test \n\n"),
    Many = 1000,
    R = range(0, Many),
    R1 = points_list(Many),
    R2 = lists:map(
           fun({P, _}) ->
                   N0 = jubjub:extended2extended_niels(P),
                   N = encode_extended_niels(N0),
                   <<B:64>> = crypto:strong_rand_bytes(8),
                   {N0, N, B} end, R1),
    T1 = erlang:timestamp(),
    lists:foldl(fun({N0, _, B}, _) ->
                        jubjub:multiply(B, N0)
                end, 0, R2),
    T2 = erlang:timestamp(),
    lists:foldl(fun({_, N, B}, _) ->
                        e_mul(N, B)
                end, 0, R2),
    T3 = erlang:timestamp(),
    {{erl, timer:now_diff(T2, T1)/Many},
     {c, timer:now_diff(T3, T2)/Many}};
test(23) ->
    io:fwrite("testing long elliptic multiplication\n"),
    N0 = jubjub:affine_niels2extended_niels(
           jubjub:affine2affine_niels(
             jubjub:gen_point())),
    N = encode_extended_niels(N0),
    <<B:256>> = crypto:strong_rand_bytes(32),
    %B = 18446744073709551615,
    <<One:256>> = encode(1),
    Me =  e_mul1(N, reverse_bytes(<<B:256>>)),
    M = jubjub:multiply(B, N0),
    M2 = decode_extended(Me),
    true = jubjub:eq(M, M2),
    success;
test(24) ->
    G = gen_point(),
    GN = extended2extended_niels(G),
    G2 = extended_niels2extended(GN),
    true = eq(G, G2),
    success;
test(25) ->
    %check that both simplifies don't change the order.
    Gs = [gen_point(),
          gen_point(),
          gen_point()],
    G2s = lists:map(fun(X) -> e_double(X) end,
                    Gs),
    G2simp = e_simplify_batch(G2s),
    [true, true, true] = 
        lists:zipwith(fun(A, B) -> eq(A, B) end,
                  G2s, G2simp),

    E = secp256k1:make(),
    G = fun() ->
                secp256k1:to_jacob(
                  secp256k1:gen_point(E))
        end,
    Ps = [G(), G(), G()],
    Ps = secp256k1:simplify_Zs_batch(Ps),
    success;
test(26) ->
    io:fwrite("testing elliptic zero point\n"),
    Z0 = e_zero(),
    Z1 = e_double(Z0),
    Z2 = e_add(Z0, extended2extended_niels(Z1)),
    Z3 = extended_niels2extended(
           extended2extended_niels(Z2)),
    true = is_zero(Z0),
    true = is_zero(Z1),
    true = is_zero(Z2),
    true = is_zero(Z3),

    true = is_zero(e_mul2(fr:encode(0), extended2extended_niels(gen_point()))),
    
    


    success.
    
    

    

    
    


    




    

