-module(fq).
-export([
         det_pow/2,
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
         affine2extended/1,
         to_affine_batch/1,
         hash_point/1,
         compress/1,
         decompress/1
        ]).
-on_load(init/0).
-record(extended_point, {u, v, z, t1, t2}).
-record(extended_niels_point, 
        {v_plus_u, v_minus_u, t2d, z}).

% -(121665/121666)
%37095705934669439343138083508754565189542113879843219016388785533085940283555
-define(D, 
<<250,233,71,223,254,139,237,128,115,41,198,175,
  119,135,161,16,144,134,24,188,7,146,147,229,38,
  197,159,114,90,43,130,44>>).

% 2 * D
%16295367250680780974490674513165176452449235426866156013048779062215315747161
-define(D2, 
<<244,211,143,190,253,23,219,1,231,82,140,95,239,
  14,67,33,32,13,49,120,15,36,39,203,77,138,63,
  229,180,86,4,89>>).

init() ->
    ok = erlang:load_nif("./ebin/fq", 0),
    setup(0),
    ok.


setup(_) ->
    %defined in C.
    ok.

%This is the finite field on top of BLS12-381
%jubjub is implemented on this curve.

%uses montgomery notation for faster modular multiplication.

%binaries store bytes in reverse order in comparison to normal erlang binaries. This way when we pass the binaries to C, the bytes are already in order to fit into bigger registers.

-define(q, 
        57896044618658097711785492504343953926634992332820282019728792003956564819949
       ).



%-define(i2, 28948022309329048855892746252171976963317496166410141009864396001978282409975).
-define(i2, <<19:256/little>>).
%<<255,255,255,255,0,0,0,0,1,164,1,0,253,91,66,172,
%  250,39,94,246,247,39,198,204,183,130,98,214,172,
%  88,18,12>>).

%2^256
-define(r, 115792089237316195423570985008687907853269984665640564039457584007913129639936).

%2^256 rem q
-define(r1, 38).

%r*r rem q
-define(r2, 1444).

%r*r*r rem q
-define(r3, 54872).

%1/r rem q
-define(ir, 10665060850805439052171011777115991512801182798151104582581619579676209308938).

-define(encode_one, <<38:256/little>>).
%<<254,255,255,255,1,0,0,0,2,72,3,0,250,183,132,88,
%  245,79,188,236,239,79,140,153,111,5,197,172,89,
%  177,36,24>>).

-define(encode_zero, <<0:256>>).

prime() -> ?q.

%todo. binary:encode_unsigned(X, little) is probably faster.
reverse_bytes(<<X:256>>) -> <<X:256/little>>.
%reverse_bytes(X) ->
%    reverse_bytes(X, <<>>).
%reverse_bytes(<<A, B/binary>>, R) ->
%    reverse_bytes(B, <<A, R/binary>>);
%reverse_bytes(<<>>, R) -> R.

encode(0) -> <<0:256>>;
encode(1) -> <<38:256/little>>;
encode(A) when ((A < ?q) and (A > -1)) ->
    mul(<<A:256/little>>,
        <<?r2:256/little>>).

decode(C) ->
    X = mul(C, (<<1:256/little>>)),
    <<Y:256/little>> = X,
    Y.
   

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

hash_point(<<U:256>>) ->
    fr:encode(U);
hash_point(<<U:256, _:256>>) ->
    fr:encode(U);
hash_point(X = <<U:(256*5)>>) ->
    hash_point(extended2affine(X)).

sqrt(A) ->
    %when prime mod 8 = 5
%https://www.rieselprime.de/ziki/Modular_square_root
    %v = (2*a) ^ ((p-5)/8)
    %i = 2*a*v*v
    %r = +-av(i-1)
    T = encode(2),
    V = pow_(mul(T, A), (?q - 5) div 8),
    AV = mul(A, V),
    I = mul(mul(T, AV), V),
    R = mul(AV, sub(I, ?encode_one)),
    %{neg(R), R, T, V, AV, I}.
    {neg(R), R}.
det_pow(_, 0) -> 1;
det_pow(X, 1) -> X;
det_pow(X, N) when ((N rem 2) == 0) and (N>0) -> 
    det_pow(X*X, N div 2);
det_pow(X, N) when (N > 0) -> X * det_pow(X, N-1).
            
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
            %R3 = fr:reverse_bytes(<<R2:256>>),
            e_mul1(Fq, <<R2:256/little>>)
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
    [All|V2] = lists:reverse(pis(Vs, ?encode_one)),%[v16, v15, v14, v13, v12, v1]
    %AllI = encode(ff:inverse(decode(All), ?q)),%i16
    AllI = inv(All),
    VI = lists:map(
           fun(V) -> mul(AllI, V) end,
           V2), %[i6, i56, i46, i36, i26]
    V3 = lists:reverse(pis(lists:reverse(Vs), ?encode_one)),%[v16, v26, v36, v46, v56, v6]
    V4 = tl(V3)++[?encode_one],%[v26, v36, v46, v56, v6, 1]
    VI2 = [AllI|lists:reverse(VI)],%[i16, i26, i36, i46, i56, i6]
    lists:zipwith(fun(A, B) ->
                          mul(A, B)
                  end, V4, VI2).

e_simplify_batch([]) -> [];
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
    <<U2/binary, V2/binary, (?encode_one)/binary, 
      U2/binary, V2/binary>>.
extended2affine(E) ->
    [E2] = e_simplify_batch([E]),
    <<A:256, B:256, _:(256*3)>> = E2,
    <<A:256, B:256>>.

to_affine_batch(L) ->
    L2 = e_simplify_batch(L),
    lists:map(fun(<<U:256, V:256, _:(256*3)>>) ->
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
    Z = ?encode_one,
    <<U:256, V:256, Z/binary, U:256, V:256>>.
    

-define(sub3(A, B),
    if
        B>A -> A + ?q - B;
        true -> A - B
    end).

ctest(_) ->
    ok.

gen_point() ->
    <<X0:256>> = crypto:strong_rand_bytes(32),
    X = X0 rem ?q,
    G = gen_point(encode(X), 2, 2),
    true = is_on_curve(G),
    G.
gen_point(U, 0, S) ->
    io:fwrite("next U\n"),
    gen_point(add(U, 1), S, S);
gen_point(Us, _, _) when is_list(Us) ->
    UUs = lists:map(fun(X) -> mul(X, X) end, Us),
    DUUs = lists:map(fun(X) -> sub(encode(1), 
                                   mul(?D, X))
                     end, UUs),
    Bs = batch_inverse(DUUs),
    VVs = lists:zipwith(
            fun(B, UU) ->
                    mul(add(encode(1), UU), B)
            end, Bs, UUs),
    lists:zipwith(
      fun(U, VV) ->
              gen_point(U, 20, 20, VV)
      end, Us, VVs);
gen_point(U, Tries, S) ->
    UU = mul(U, U),
    DUU = mul(?D, UU),
    B = inv(sub(encode(1), DUU)),
    T = add(encode(1), UU),
    VV = mul(T, B),
    gen_point(U, Tries, S, VV).
gen_point(U, _, S, VV) ->
    case sqrt(VV) of
        error ->
            gen_point(add(U, 1), S, S);
        {V1, V2} ->
            A = <<U/binary, V1/binary>>,
            A2 = <<U/binary, V2/binary>>,
            G = affine2extended(A),
            Prime = is_prime_order(G),
            %Prime = is_on_curve(A),
            io:fwrite(is_on_curve(A)),
            io:fwrite(is_on_curve(A2)),
            R = if
                not(Prime) -> A;
                true -> <<U/binary, V2/binary>>
            end,
            R
    end.
            

%    G = jubjub:affine2extended(
%          jubjub:gen_point()),
%    encode_extended(G).
gen_point(X) ->
    gen_point(X, 20, 20).
%    fq:encode_extended(
%      jubjub:affine2extended(
%        jubjub:gen_point(X))).

decompress_points(Us) 
  when is_list(Us) ->
    %UU = U*U,
    %DUU = 1 - (D * UU)
    %B = inverse(DUU)
    %VV = (UU+1) * B 
    %V = sqrt(VV)
    %V = sqrt((UU+1) / (1 - (D * UU)))
    UUs = lists:map(fun(X) -> mul(X, X) end, Us),
    DUUs = lists:map(
             fun(X) -> 
                     sub(?encode_one, mul(?D, X))
             end, UUs),
    Bs = batch_inverse(DUUs),
    VVs = lists:zipwith(
            fun(B, UU) -> 
                    mul(add(?encode_one, UU), B)
            end, Bs, UUs),
    lists:zipwith(
      fun(U, VV) ->
              decompress_point2(U, VV)
      end, Us, VVs).
decompress_point2(U, VV) ->
    %without prime_order 372. 
    %prime order 200.
    case sqrt(VV) of%0.000350
        error ->
            error;
        {V1, V2} ->
            A = <<U/binary, V1/binary>>,%affine
            A2 = <<U/binary, V2/binary>>,%affine
            G = affine2extended(A),
            B = is_on_curve(A),%this is the slow line. Is there no faster way to know? TODO.
            %B = is_prime_order(G),%this is the slow line. Is there no faster way to know? TODO.
            %OnCurve = is_on_curve(A), TODO
            if
                B -> A;
                true -> A2
            end
    end.
is_on_curve(<<U:256, V:256>>) ->
    U2 = mul(<<U:256>>, <<U:256>>),
    V2 = mul(<<V:256>>, <<V:256>>),
    UV2 = mul(U2, V2),
    (sub(V2, U2) == 
         add(?encode_one, mul(?D, UV2))).
is_prime_order(E) ->
    is_torsion_free(E) and not(identity(E)).
is_torsion_free(E) ->
    %S = 6554484396890773809930967563523245729705921265872317281365359162392183254199,
    %fr modulus.
    R = 7237005577332262213973186563042994240857116359379907606001950938285454250989,
    E2 = e_mul1(E, <<R:256/little>>),
    %eq(encode(0), E2).
    identity(E2).
identity(<<U:256, V:256, Z:256, Ts:512>>) ->
    (U == 0) and (V == Z).

compress(L) when is_list(L) ->
    L2 = to_affine_batch(L),
    lists:map(fun(<<A:256, _:256>>)->
                      <<A:256>> end, L2).
decompress(<<A:256>>) ->
    hd(decompress([<<A:256>>]));
%decompress(<<A:256>>) ->
%    gen_point(decode(<<A:256>>));
decompress(L) when is_list(L) ->
    L2 = decompress_points(L),
    lists:map(fun(X) -> affine2extended(X) end,
              L2).

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
                          (X >= Y) -> X - Y;
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
    %erl add
    lists:foldl(fun({X, Y}, _) ->
                      C = X+Y,
                      if
                          (C > ?q) -> C - ?q;
                          true -> C
                      end,
                        0
                end, 0, R),
    T6 = erlang:timestamp(),
    %c add
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
    %TODO
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
    true = is_zero(extended2extended_niels(Z0)),
    true = is_zero(extended2extended_niels(Z1)),
    true = is_zero(extended2extended_niels(Z2)),
    true = is_zero(extended2extended_niels(Z3)),
    
    true = is_zero(e_mul2(extended2extended_niels(gen_point()), fr:encode(0))),

    success;
test(27) ->
    io:fwrite("encode decode speed test\n"),
    Many = 100000,
    R = range(0, Many),
    R2 = lists:map(fun(X) -> encode(X) end, R),
    T1 = erlang:timestamp(),
    lists:foldl(fun(X, _) ->
                        encode(X),
                        0
                end, 0, R),
    T2 = erlang:timestamp(),
    lists:foldl(fun(X, _) ->
                        decode(X),
                        0
                end, 0, R2),
    T3 = erlang:timestamp(),
    {
      {encode, (timer:now_diff(T2, T1)/Many)},
      {decode, (timer:now_diff(T3, T2)/Many)}
    };
test(28) ->
    io:fwrite("testing e_add with niels/extended niels\n"),
    G = gen_point(),
    H = gen_point(),
    HE = extended2extended_niels(H),
    R1 = e_add(G, H),
    R2 = e_add(G, HE),
    eq(R1, R2);
test(29) ->
    io:fwrite("testing e_add error that returns a broken point.\n"),
    G = gen_point(),
    Z = e_zero(),
    Z1 = extended_niels2extended(
           extended2extended_niels(Z)),
    Bad = encode_extended(%this is the bad point.
           {extended_point, 0,0,1,0,0}),
    {
      decode_extended(Z1),
      decode_extended(e_mul2(G, fr:encode(0))),

      decode_extended(e_add(G, Bad)),
      decode_extended_niels(
        extended2extended_niels(Bad)),
      decode_extended(
        extended_niels2extended(
          extended2extended_niels(Bad))),
      decode_extended(e_add(G, extended2extended_niels(Bad)))
    };
test(30) ->
    io:fwrite("testing compressing a point to 32 bytes"),
    X = gen_point(),
    X2 = e_add(X, X),
    [<<A:256>>] = compress([X2]),
    X3 = decompress(<<A:256>>),
    Aff = extended2affine(X2),
    Aff = extended2affine(X3),
    ok;
test(31) ->
    %decompressing in batches.
    X = [gen_point(), gen_point()],
    C = compress(X),
    D = decompress(C),
    C = compress(D),
   
    D2 = decompress_points(C),
    D3 = lists:map(fun(X) ->
                           affine2extended(X) end,
                   D2),
    C = compress(D3),
    {D3, D};
test(32) ->
    %compression/decompression speed test.
    Many = 300,
    Range = range(0, Many),
    Points = lists:map(
               fun(X) -> 
                       e_double(e_double(gen_point())) end,
               Range),
    
    T1 = erlang:timestamp(),
    C = compress(Points),
    T2 = erlang:timestamp(),

    %{ok, _PID} = fprof:start(),
    %fprof:trace([start, {procs, all}]),

    decompress(C),

    %fprof:trace([stop]),
    %fprof:profile(),
    %fprof:analyse(),
    %fprof:stop(),

    T3 = erlang:timestamp(),
    {{compress, (timer:now_diff(T2, T1)/Many)},
     {decompress, (timer:now_diff(T3, T2)/Many)}}.
   
                               

    
    

    


