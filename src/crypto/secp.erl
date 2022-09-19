-module(secp).
-export([
         %finite field used to implement the curve.
         inv/1, pow/2, mul/2, square/1, sub/2, add/2,
         neg/1, sqrt/1, prime/0, 

         %elliptic curve operations
         is_on_curve/1,
         gen_point/0, gen_point/1,
         compress_point/1, decompress_point/1,
         decompress_points/1, compress_points/1,
         affine2extended/1,
         extended2affine_batch/1,
         a_neg/1, e_neg/1, normalize/1, 
         e_eq/2,
         e_add/2, e_mul/2, e_mul2/2,
         encode/1, decode/1,
         affine_zero/0, extended_zero/0,
         test/1
         
        ]).

-define(prime, 115792089237316195423570985008687907853269984665640564039457584007908834671663).
-define(prime_over_4, %28948022309329048855892746252171976963317496166410141009864396001977208667916).
<<12,255,255,191,255,255,255,255,255,255,255,255,
  255,255,255,255,255,255,255,255,255,255,255,255,
  255,255,255,255,255,255,255,63>>).

%2^(256+256) rem ?prime in montgomery format
-define(r2, <<18446752466076602529:256/little>>).

-define(zero, <<0:256>>).
-define(one, 
<<209,3,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0>>).

-define(extended_zero, <<0:256, (?one)/binary, 0:256>>).
-define(affine_zero, <<0:256, (?one)/binary>>).

extended_zero() ->
    ?extended_zero.
affine_zero() ->
    ?affine_zero.
prime() ->
    ?prime.

inv(X) -> encode(ff:inverse(decode(X), ?prime)).
pow(X, Y) when is_integer(Y) ->
    c_secp:pow(X, <<Y:256/little>>).
mul(X, Y) ->
    c_secp:mul(X, Y).
square(X) ->
    c_secp:square(X).
sub(X, Y) ->
    c_secp:sub(X, Y).
add(X, Y) ->
    c_secp:add(X, Y).
e_add(X = <<_:768>>, Y = <<_:768>>) ->
    c_secp:padd(X, Y);
e_add(X = <<_:512>>, Y) ->
    e_add(affine2extended(X), Y);
e_add(X, Y = <<_:512>>) ->
    e_add(X, affine2extended(Y)).
e_double(X = <<_:768>>) ->
    c_secp:double(X).
e_mul(X, Y = <<0:256>>) -> ?extended_zero;
e_mul(X = <<_:512>>, Y) ->
    e_mul(affine2extended(X), Y);
e_mul(X = <<_:768>>, Y = <<_:256>>) ->
    c_secp:pmul_long(X, Y).
e_mul2(X = <<_:768>>, Y = <<_:256>>) ->
    %Y is montgomery encoded.
    R = fr:decode(Y),
    e_mul(X, <<R:256/little>>).
neg(X) ->
    c_secp:neg(X).
sqrt(X) ->
    c_secp:pow(X, ?prime_over_4).
%    Y = ff:pow(fn:decode(X), 
%               (?prime + 1) div 4, ?prime),
%    fn:encode(Y).
is_on_curve(<<X0:256, Y0:256>>) ->
    X = <<X0:256>>,
    Y = <<Y0:256>>,
    B = fn:encode(7),
    X3 = mul(square(X), X),
    Y2 = square(Y),
    <<0:256>> == sub(add(X3, B), Y2).
    
compress_points(Es) ->
    As = extended2affine_batch(Es), 
    lists:map(fun(A) ->
                      compress_point(A)
              end, As).
is_positive(P = <<_:255, 1:1>>) ->
    false;
is_positive(P = <<_:255, 0:1>>) ->
    true.

compress_point(<<X0:256/little, Y0:256/little>>) ->
    %from 64 byte affine to 32 byte compressed
    %Y = decode(<<Y0:256>>),
    S = case is_positive(Y0) of
            true -> 2;
            false -> 3
        end,
    <<S, X0:256/little>>.
decompress_point(<<S, X0:256/little>>) ->
    XX = square(X),
    X3 = mul(X, XX),
    YY = add(fr:encode(7), X3),
    Y = sqrt(YY),
    B = is_positive(Y),
    Y2 = if
             B and (S==2) -> Y;
             B and (S==3) -> neg(Y);
             not(B) and (S==2) -> neg(Y);
             not(B) and (S==3) -> Y
         end,
    <<X0:256/little, Y2/binary>>.
decompress_points(L) when is_list(L) ->
    lists:map(fun(X) ->
                      decompress_point(X)
              end, L).
gen_point() ->
    <<X0:256>> = crypto:strong_rand_bytes(32),
    X = X0 rem ?prime,
    gen_point(<<X:256>>).
gen_point(<<X:256>>) ->
    P = decompress_point(<<2, X:256>>),
    B = is_on_curve(P),
    if
        B -> P;
        true -> gen_point(<<(X+1):256>>)
    end.
affine2extended(_) ->
    %should work for lists or elements.
    ok.
pis([H|T], A) -> 
    X = mul(H, A),
    [X|pis(T, X)].
batch_inverse([]) -> [];
batch_inverse(Vs) ->
    [All|V2] = lists:reverse(pis(Vs, ?one)),%[v16, v15, v14, v13, v12, v1]
    AllI = inv(All),
    VI = lists:map(
           fun(V) -> mul(AllI, V) end,
           V2), %[i6, i56, i46, i36, i26]
    V3 = lists:reverse(pis(lists:reverse(Vs), ?one)),%[v16, v26, v36, v46, v56, v6]
    V4 = tl(V3)++[?one],%[v26, v36, v46, v56, v6, 1]
    VI2 = [AllI|lists:reverse(VI)],%[i16, i26, i36, i46, i56, i6]
    lists:zipwith(fun(A, B) ->
                          mul(A, B)
                  end, V4, VI2).
extended2affine_batch(L) ->
    %batch_inverse
    ok.
extended2affine(<<X:256, Y:256, _:256>>, I) ->
    %X2 = mul(<<X:256>>, I),
    %Y2 = mul(<<Y:256>>, I),
    %<<X2/binary, Y2/binary>>.
    ok.
e_neg(P) ->
    <<(x(P))/binary, (neg(y(P)))/binary, 
      (z(P))/binary>>.
a_neg(<<X:256, Y:256>>) ->
    <<X:256, (neg(<<Y:256>>))/binary>>.
normalize(L) ->
    affine2extended(extended2affine_batch(L)).

is_extended_zero(P = <<_:768>>) ->
    %{0,1,0}
    %Check2 = (0 == Z1^3).
    e_eq(P, ?extended_zero).

x(<<X:256, _:512>>) -> <<X:256>>.
y(<<_:256, Y:256, _:256>>) -> <<Y:256>>.
z(<<_:512, Z:256>>) -> <<Z:256>>.

e_eq(P1, P2) ->
    Z1 = z(P1),
    Z2 = z(P2),
    ZZ = mul(Z1, Z1),
    ZZZ = mul(ZZ, Z1),
    ZZ2 = mul(Z2, Z2),
    ZZZ2 = mul(Z2, ZZ2),
    Check1 = (mul(x(P1), ZZ2) == mul(x(P2), ZZ)),
    Check2 = (mul(y(P1), ZZZ2) == mul(y(P2), ZZZ)),
    Check1 and Check2.

encode(0) -> ?zero;
encode(1) -> ?one;
encode(A) -> mul(<<A:256/little>>, ?r2).
decode(C = <<_:256>>) ->
    X = mul(C, <<1:256/little>>),
    <<Y:256/little>> = X,
    Y.

range(N, N) -> [N];
range(A, B) when (A < B) -> 
    [A|range(A+1, B)].

test(0) ->
    success.
