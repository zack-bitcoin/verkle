-module(ed).

%using the c library c_ed.erl to build out the rest of ed25519

-export([
         inv/1, pow/2,
         sqrt/1, 
         gen_point/0,
         compress_point/1, decompress_point/1,
         affine2extended/1,
         extended2affine_batch/1,
         a_neg/1, e_neg/1, normalize/1, 
         a_eq/2, e_eq/2,
         encode/1, decode/1,
         test/1
        ]).

% 2^255 - 19
-define(q, 
        57896044618658097711785492504343953926634992332820282019728792003956564819949
       ).
-define(one, <<38:256/little>>).
-define(zero, <<0:256/little>>).
-define(affine_zero, <<0:256, ?one/binary>>).
-define(extended_zero, <<0:256, ?one/binary, ?one/binary, 0:256>>).
-define(D, 
<<20131754669644349956395353228418582963360511446355554149282842162308175096314:256/little>>
).
%2^(256*256) rem ?q in montgomery format
-define(r2, <<1444:256/little>>).

% 2^255
-define(max255, 57896044618658097711785492504343953926634992332820282019728792003956564819968).

%encode(X) ->
%    Y = ed25519:encode(X),
%    <<Y:256/little>>.
%decode(<<Y:256/little>>) ->
%    ed25519:decode(Y).

inv(X) -> encode(ff:inverse(decode(X), ?q)).
pow(X, Y) when is_integer(Y) ->
    c_ed:pow(X, <<Y:256/little>>).
mul(X, Y) ->
    c_ed:mul(X, Y).
sub(X, Y) ->
    c_ed:sub(X, Y).
add(X, Y) ->
    c_ed:add(X, Y).
neg(X) ->
    c_ed:neg(X).
sqrt(A) ->
    T = encode(2),
    V = pow(mul(T, A), (?q - 5) div 8),
    AV = mul(A, V),
    I = mul(mul(T, AV), V),
    R = mul(AV, sub(I, ?one)),
    {neg(R), R}.
is_on_curve(<<X0:256, Y0:256>>) ->
    X = <<X0:256>>,
    Y = <<Y0:256>>,
    XX = mul(X, X),
    YY = mul(Y, Y),
    XY = mul(XX, YY),
    sub(YY, XX) == add(?one, mul(?D, XY)).
compress_point(<<X0:256/little, Y0:256/little>>) ->
    %Y = decode(<<Y0:256>>),
    S = case not(is_positive(Y0)) of
            true -> 1;
            false -> 0
        end,
    <<S:1, X0:255>>.
decompress_point(<<S:1, P:255>>) ->
    true = P < ?q,
    UU = mul(<<P:256/little>>, <<P:256/little>>),
    DUU = mul(?D, UU),
    B = inv(sub(?one, DUU)),
    T = add(?one, UU),
    VV = mul(T, B),
    case sqrt(VV) of
        error ->
            %invalid point.
            io:fwrite("invalid, no square root\n"),
            error;
        {V1 = <<V1n:256>>, V2} ->
            S2 = is_positive(V1n),
            V = if
                    (S == S2) -> V1;
                    true -> V2
                end,
%            V = case S of
%                    0 -> V1;
%                    1 -> V2
%                end,
            Point = <<P:256/little, V/binary>>,
            Bool = is_on_curve(Point),
            if
                Bool -> Point;
                true -> 
                    %invalid point
                    io:fwrite("invalid, not on curve\n"),
                    error
            end
    end.
            
    
gen_point() ->
    <<X0:256>> = crypto:strong_rand_bytes(32),
    case decompress_point(<<X0:256>>) of
        error -> gen_point();
        P -> P
    end.
is_positive(Y) ->
    (Y band ?max255) == 0.

affine2extended(P = <<X0:256, Y0:256>>) ->
    B = a_eq(P, ?affine_zero),
    if
        B -> ?extended_zero;
        true ->
            T = mul(<<X0:256>>, <<Y0:256>>),
            <<X0:256, Y0:256, 
              ?one/binary, T/binary>>
    end.

pis([], _) -> [];
pis([H|T], A) -> 
    X = mul(H, A),
    [X|pis(T, X)].
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
    Zs = lists:map(fun(<<_:512, Z:256, _:256>>) ->
                           <<Z:256>>
                   end, L),
    Is = batch_inverse(Zs),
    lists:zipwith(
      fun(P, I) -> extended2affine(P, I) end,
      L, Is).
extended2affine(<<X:256, Y:256, _:512>>, I) ->
    X2 = mul(<<X:256>>, I),
    Y2 = mul(<<Y:256>>, I),
    <<X2/binary, Y2/binary>>.
e_neg(<<X:256, Y:256, Z:256, T:256>>) ->
    X2 = neg(<<X:256>>),
    T2 = neg(<<T:256>>),
    <<X2/binary, Y:256, Z:256, T2/binary>>.
a_neg(<<X:256, Y:256>>) ->
    X2 = neg(<<X:256>>),
    <<X2/binary, Y:256>>.

normalize(L) ->
    affine2extended(extended2affine_batch(L)).
e_eq(<<X1:256, Y1:256, Z1:256, _:256>>, 
     <<X2:256, Y2:256, Z2:256, _:256>>) ->
    (mul(<<X1:256>>, <<Z2:256>>) 
     == mul(<<X2:256>>, <<Z1:256>>)) 
        and (mul(<<Y1:256>>, <<Z2:256>>) 
             == mul(<<Y2:256>>, <<Z1:256>>)).
a_eq(<<X:512>>, <<X:512>>) ->
    true;
a_eq(<<_:512>>, <<_:512>>) ->
    false.

%encode(0) -> <<0:256>>;
%encode(1) -> <<38:256/little>>;
encode(A) -> mul(<<A:256/little>>, ?r2).
decode(C) ->
    X = mul(C, <<1:256/little>>),
    case X of
        error -> io:fwrite(C);
        _ -> ok
    end,
    <<Y:256/little>> = X,
    Y.

c2m(<<X:256/little, Y:256/little>>) ->
    {affine, X, Y};
c2m(<<X:256/little, Y:256/little, 
      Z:256/little, T:256/little>>) ->
    {extended, X, Y, Z, T}.

test(1) ->
    X = 55,
    Y = ed25519:encode(X),
    <<Y:256/little>> = encode(X),
    success;
test(2) ->
    L = [encode(5), encode(9), encode(11)],
    L = batch_inverse(batch_inverse(L)),
    success;
test(3) ->
    Affine = gen_point(),

    %check compression is the same between versions.
    Compressed = compress_point(Affine),
    Affine = decompress_point(Compressed),

    Maffine = ed25519:mdecode_point(Compressed),
    Compressed = ed25519:mencode_point(Maffine),

    Maffine = c2m(Affine),

    %check that converting to extended coordinates and back doesn't introduce any inconsistencies.
    
    Extended = affine2extended(Affine),
    [Affine] = extended2affine_batch([Extended]),
    MExtended = ed25519:maffine2extended(Maffine),
    [Maffine] = ed25519:mextended2affine_batch([MExtended]),

    %double both points, check equality

    Extended2 = c_ed:double(Extended),
    MExtended2 = ed25519:mextended_double(
                   MExtended),

    Affine2 = hd(extended2affine_batch(
                   [Extended2])),
    MAffine2 = hd(ed25519:mextended2affine_batch(
                    [MExtended2])),

    MAffine2 = c2m(Affine2),

    %add points, check equality

    Extended3 = c_ed:padd(Extended, Extended2),
    MExtended3 = ed25519:mextended_add(
                   MExtended2, MExtended),
    %io:fwrite({Extended, Extended2, Extended3}),

    Affine3 = hd(extended2affine_batch(
                   [Extended3])),
    MAffine3 = hd(ed25519:mextended2affine_batch(
                    [MExtended3])),
    MAffine3 = c2m(Affine3),

    success;
test(4) ->
    Affine = gen_point(),
    Extended = affine2extended(Affine),

    MAffine = c2m(Affine),
    MExtended = ed25519:maffine2extended(MAffine),

    Try = fun(F) ->
                  Extended2 = c_ed:pmul_long(
                                Extended, <<F:256/little>>),
                  MExtended2 = ed25519:mextended_mul(
                                 MExtended, F),

                  [Affine2] = extended2affine_batch([Extended2]),
                  [MAffine2] = ed25519:mextended2affine_batch(
                   [MExtended2]),
                  B = MAffine2 == c2m(Affine2),
                  if
                      not(B) ->
                          io:fwrite({c2m(Extended2),
                                     MExtended2});
                      true ->true
                  end
          end,
    true = Try(0),
    true = Try(1),
    true = Try(2),
    true = Try(3),
    true = Try(10000000),
    success.
    

