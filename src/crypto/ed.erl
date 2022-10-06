-module(ed).

%using the c library c_ed.erl to build out the rest of ed25519

-export([
         %finite field used to implement the curve.
         inv/1, pow/2, mul/2, square/2, sub/2, add/2,
         neg/1, sqrt/1, prime/0, 

         %elliptic curve operations
         is_on_curve/1,
         gen_point/0, gen_point/1,
         compress_point/1, decompress_point/1,
         decompress_points/1, compress_points/1,
         affine2extended/1,
         extended2affine_batch/1,
         a_neg/1, e_neg/1, normalize/1, 
         e_eq/2, a_eq/2,
         e_add/2, e_mul/2, e_mul2/2,
         encode/1, decode/1,
         affine_zero/0, extended_zero/0,
         affine_base/0,
         test/1
        ]).

-define(sanity, false).

% 2^255 - 19
-define(q, 
        57896044618658097711785492504343953926634992332820282019728792003956564819949
       ).
-define(one, <<38:256/little>>).
-define(zero, <<0:256/little>>).
-define(affine_zero, <<0:256, ?one/binary>>).
-define(extended_zero, <<0:256, ?one/binary, ?one/binary, 0:256>>).
-define(affine_base, 
<<135,162,157,63,85,188,202,226,137,228,150,35,86,152,165,
  156,183,181,228,173,107,147,121,152,208,119,96,126,112,
  35,158,117,74,51,51,51,51,51,51,51,51,51,51,51,51,51,51,
  51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51,51>>
).

% -(121665/121666)
-define(D, 37095705934669439343138083508754565189542113879843219016388785533085940283555).
%and in montgomery format.
-define(mD, 
<<20131754669644349956395353228418582963360511446355554149282842162308175096314:256/little>>
).

%2^(256*256) rem ?q in montgomery format
-define(r2, <<1444:256/little>>).

% 2^255
-define(max255, 1).
        %57896044618658097711785492504343953926634992332820282019728792003956564819968).% 2^255
%28948022309329048855892746252171976963317496166410141009864396001978282409984).%2^254

%// √(-1) aka √(a) aka 2^((p-1)/4)
-define(sqrt_m1, 19681161376707505956807079304988542015446066515923890162744021073123829784752).

%// 1-d²
-define(one_minus_d_sq,
  1159843021668779879193775521855586647937357759715417654439879720876111806838).

%// (d-1)²
-define(d_minus_one_sq,
  40440834346308536858101042469323190826248399146238708352240133220865137265952).

%// √(ad - 1)
-define(sqrt_ad_minus_one,
  25063068953384623474111414158702152701244531502492656460079210482610430750235).


%encode(X) ->
%    Y = ed25519:encode(X),
%    <<Y:256/little>>.
%decode(<<Y:256/little>>) ->
%    ed25519:decode(Y).

prime() -> ?q.
affine_zero() -> ?affine_zero.
extended_zero() -> ?extended_zero.
affine_base() -> ?affine_base.
inv(X) -> encode(ff:inverse(decode(X), ?q)).
pow(X, Y) when is_integer(Y) ->
    c_ed:pow(X, <<Y:256/little>>).
mul(X, Y) ->
    c_ed:mul(X, Y).
square(X, Y) ->
    c_ed:square(X, Y).
sub(X, Y) ->
    c_ed:sub(X, Y).
add(X, Y) ->
    c_ed:add(X, Y).
%e_add(X = <<0:256,_:768>>, Y = <<_:1024>>) ->
%    Y;
%e_add(X = <<_:1024>>, Y = <<0:256,_:768>>) ->
%    X;
e_add(X = <<_:1024>>, Y = <<_:1024>>) ->
    c_ed:padd(X, Y);
e_add(X = <<_:512>>, Y) ->
    e_add(affine2extended(X), Y);
e_add(X, Y = <<_:512>>) ->
    e_add(X, affine2extended(Y)).
e_mul(X, Y = <<0:256>>) -> ?extended_zero;
e_mul(X = <<_:512>>, Y) ->
    e_mul(affine2extended(X), Y);
%e_mul(X = <<0:256,_:768>>, Y = <<_:256>>) ->
    %zero to the power of anything.
%    extended_zero();
e_mul(X = <<_:1024>>, Y = <<_:256>>) ->
%    B = e_eq(X, ?extended_zero),
%    if
%        B -> ?extended_zero;
%        true ->
    <<Xp:256, Yp:256, Zp:256, _:256>> = X,
    if
        (Xp == 0) and (Yp == Zp) ->
            extended_zero();
        true ->
            c_ed:pmul_long(X, Y)
    end.
%    end.
%e_mul2(X = <<_:256>>, Y) ->
%    e_mul2(decompress_point(X), Y);
e_mul2(X = <<_:512>>, Y) ->
    e_mul2(affine2extended(X), Y);
%e_mul2(X = <<0:256,_:768>>, Y = <<_:256>>) ->
    %zero to the power of anything.
%    extended_zero();
e_mul2(X = <<_:1024>>, Y = <<_:256>>) ->
    %Y is montgomery encoded.
    R = fr:decode(Y),
    e_mul(X, <<R:256/little>>).
    %case fr:decode(Y) of
    %    0 -> extended_zero();
    %    R -> e_mul(X, <<R:256/little>>)
    %end.

   

neg(X) ->
    c_ed:neg(X).
sqrt(A) ->
    % v = (2 * a) ^ ((m - 5)/8) mod m
    % i = 2 * a * v^2  mod m    (aka sqrt(-1))
    % r = +- a * v * (i - 1) mod m

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
    sub(YY, XX) == add(?one, mul(?mD, XY)).
compress_points(Es) -> %<<P:1024/little>>) ->
    %from list of 128 byte extended to list of 32-byte compressed.
    As = extended2affine_batch(Es), 
    lists:map(fun(A) ->
                      compress_point(A)
              end, As).
compress_point(error) -> error;
compress_point(P = <<_:1024>>) ->
    [A] = extended2affine_batch([P]),
    compress_point(A);
compress_point(<<X0:256/little, Y0:256/little>>) ->
    %from 64 byte affine to 32 byte compressed
    %Y = decode(<<Y0:256>>),
    S = case is_positive(<<Y0:256/little>>) of
            true -> 
                %io:fwrite("compress positive\n"),
                0;
            false -> 
                %io:fwrite("compress negative\n"),
                1
        end,
    <<S:1, X0:255>>.
decompress_points(L) when is_list(L) ->
    L2 = lists:map(fun(<<S:1, P:255>>) ->
                      true = P < ?q,
                      U = <<P:256/little>>,
                      UU = mul(U, U),
                      DUU = sub(?one, mul(?mD, UU)),
                      T = add(?one, UU),
                      {DUU, U, S, T}
                   end, L),
    DUUs = lists:map(fun({DUU, U, S, T}) -> 
                             DUU end, 
                  L2),
    IDUUs = batch_inverse(DUUs),
    lists:zipwith(
      fun(B, {_, U, S, T}) ->
              decompress_point2(U, S, T, B)
      end, IDUUs, L2).
decompress_point(Start = <<S:1, P:255>>) ->
    if
        (P < ?q) ->
            U = <<P:256/little>>,
            UU = mul(U, U),
            DUU = sub(?one, mul(?mD, UU)),
            T = add(?one, UU),
            B = inv(DUU),
            decompress_point2(U, S, T, B);
        true -> error
    end.
decompress_point2(<<0:256>>, _S, _T, _B) ->
    ?affine_zero;
decompress_point2(U, S, T, B) ->
    VV = mul(T, B),
    case sqrt(VV) of
        error ->
            io:fwrite("invalid, no square root\n"),
            error;
        {<<0:256>>, <<0:256>>} ->
            io:fwrite("couldn't sqrt\m"),
            error;
        {V1 = <<V1n:256/little>>, V2} ->
            SB = (S == 0),
            S2 = is_positive(V1),
            V = if
                    (SB == S2) -> V1;
                    true -> V2
                end,
            Point = <<U/binary, V/binary>>,
            Bool = is_on_curve(Point),

            <<VN:256/little>> = V,
            SB = ((VN rem 2) == 0),
            if
                Bool -> 
                    if
                        ?sanity ->
                            V1 = neg(V2),
                            V2 = neg(V1),
                            true = (not(S2)) == 
                                is_positive(V2),
                            ok;
                        true -> ok
                    end,
                    Point;
                true -> 
                    %io:fwrite("invalid, not on curve\n"),
                    error
            end
    end.
           
gen_point() ->
    <<X:256>> = crypto:strong_rand_bytes(32),
    gen_point(<<X:256>>).
gen_point(<<X:256>>) ->
    %accepts 32 random bytes.
    %returns point in affine format.
    P = decompress_point(<<X:256>>),
    case P of
        error -> 
            io:fwrite("gen point next\n"),
            gen_point(<<(X+1):256>>);
        _ -> 
            %P = decompress_point(compress_point(P)),
            %P = hd(extended2affine_batch([affine2extended(P)])),
            %e_mul(P, <<8:256/little>>)
            P
    end.
is_positive(<<Y:256/little>>) ->
    (Y band ?max255) == 0.

affine2extended(P = <<_:1024>>) -> P;%already in extended format.
affine2extended(P = <<_:256>>) ->
    io:fwrite("compressed to extended instead \n"),
    affine2extended(decompress_point(P));
affine2extended(P = <<X0:256, Y0:256>>) ->
%    B = a_eq(P, ?affine_zero),
%    if
%        B -> ?extended_zero;
%        true ->
    T = mul(<<X0:256>>, <<Y0:256>>),
    <<X0:256, Y0:256, 
      ?one/binary, T/binary>>;
%    end;
affine2extended([]) -> [];
affine2extended([H|T]) ->
    [affine2extended(H)|
     affine2extended(T)];
affine2extended(error) -> 1=2;
affine2extended(X) -> io:fwrite({X, size(X)}).
                      



pis([], _) -> [];
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
    Zs = lists:map(fun(<<X:256, Y:256, Z:256, T:256>>) ->
                           if
                               (Z == 0) ->
                                   io:fwrite({X, Y, Z, T});
                               true -> ok
                           end,
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

%0,1,1,0
is_extended_zero(<<0:256, Y:256, Y:256, _:256>>) ->
    true;
is_extended_zero(<<_:1024>>) -> false.
         
    
e_eq(P1, P2) ->
    TZ = e_add(P1, e_neg(P2)),
    TZ2 = e_mul(TZ, <<8:256/little>>),
    is_extended_zero(TZ2).
    %e_eq2(extended_zero(), TZ2).
e_eq2(<<X1:256, Y1:256, Z1:256, _:256>>, 
     <<X2:256, Y2:256, Z2:256, _:256>>) ->
    (mul(<<X1:256>>, <<Z2:256>>) 
     == mul(<<X2:256>>, <<Z1:256>>)) 
        and (mul(<<Y1:256>>, <<Z2:256>>) 
             == mul(<<Y2:256>>, <<Z1:256>>)).
a_eq(A, B) ->
    [C, D] = affine2extended([A, B]),
    e_eq(C, D).
%a_eq(<<X:512>>, <<X:512>>) ->
%    true;
%a_eq(<<_:512>>, <<_:512>>) ->
%    false.

%encode(0) -> <<0:256>>;
%encode(1) -> <<38:256/little>>;
encode([]) -> [];
encode([H|T]) -> [encode(H)|encode(T)];
encode(A) -> mul(<<A:256/little>>, ?r2).
decode(C = <<_:256>>) ->
    X = mul(C, <<1:256/little>>),
    <<Y:256/little>> = X,
    Y.

% X * 2^Power.
pow2(X, 0) -> X;
pow2(X, Power) ->
    X2 = X*X rem ?q,
    pow2(X2, Power-1).

pow_2_252_3(X) ->
    %263 multiplications.
    X2 = X*X rem ?q,
    B2 = X2*X rem ?q,% X^3
    B4 = pow2(B2, 2) * B2 rem ?q,% x^15
    B5 = pow2(B4, 1) * X rem ?q,% x^31
    B10 = pow2(B5, 5) * B5 rem ?q,% 
    B20 = pow2(B10, 10) * B10 rem ?q,% 
    B40 = pow2(B20, 20) * B20 rem ?q,% 45
    B80 = pow2(B40, 40) * B40 rem ?q,% 86
    B160 = pow2(B80, 80) * B80 rem ?q,% 167
    B240 = pow2(B160, 80) * B80 rem ?q,% 248
    B250 = pow2(B240, 10) * B10 rem ?q,% 259
    Pow_p_5_8 = pow2(B250, 2) * X rem ?q,% 263
    % ^ To pow to (p+3)/8, multiply it by x.
    {Pow_p_5_8, B2}.

%// Little-endian check for first LE bit (last BE bit);
edIsNegative(N) ->
%  return (mod(num) & _1n) === _1n;
    N2 = N rem ?q,
    (N2 rem 2 == 1).

uvRatio(U, V) ->
    %274 multiplications
    %combines inversion with sqrt.
    V3 = (V*V*V) rem ?q,
    V7 = (V3 * V3 * V) rem ?q,
    {Pow, _} = pow_2_252_3(U * V7),
    X = U*V3*Pow rem ?q,% (uv^3)(uv^7)^(p-5)/8
    VX2 = V*X*X rem ?q,
    Root = X, %first root candidate.
    Root2 = X * ?sqrt_m1 rem ?q,%second root candidate.
    UseRoot1 = (VX2 == U), %if true, it is a square root.
    UseRoot2 = (VX2 == ((?q - U) rem ?q)), %if true, set x = x* 2^((p-1)/4)
    NoRoot = (VX2 == (((?q - U) * ?sqrt_m1) rem ?q)), %there is no vaid root. vxx = -u*sqrt(-1)
    X2 = if
             UseRoot1 -> Root;
             (UseRoot2 or NoRoot) -> Root2;%return root2 anyway, for constant-time.
             true ->
                 io:fwrite("unexepcted\n"),
                 X
         end,
    B = edIsNegative(X2),
    X3 = if
             B -> (?q - X2) rem ?q;
             true -> X2
         end,
    {{isValid, UseRoot1 or UseRoot2},
     {value, X3}}.

calcElligatorRistrettoMap(
  R0) when is_integer(R0) and R0 > 0->
    %293 multiplications

    R = (?sqrt_m1 * R0 * R0) rem ?q,
    Ns = ((R + 1) * ?one_minus_d_sq) rem ?q,
    %c is -1
    D = (-1 - (?D*R)) * ((R + ?D) rem ?q) rem ?q,
    {{isValid, Ns_D_is_sq}, {value, S}} = 
        uvRatio(Ns, D),
    S_ = S * R0 rem ?q,
    B = edIsNegative(S_),
    S_2 = if
              B -> S_;
              true -> (?q - S_) rem ?q
          end,
    {S2, C2} = 
        if
            Ns_D_is_sq -> {S, -1};
            true ->{S_, R}
        end,
    Nt = (C2 * (R - 1) * ?d_minus_one_sq - D) rem ?q,
    S4 = S2 * S2,
    W0 = ((S2 + S2) * D) rem ?q,
    W1 = Nt * ?sqrt_ad_minus_one rem ?q,
    W2 = (1 - S4 + ?q) rem ?q,
    W3 = (1 + S4) rem ?q,
    P1 = W0 * W3 rem ?q,
    P2 = W2 * W1 rem ?q,
    P3 = W1 * W3 rem ?q,
    P4 = W0 * W2 rem ?q,
    
    B1 = encode(P1),
    [B1, B2, B3, B4] = encode([P1, P2, P3, P4]),
    <<B1/binary, B2/binary, B3/binary, B4/binary>>.
    

%2 montgomery
c2m(<<X:256/little, Y:256/little>>) ->
    {affine, X, Y};
c2m(<<X:256/little, Y:256/little, 
      Z:256/little, T:256/little>>) ->
    {extended, X, Y, Z, T}.

range(N, N) -> [N];
range(A, B) when (A < B) -> 
    [A|range(A+1, B)].
test(0) ->
    %printing a basis point.
    {G, H, Q} = ipa:basis(256),
    P = hd(G),
    C = compress_point(P),
    P1 = hd(tl(G)),
    C1 = compress_point(P1),
    [base64:encode(C), base64:encode(C1)];
test(1) ->
    %encode decode test
    X = 55,
    Y = ed25519:encode(X),
    <<Y:256/little>> = encode(X),
    success;
test(2) ->
    %inverse test.
    L = [encode(5), encode(9), encode(11)],
    L = batch_inverse(batch_inverse(L)),
    success;
test(3) ->
    Affine = gen_point(),

    %check compression is the same between versions.
    Compressed = compress_point(Affine),
    <<S:1, _:255>> = Compressed,
    Affine = decompress_point(Compressed),

    Maffine = ed25519:mdecode_point(Compressed),
    Maffine2 = c2m(Affine),
    %io:fwrite({S, {c, Maffine}, {erl, Maffine2}}),
    
    Maffine = Maffine2,
    Compressed = ed25519:mencode_point(Maffine),


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
    %checking multiplication is the same
    Affine = gen_point(),
    Extended = affine2extended(Affine),

    %doubling is the same as adding to itself.
    Extended_t_2 = c_ed:double(Extended),
    Extended_t_2b = e_add(Extended, Extended),
    true = e_eq(Extended_t_2, Extended_t_2b),
   
    %adding is commutative
    Extended_t_3 = e_add(Extended, Extended_t_2),
    Extended_t_3b = e_add(Extended_t_2, Extended),
    true = e_eq(Extended_t_3, Extended_t_3b),

    %multiplication is repeated addition
    Extended_t_3c = 
        e_mul(Extended, <<3:256/little>>),
    true = e_eq(Extended_t_3, Extended_t_3c),
    

    MAffine = c2m(Affine),
    MExtended = ed25519:maffine2extended(MAffine),

    %doubling is the same as adding to itself.
    MExtended_t_2 = ed25519:mextended_double(
                      MExtended),
    MExtended_t_2b = ed25519:mextended_add(
                       MExtended, MExtended),
    true = ed25519:meq(MExtended_t_2, MExtended_t_2b),
    
    %adding is commutative
    MExtended_t_3 = ed25519:mextended_add(
                      MExtended, MExtended_t_2),
    MExtended_t_3b = ed25519:mextended_add(
                       MExtended_t_2, MExtended),
    true = ed25519:meq(MExtended_t_3, MExtended_t_3b),

    %multiplication is repeated addition
    MExtended_t_3c = 
       ed25519:mextended_mul(MExtended, 3),
    true = ed25519:meq(MExtended_t_3, MExtended_t_3c),



    Try = fun(F) ->
                  Extended2 = 
                      e_mul(Extended, 
                            <<F:256/little>>),
                  MExtended2 = ed25519:mextended_mul(
                                 MExtended, F),

                  [Affine2] = 
                      extended2affine_batch(
                        [Extended2]),
                  [MAffine2] = 
                      ed25519:mextended2affine_batch(
                        [MExtended2]),
                  B = MAffine2 == c2m(Affine2),
                  if
                      not(B) ->
                          io:fwrite({%MAffine2,
                                     %c2m(Affine2),
                                     c2m(Extended2),
                                     MExtended2});
                      true ->true
                  end
          end,
    true = Try(0),
    true = Try(1),
    true = Try(2),
    true = Try(4),
    true = Try(8),
    true = Try(3),%here
    true = Try(10000000),
    success;
test(5) ->
    %batch decompression of points.
    R = range(1, 20),
    Cs = lists:map(fun(_) ->
                           compress_point(
                             gen_point())
                   end, R),
    Ps = decompress_points(Cs),
    Cs = lists:map(fun(P) ->
                           compress_point(P)
                   end, Ps),
    success;
test(6) ->
    %multiplication speed test
    Many = 1000,
    R = range(0, Many),
    Ps = lists:map(
           fun(_) ->
                   <<X:256>> = crypto:strong_rand_bytes(32),
                   X2 = X rem ?q,
                   {affine2extended(gen_point()), 
                    <<X2:256/little>>}
              end, R),
    T1 = erlang:timestamp(),
    lists:foldl(fun({P, R}, _) ->
                        e_mul(P, R)
                end, 0, Ps),
    T2 = erlang:timestamp(),
    {{c, timer:now_diff(T2, T1)/Many}};
test(7) ->
    %multiply test
    P = gen_point(),
    R = e_mul(affine2extended(P), <<1:256/little>>),

    P2 = e_add(P, P),
    P3 = e_add(P, P2),
    P3b = e_add(P2, P),
    true = e_eq(P3, P3b),
    P4 = e_add(P2, P2),
    P4b = e_add(P, P3),
    true = e_eq(P4, P4b),
    P5 = e_add(P3, P2),
    P5b = e_add(P, P4),
    P5c = e_add(P4, P),
    P5d = e_add(P3b, P2),
    P5e = e_add(P4b, P),
    true = e_eq(P5, P5b),
    true = e_eq(P5, P5c),
    true = e_eq(P5, P5d),
    true = e_eq(P5, P5e),

    {P, R},
    success;
test(8) ->
    %add zero test
    G = gen_point(),
    %compression is reversible for normal points.
    G = decompress_point(compress_point(G)),
    E = affine2extended(G),
    E2 = affine2extended(gen_point()),
    E3 = e_add(extended_zero(), E),
    E4 = e_mul2(extended_zero(), fr:encode(3)),

    P0 = affine2extended(gen_point()),
    P = e_mul(P0, <<29394:256/little>>),
    Z = extended_zero(),
    Zb = extended_zero(),

    %compression is not reversible for zero points.
    AZ = affine_zero(),
    AZb = decompress_point(compress_point(AZ)),
    %true = (AZ == AZb),

    Gi = ed25519:faffine2extended(
           ed25519:fgen_point()),
    Zi = {extended, 0,1,1,0},
    Zi2 = ed25519:fextended_double(Zi),
    P2i = ed25519:fextended_add(Gi, Zi2),

    Gm = ed25519:maffine2extended(
           ed25519:mgen_point()),
    Zm = {extended, 0, 38, 38, 0},
    Zm2 = ed25519:mextended_double(Zm),
    P2m = ed25519:mextended_add(Gm, Zm2),

    Z2 = e_add(Z, Z),
    Z3 = c_ed:double(Z),
    Z2 = c_ed:padd(Z, Z),
    Z2 = c_ed:padd(Z, Z2),
    Z2 = c_ed:padd(Z2, Z2),
    true = is_extended_zero(Z),
    true = is_extended_zero(Z2),
    [AZ2, AZ2] = extended2affine_batch([Z, Z]),
    true = is_on_curve(AZ2),
    AZ2b = decompress_point(compress_point(AZ2)),
    P2 = e_add(P, Z2),
    P3 = e_add(Z2, P),
    P4 = e_add(Z, P),
    P5 = e_add(P, Z),
    P6 = e_add(e_add(P, E), e_neg(E)),
    P7 = e_add(P, e_add(E, e_add(E2, e_add(e_neg(E), e_neg(E2))))),
    %P8 = e_add(e_add(P, E3), e_neg(E3)),
    P9 = e_add(e_add(P, Z), e_neg(Z)),
    P8 = e_add(e_add(P, Z), Z),

    <<Z2x:256, Z2y:256, Z2z:256, Z2t:256>> = e_neg(Z),

    

    if
        false ->
            {
          Z, e_neg(Z),
          {decode(<<Z2x:256>>),
          decode(<<Z2y:256>>),
          decode(<<Z2z:256>>),
          decode(<<Z2t:256>>)},
          P, P2,
          %Zi, Zi2,
          %Z2,
          ed25519:feq(Gi, P2i),
          ed25519:meq(Gm, P2m),
          %e_eq(Z, Z2), 
          e_eq(P, P2), 
          e_eq(P, P3),
          e_eq(P2, P3),
          e_eq(P, P4),
          e_eq(P, P5),
          e_eq(P, P6),
          e_eq(P, P7),
          {eight, e_eq(P, P8)},
          {nine, e_eq(P, P9)}
         };
        true ->
    %<<_:512, PZ:256, _:256>>,
    %io:fwrite({P2}),
            true = e_eq(P, P2),
            true = e_eq(P, P3),
            true = e_eq(P, P4),
            true = e_eq(P, P5),
            true = e_eq(P, P6),
            true = e_eq(P, P7),
            true = e_eq(P, P8),
            true = e_eq(P, P9),

            true = e_eq(extended_zero(),
                        e_add(P, e_neg(P))),

            success
    end;
test(9) ->
    %using addition to double a point test.
    P1 = <<185,242,223,138,53,21,37,141,21,83,123,0,96,62,
           119,105,86,100,243,119,237,190,212,227,132,244,
           203,14,195,236,112,95,7,55,148,39,44,100,229,76,
           101,87,123,149,65,239,33,172,192,152,33,229,32,98,
           87,42,35,110,112,103,92,35,50,30,33,6,3,175,211,
           113,228,255,237,58,193,229,128,136,116,8,167,103,
           245,17,34,19,114,166,158,183,238,219,193,98,92,80,
           73,102,131,178,8,86,173,34,65,38,107,192,93,99,
           200,218,75,110,235,115,115,250,31,2,141,140,121,
           143,19,45,211,114>>,
    P2 = <<216,139,172,250,203,36,115,179,198,8,222,191,60,
           231,26,238,81,204,217,165,124,40,142,215,16,76,
           252,40,221,22,73,108,76,167,184,225,112,138,155,
           105,165,194,167,95,228,196,244,233,50,105,69,202,
           176,90,20,123,134,32,248,215,135,110,227,5,38,0,
           0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
           0,0,0,0,0,0,115,62,63,20,139,227,6,128,68,177,
           143,198,223,221,226,61,22,166,130,123,55,123,99,
           86,24,82,4,137,79,231,232,11>>,
    P3 = affine2extended(gen_point()),
    P4 = affine2extended(gen_point()),
    P5 = e_add(P3, P4),
    P6 = e_add(P1, P2),
    P7 = e_add(P1, e_neg(P1)),
    Z = extended_zero(),
    P8 = e_add(P1, e_add(P1, Z)),
    P9 = e_add(P1, P1),
    %{P7, P6, P5, P8, P9}.
    success;
test(10) ->
    %testing that multiplying by zero works correctly.
    <<B0:256>> = crypto:strong_rand_bytes(32),
    B = B0 rem ?q,
    G = gen_point(),
    Z0 = e_mul2(G, fr:encode(0)),
    Z1 = extended_zero(),
    Z2 = e_mul(extended_zero(), fr:encode(B)),
    true = ed:e_eq(Z0, Z1),
    true = ed:e_eq(Z2, Z1),
    Big = 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,
    false = ed:e_eq(Z1, e_mul2(G, fr:encode(basics:rlpow(2, 1, Big)))),
    false = ed:e_eq(Z1, e_mul2(G, fr:encode(basics:rlpow(2, 2, Big)))),
    false = ed:e_eq(Z1, e_mul2(G, fr:encode(basics:rlpow(2, 4, Big)))),
    false = ed:e_eq(Z1, e_mul2(G, fr:encode(basics:rlpow(2, 7, Big)))),
    false = ed:e_eq(Z1, e_mul2(G, fr:encode(basics:rlpow(2, 8, Big)))),
    false = ed:e_eq(Z1, e_mul2(G, fr:encode(basics:rlpow(2, 66, Big)))),
    false = ed:e_eq(Z1, e_mul2(G, fr:encode(basics:rlpow(2, 127, Big)))),
    false = ed:e_eq(Z1, e_mul2(G, fr:encode(basics:rlpow(2, 128, Big)))),
    false = ed:e_eq(Z1, e_mul2(G, fr:encode(basics:rlpow(2, 255, Big)))),

    true = e_eq(Z1, e_mul2(G, fr:encode(fr:prime()))),
    true = e_eq(Z1, e_add(G, e_mul2(G, fr:encode(fr:prime()-1)))),

    success;
test(11) ->
    G = affine2extended(gen_point()),
    %G = base_point(),
    %G2 = e_mul(G, <<2:256/little>>),
    %G2b = c_ed:double(G),
    %true = e_eq(G2, G2b),
    Z = extended_zero(),
    P = fr:prime(),
    %true = e_eq(Z, e_add(e_neg(G), e_mul2(G, fr:encode(P+1)))),
    %true = e_eq(Z, e_add(e_neg(G), G)),
    %true = e_eq(Z, e_add(e_neg(G), G)),
    io:fwrite("neg add\n"),
    %true = e_eq(Z, e_add(e_neg(G), e_mul(G, <<(P+1):256/little>>))),
    io:fwrite("just circle\n"),
    NG = e_mul(G, <<(P+1):256/little>>),
    Z2 = e_add(NG, e_neg(G)),
    Z2b = e_mul(Z2, <<8:256/little>>),
    true = e_eq(Z, Z2b),
    %io:fwrite({G}),
%    true = e_eq(Z, e_add(G, e_mul2(G, fr:encode(P-1)))),

    success;
test(12) ->
    WorkingPoint = 
<<48,224,74,190,145,127,2,130,46,94,157,8,11,203,
  61,171,78,222,166,110,128,11,103,246,223,105,
  255,72,254,34,15,95,15,117,9,24,22,166,155,225,
  193,196,170,17,75,191,228,96,182,26,113,125,197,
  244,91,59,14,202,207,188,83,251,50,60,38,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,224,207,0,7,228,116,91,73,153,117,107,
  141,84,199,52,80,177,189,121,70,11,211,198,49,
  200,110,183,84,41,16,127,75>>,
    BrokenPoint = 
<<223,241,198,92,127,189,75,7,1,58,95,114,167,153,
  21,22,222,132,135,93,16,122,141,207,124,147,140,
  58,37,195,8,60,172,86,154,5,179,37,130,207,138,
  203,194,67,16,167,78,252,208,241,176,82,152,136,
  207,246,48,27,72,112,93,8,135,61,38,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,113,11,47,28,23,33,244,4,252,139,113,68,46,
  235,200,32,104,199,71,3,46,236,56,5,67,189,74,
  60,166,85,153,65>>,
    %[A, B] = [WorkingPoint, BrokenPoint],
    [A, B] = [WorkingPoint, affine2extended(gen_point())],
    [AW, AB] = extended2affine_batch([A, B]),
    B2 = affine2extended(AB),
    true = is_on_curve(AW),
    true = is_on_curve(AB),
    P = fr:prime(),
    true = e_eq(A, e_mul(A, <<(P+1):256/little>>)),
    true = e_eq(extended_zero(), c_ed:double(c_ed:double(c_ed:double(e_mul(B2, <<(P):256/little>>))))),
    true = e_eq(extended_zero(), c_ed:double(c_ed:double(e_mul(B2, <<(P):256/little>>)))),
    true = e_eq(extended_zero(), e_mul(B2, <<(P*4):256/little>>)),
    true = e_eq(extended_zero(), c_ed:double(e_mul(B2, <<(P):256/little>>))),
    true = e_eq(extended_zero(), e_mul(B2, <<(P):256/little>>)),
    true = e_eq(B, e_mul(B, <<(P+1):256/little>>)),
    Factor = <<333:256/little>>,
    true = e_eq(e_mul(e_neg(B), Factor),
                e_neg(e_mul(B, Factor))),
    success;
test(13) ->
    As = [gen_point(), gen_point()],
    io:fwrite("points generated."),
    Es0 = affine2extended(As),
    Cs = compress_points(Es0),
    As = decompress_points(Cs),
    Es = affine2extended(decompress_points(Cs)),
    As = extended2affine_batch(Es),
    As = extended2affine_batch(Es0),
    Hs = lists:map(fun(X) -> stem2:hash_point(X) end,
                   Es),
    Hs = lists:map(fun(X) -> stem2:hash_point(X) end,
                   Es0),
    success;
test(14) ->
    io:fwrite(""),
    G = affine2extended(gen_point()),
    P = e_mul(G, <<254:256/little>>),
    %P = affine2extended(gen_point()),
    CD = affine2extended(decompress_point(compress_point(P))),
    false = (P == CD),
    %P2 = ed:e_mul(P, <<8:256/little>>),
    %P2b = ed:e_mul(CD, <<8:256/little>>),
  
    {
      e_eq(P, CD),
      %is_on_curve(G),
      is_on_curve(hd(extended2affine_batch([P]))),
      is_on_curve(hd(extended2affine_batch([CD]))),
%      compress_point(P2) == 
%          compress_point(P2b),
      fr:decode([compress_point(P), 
                 compress_point(CD)])};
test(15) ->
    io:fwrite(""),
    G = affine2extended(gen_point()),
    P = e_mul(G, <<254:256/little>>),
    A = hd(extended2affine_batch([P])),
    C = compress_point(P),
    A = decompress_point(C),
    P2 = affine2extended(decompress_point(C)),
    true = e_eq(P, P2),
    success;
test(16) ->
    %adding and doubling the base point, to check that this version of ed25519 is doing the same thing as other implementations.
    P = {affine, 15112221349535400772501151409588531511454012693041857206046113283949847762202, 46316835694926478169428394003475163141307993866256225615783033603165251855960},
    C = ed25519:fencode_point(P),
    A = decompress_point(C),
    A = affine_base(),
    E = affine2extended(decompress_point(C)),
    true = is_on_curve(A),

    E2 = c_ed:double(E),
    E3 = e_add(E, E2),

    [C, C2, C3] = compress_points([E, E2, E3]),

    [P, P2, P3] = lists:map(
                    fun(X) -> ed25519:fdecode_point(X)
                    end, [C, C2, C3]),
    {P, P2, P3}.


%success.

    

    

    
    

    

