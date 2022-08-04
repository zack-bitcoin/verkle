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
decompress_point(<<S:1, P:255>>) ->
    true = P < ?q,
    UU = mul(<<P:256>>, <<P:256>>),
    DUU = mul(?D, UU),
    B = inv(sub(?one, DUU)),
    T = add(?one, UU),
    VV = mul(T, B),
    case sqrt(VV) of
        error ->
            %invalid point.
            io:fwrite("invalid, no square root\n"),
            error;
        {V1, V2} ->
            V = case S of
                    0 -> V1;
                    1 -> V2
                end,
            Point = <<P:256, V/binary>>,
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
compress_point(<<X0:256, Y0:256>>) ->
    %Y = decode(<<Y0:256>>),
    S = case not((Y0 band  ?max255) == 0) of
            true -> 1;
            false -> 0
        end,
    <<S:1, X0:255>>.
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
    C0 = gen_point(),
    io:fwrite("have point\n"),
    C = affine2extended(C0),
    P = compress_point(C0),
%    Pm = ed25519:mencode_point(P),
%    Pf = ed25519:fencode_point(P),
%    io:fwrite({P, Pm, Pf}),
    C0 = decompress_point(P),
    M = ed25519:maffine2extended(
          ed25519:mdecode_point(P)),
    M2 = ed25519:mextended_double(M),
    C2 = c_ed:double(C),

    P2 = compress_point(
           hd(extended2affine_batch([C2]))),
    M2b = ed25519:maffine2extended(
            ed25519:mdecode_point(P2)),
    true = ed25519:meq(M2, M2b),
    success.
        
    

