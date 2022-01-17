-module(ipa2).
-export([make_ipa/5, verify_ipa/5,
         commit/2, eq/2, 
         basis/2,
         test/1]).
%inner product arguments using pedersen commitments.

%learn more about inner product arguments here https://dankradfeist.de/ethereum/2021/07/27/inner-product-arguments.html

%uses the secp256k1 library.

%-include("../constants.hrl").
%-define(order, 115792089237316195423570985008687907852837564279074904382605163141518161494337).

%-define(mul(A, B), ((A * B) rem ?order)).
%-define(add_mod(C), %assumes C is positive and less than ?prime
%        if (C>= ?order ) -> C - ?order;
%           true -> C end).

dot(A, B) -> dot(A, B, fr:encode(0)).
dot([], [], Acc) -> Acc;
dot([A|AT], [B|BT], Acc) ->
    %dot product of two scalar vectors.
    %io:fwrite("dot 0 \n"),
    %io:fwrite({A, B}),
    Acc2 = fr:mul(A, B),
    %io:fwrite("dot 1 \n"),
    Acc3 = fr:add(Acc, Acc2),
    %io:fwrite("dot 2 \n"),
    dot(AT, BT, Acc3).
%    Acc3 = Acc + Acc2,
%    dot(AT, BT, ?add_mod(Acc3)).
fv_add(As, Bs) ->
    %adding 2 scalar vectors by adding each component.
    lists:zipwith(
      %fun(A, B) -> C = A+B, ?add_mod(C) end,
      fun(A, B) -> fr:add(A, B) end,
      As, Bs).
fv_mul(S, Bs) ->
    %multiplying a scalar vector by a scalar.
    %lists:map(fun(X) -> ?mul(X, S) end,
    lists:map(fun(X) -> fr:mul(X, S) end,
              Bs).

commit(V, G) ->
    %pedersen commitment
    %G is a list of extended niels encoded points.
    %returns a single jacob encoded point.
    %V1*G1 + V2*G2 + V3*G3 + ...
    %secp256k1:multi_exponent(V, G, E).
    %V is integers that fit in 256 bits.

    %todo. call this with the correct inputs.

    multi_exponent:doit(V, G).

add(A, B = <<_:(256*5)>>) ->
    add(A, fq2:extended2extended_niels(B));
add(A, B) ->
    true = is_binary(A),
    true = (32*5) == size(A),
    true = is_binary(B),
    true = (32*4) == size(B),
    fq2:e_add(A, B).
    %secp256k1:jacob_add(A, B, E).
%sub(A, B, E) ->
%    secp256k1:jacob_sub(A, B, E).
%double(A, E) ->
%    secp256k1:jacob_double(A, E).
mul(X, G) ->
    %multiply point G by scalar X.
    %secp256k1:jacob_mul(G, X, E).
    true = is_binary(X),
    true = 32 == size(X),
    true = is_binary(G),
    true = (32*4) == size(G),
    fq2:e_mul_long(G, X).
eq(G, H) ->
    %secp256k1:jacob_equal(G, H, E).
    fq2:eq(G, H).
v_add(As, Bs) ->
    lists:zipwith(
      fun(A, B) ->
              add(A, B)
      end, As, Bs).
v_mul(A, Bs) ->
    %this is like, half way to a commitment. it does the multiplications, but doesn't add up the points at the end.
    R = lists:map(
          fun(B) ->
                  mul(A, B)
          end, Bs),
    %simplify_v(R).
    R.

simplify_v(X) ->
    %simplifies jacobian points to make the denomenator of the projective points Z = 1.
    %secp256k1:simplify_Zs_batch(X).
    fq2:e_simplify_batch(X).

points_to_entropy(L) ->
    L2 = simplify_v(L),
    lists:map(fun(<<X:512, _/binary>>) ->
                      X rem fq2:prime()
              end, L2).
   
%todo. update below here to not use secp256k1. 

make_ipa(A, B, G, H, Q) ->
    io:fwrite("make ipa 0\n"),
    AG = commit(A, G),
    BH = commit(B, H),
    io:fwrite("make ipa 1\n"),
    %io:fwrite({size(hd(A)), A, G, AG, BH}),
    AGBH = add(AG, BH),
    io:fwrite("make ipa 2\n"),
    AB = dot(A, B),
    io:fwrite("make ipa 3\n"),
    ABQ = mul(AB, Q),
    C1 = add(AGBH, ABQ),
    %io:fwrite({size(AGBH), size(ABQ), AGBH, ABQ, C1}),
    io:fwrite("make ipa 4\n"),
    %io:fwrite({fq2:decode_extended(AG), fq2:decode_extended(BH), fq2:decode_extended(AGBH)}),
    %io:fwrite({fq2:decode_extended(AGBH), fq2:decode_extended(mul(AB, Q)), fq2:decode_extended(C1)}),
    [X0] = points_to_entropy([C1]),
    X = fr:encode((X0 rem fr:prime())),
    io:fwrite("make ipa 5\n"),
    Xi = fr:inv(X),
    %io:fwrite({X, C1, Xi}),
    io:fwrite("make ipa 6\n"),
    {Cs0, AN, BN} = 
        make_ipa2(C1, A, G, B, H, 
                  Q, [C1], X, Xi), 
    io:fwrite("make ipa 7\n"),
    [AGf|Cs] = simplify_v([AG|Cs0]),
    io:fwrite("make ipa 8\n"),
    {AGf, AB, Cs, AN, BN}.
    
make_ipa2(_C1, [A], _, [B], _, _, Cs, _, _) ->
    %maybe at this point we should compress some of this data so it is smaller to send.
    {Cs, A, B};
make_ipa2(C1, A, G, B, H, Q, Cs, X, Xi)  ->
    S2 = length(A) div 2,
    {Al, Ar} = lists:split(S2, A),
    {Bl, Br} = lists:split(S2, B),
    Zl = dot(Ar, Bl),
    Zr = dot(Al, Br),
    {Gl, Gr} = lists:split(S2, G),
    {Hl, Hr} = lists:split(S2, H),
    Cl = add(commit(Ar, Gl),
             add(commit(Bl, Hr),
                 mul(Zl, Q))),
    Cr = add(commit(Al, Gr),
             add(commit(Br, Hl),
                 mul(Zr, Q))),
    A2 = fv_add(Al, fv_mul(X, Ar)),
    B2 = fv_add(Bl, fv_mul(Xi, Br)),
    C12 = add(mul(X,  fq2:extended2extended_niels(Cl)),
             mul(Xi, fq2:extended2extended_niels(Cr))),
    C2 = add(C1, C12),
    %G2 = v_add(Gl, v_mul(Xi, Gr, E), E),
    %H2 = v_add(Hl, v_mul(X, Hr, E), E),
    G20 = v_add(fq2:extended_niels2extended(Gl), 
               simplify_v(v_mul(Xi, Gr))),
    H20 = v_add(fq2:extended_niels2extended(Hl), 
               simplify_v(v_mul(X, Hr))),
    G2 = fq2:extended2extended_niels(G20),
    H2 = fq2:extended2extended_niels(H20),
               
    make_ipa2(C2, A2, G2, B2, 
              H2, Q, [Cl, Cr|Cs], X, Xi).

get_gn(_, [G]) -> G;
get_gn(X, G) ->
    S = length(G),
    S2 = S div 2,
    {Gl, Gr} = lists:split(S2, G),
    Gr2 = v_mul(X, Gr),
    Gr3 = simplify_v(Gr2),
    G2 = v_add(Gl, Gr3),
    get_gn(X, G2).

foldh_mul(_, _, [C]) -> [C];
foldh_mul(X, Xi, [L, R|C]) -> 
    [mul(X, L), mul(Xi, R)|
     foldh_mul(X, Xi, C)].
fold_cs(X, Xi, Cs) ->
    Cs30 = foldh_mul(X, Xi, Cs),
    Cs3 = if
              (length(Cs30) > 15) ->  
                  Cs30;
              true -> Cs30
          end,
    lists:foldl(fun(A, B) ->
                        add(A, B)
                end, fq2:e_zero(), 
                Cs3).

%-define(comp(X), secp256k1:compress(X)).
%-define(deco(X), secp256k1:decompress(X)).

%compress({AG, AB, Cs, AN, BN}) ->    
%    [AG2|Cs2] = 
%        secp256k1:compress(
%          [AG|Cs]),
%    {AG2, AB, Cs2, AN, BN}.
%decompress({AG, AB, Cs, AN, BN}) ->
%    Cs2 = lists:map(fun(X) -> ?deco(X) end, Cs),
%    {?deco(AG), AB, Cs2, AN, BN}.

verify_ipa({AG0, AB, Cs0, AN, BN}, %the proof
           B, G, H, Q) ->
    %we may need to decompress the proof at this point.
    [AG|Cs] = simplify_v([AG0|Cs0]),
    C1 = hd(lists:reverse(Cs)),
    C1b = add(add(AG, commit(B, H)), 
             mul(AB, Q)),
    EB = eq(C1, C1b),
    if
        not(EB) -> false;
        true ->
    
            [X] = points_to_entropy([C1]),
            Xi = fr:inv(X),
            GN = get_gn(Xi, G),
            HN = get_gn(X, H),
            CNa = add(add(mul(AN, GN),
                          mul(BN, HN)),
                      mul(fq2:mul(AN, BN), Q)),
            %T1 = erlang:timestamp(),
            CNb = fold_cs(X, Xi, Cs),
            %T2 = erlang:timestamp(),
            eq(CNa, CNb)
    end.

gen_point(_E) ->
    fq2:extended2extended_niels(
      fq2:gen_point()).
%    secp256k1:to_jacob(
%      secp256k1:gen_point(E)).
basis(S, E) ->
    G = lists:map(fun(_) ->
                           gen_point(E)
                   end, range(0, S)),
    H = lists:map(fun(_) ->
                           gen_point(E)
                   end, range(0, S)),
    Q = gen_point(E),
    {G, H, Q}.

range(X, X) -> [];
range(X, Y) when X < Y -> 
    [X|range(X+1, Y)].

encode_list(L) ->
    lists:map(fun(X) -> fr:encode(X) end, L).

test(1) ->
    A0 = range(100, 108),
    A = encode_list(A0),
    %A = A0,
    S = length(A),
    E = secp256k1:make(),
    {G, H, Q} = basis(S, E),
    Bv = encode_list([0,0,0,1,1,0,0,0]),%103+104 = 207
    Bv2 = encode_list([1,0,0,0,0,1,0,0]),%100+105 = 205
    io:fwrite("test 1 0 \n"),
    Proof = make_ipa(
              A, Bv,%103+104 = 207
              G, H, Q),
    N207 = fr:encode(207),
    {_, N207, _, _, _} = Proof,
    io:fwrite("test 1 1 \n"),
    Proof2 = make_ipa(
              A, Bv2,%103+104 = 207
              G, H, Q),
    io:fwrite("test 1 2 \n"),
    true = verify_ipa(Proof, Bv, G, H, Q),
    io:fwrite("test 1 3 \n"),
    true = verify_ipa(Proof2, Bv2, G, H, Q),
    io:fwrite("test 1 4 \n"),
    success;
test(2) ->
    %comparing the speed between versions
    A = range(100, 356),
    %A = range(100, 132),
    S = length(A),
    E = secp256k1:make(),
    {G, H, Q} = basis(S, E),
    B = range(200, 200 + length(A)),
    T1 = erlang:timestamp(),
    Proof = make_ipa(A, B, G, H, Q),
    T2 = erlang:timestamp(),
    true = verify_ipa(Proof, B, G, H, Q),
    T3 = erlang:timestamp(),

    %E2 = E,
    %{G2, H2, Q2} = pedersen:basis(S, E2),
    %T4 = erlang:timestamp(),
%    Proof2 = pedersen:make_ipa(
%              A, B,
%              G2, H2, Q2, E2),
%    T5 = erlang:timestamp(),
%    true = pedersen:verify_ipa(
%             Proof2, B, G2, H2, Q2, E2),
%    T6 = erlang:timestamp(),

    {{make, timer:now_diff(T2, T1)},%     2246729
     {verify, timer:now_diff(T3, T2)}%,%   1570761
%     {make2, timer:now_diff(T5, T4)},%   10728733
%     {verify2, timer:now_diff(T6, T5)}%   9816297
};
%new version creates the proof 4.5x faster, and verifies 6x faster.

test(3) ->
    %testing compression.
    A = range(100, 108),
    S = length(A),
    E = secp256k1:make(),
    {G, H, Q} = basis(S, E),
    Bv = [0,0,0,1,1,0,0,0],%103+104 = 207
    Proof = make_ipa(
              A, Bv,%103+104 = 207
              G, H, Q),
    success;
test(4) ->
    %speed test.
    verkle_app:start(normal, []),
    %Gs = ?p#p.g,
    %E = ?p#p.e,
    G2 = ok,
    E = ok,
    Many = 10,
    V = lists:map(fun(_) ->
                          <<R:256>> = 
                              crypto:strong_rand_bytes(32),
                          R
                  end, range(0, 256)),
    256 = length(V),
    MEP = parameters:multi_exp(),
    T1 = erlang:timestamp(),
    lists:map(fun(_) ->
                      %commit(V, Gs)
                      commit(V, ok)
              end, range(0, Many)),
    T2 = erlang:timestamp(),
    lists:map(fun(_) ->
                          store:precomputed_multi_exponent(V, MEP)
              end, range(0, Many)),
    T3 = erlang:timestamp(),
    lists:map(fun(_) ->
                       %secp256k1:simple_exponent(V, Gs, fq2:e_zero())
                       secp256k1:simple_exponent(V, ok, fq2:e_zero())
              end, range(0, Many)),
    T4 = erlang:timestamp(),
    {timer:now_diff(T2, T1)/Many,%0.115
     timer:now_diff(T3, T2)/Many,%0.066
     timer:now_diff(T4, T3)/Many}.%0.69
    
                     
    


    
    

