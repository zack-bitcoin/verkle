-module(ipa).
-export([make_ipa/6, verify_ipa/6,
         commit/3, eq/3, 
         basis/2,
         test/1]).
%inner product arguments using pedersen commitments.

%learn more about inner product arguments here https://dankradfeist.de/ethereum/2021/07/27/inner-product-arguments.html

%uses the secp256k1 library.

-include("../constants.hrl").
%-define(order, 115792089237316195423570985008687907852837564279074904382605163141518161494337).

%-define(mul(A, B), ((A * B) rem ?order)).
%-define(add_mod(C), %assumes C is positive and less than ?prime
%        if (C>= ?order ) -> C - ?order;
%           true -> C end).

dot(A, B) -> dot(A, B, 0).
dot([], [], Acc) -> Acc;
dot([A|AT], [B|BT], Acc) ->
    %dot product of two scalar vectors.
    Acc2 = ?mul(A, B),
    Acc3 = Acc + Acc2,
    dot(AT, BT, ?add_mod(Acc3)).
fv_add(As, Bs) ->
    %adding 2 scalar vectors by adding each component.
    lists:zipwith(
      fun(A, B) -> C = A+B, ?add_mod(C) end,
      As, Bs).
fv_mul(S, Bs) ->
    %multiplying a scalar vector by a scalar.
    lists:map(fun(X) -> ?mul(X, S) end,
              Bs).

commit(V, G, E) ->
    %pedersen commitment
    %G is a list of jacob encoded points.
    %returns a single jacob encoded point.
    %V1*G1 + V2*G2 + V3*G3 + ...
    secp256k1:multi_exponent(V, G, E).

add(A, B, E) ->
    secp256k1:jacob_add(A, B, E).
%sub(A, B, E) ->
%    secp256k1:jacob_sub(A, B, E).
%double(A, E) ->
%    secp256k1:jacob_double(A, E).
mul(X, G, E) ->
    %multiply point G by scalar X.
    secp256k1:jacob_mul(G, X, E).
eq(G, H, E) ->
    secp256k1:jacob_equal(G, H, E).
v_add(As, Bs, E) ->
    lists:zipwith(
      fun(A, B) ->
              add(A, B, E)
      end, As, Bs).
v_mul(A, Bs, E) ->
    %this is like, half way to a commitment. it does the multiplications, but doesn't add up the points at the end.
    R = lists:map(
          fun(B) ->
                  mul(A, B, E)
          end, Bs),
    %simplify_v(R).
    R.

simplify_v(X) ->
    %simplifies jacobian points to make the denomenator of the projective points = 1.
    secp256k1:simplify_Zs_batch(X).

point_to_entropy(J) ->
    secp256k1:hash_point(J).
    
make_ipa(A, B, G, H, Q, E) ->
    AG = commit(A, G, E),
    BH = commit(B, H, E),
    AGBH = add(AG, BH, E),
    AB = dot(A, B),
    C1 = add(AGBH, mul(AB, Q, E), E),
    X = point_to_entropy(C1),
    Xi = basics:inverse(X, ?order),
    {Cs0, AN, BN} = 
        make_ipa2(C1, A, G, B, H, 
                  Q, E, [C1], X, Xi), 
    [AGf|Cs] = simplify_v([AG|Cs0]),
    {AGf, AB, Cs, AN, BN}.
    
make_ipa2(_C1, [A], _, [B], _, _, _, Cs, _, _) ->
    %maybe at this point we should compress some of this data so it is smaller to send.
    {Cs, A, B};
make_ipa2(C1, A, G, B, H, Q, E, Cs, X, Xi) ->
    S2 = length(A) div 2,
    {Al, Ar} = lists:split(S2, A),
    {Bl, Br} = lists:split(S2, B),
    Zl = dot(Ar, Bl),
    Zr = dot(Al, Br),
    {Gl, Gr} = lists:split(S2, G),
    {Hl, Hr} = lists:split(S2, H),
    Cl = add(commit(Ar, Gl, E),
             add(commit(Bl, Hr, E),
                 mul(Zl, Q, E), E), E),
    Cr = add(commit(Al, Gr, E),
             add(commit(Br, Hl, E),
                 mul(Zr, Q, E), E), E),
    A2 = fv_add(Al, fv_mul(X, Ar)),
    B2 = fv_add(Bl, fv_mul(Xi, Br)),
    C12 = add(mul(X,  Cl, E),
             mul(Xi, Cr, E), E),
    C2 = add(C1, C12, E),
    %G2 = v_add(Gl, v_mul(Xi, Gr, E), E),
    %H2 = v_add(Hl, v_mul(X, Hr, E), E),
    G2 = v_add(Gl, simplify_v(v_mul(Xi, Gr, E)), E),
    H2 = v_add(Hl, simplify_v(v_mul(X, Hr, E)), E),
    make_ipa2(C2, A2, G2, B2, 
              H2, Q, E, [Cl, Cr|Cs], X, Xi).

get_gn(_, [G], _) -> G;
get_gn(X, G, E) ->
    S = length(G),
    S2 = S div 2,
    {Gl, Gr} = lists:split(S2, G),
    Gr2 = v_mul(X, Gr, E),
    Gr3 = simplify_v(Gr2),
    G2 = v_add(Gl, Gr3, E),
    %G2 = simplify_v(G20),
    %G2 = v_add(Gl, v_mul(X, Gr, E), E),
    get_gn(X, G2, E).

foldh_mul(_, _, [C], _) -> [C];
foldh_mul(X, Xi, [L, R|C], E) -> 
    [mul(X, L, E), mul(Xi, R, E)|
     foldh_mul(X, Xi, C, E)].
fold_cs(X, Xi, Cs, E) ->
    Cs30 = foldh_mul(X, Xi, Cs, E),
    Cs3 = if
              (length(Cs30) > 15) ->  
                  %simplify_v(Cs30);
                  Cs30;
              true -> Cs30
          end,
    lists:foldl(fun(A, B) ->
                        add(A, B, E)
                end, secp256k1:jacob_zero(), 
                Cs3).

-define(comp(X), secp256k1:compress(X)).
-define(deco(X), secp256k1:decompress(X)).

compress({AG, AB, Cs, AN, BN}) ->    
    [AG2|Cs2] = 
        secp256k1:compress(
          [AG|Cs]),
    {AG2, AB, Cs2, AN, BN}.
decompress({AG, AB, Cs, AN, BN}) ->
    Cs2 = lists:map(fun(X) -> ?deco(X) end, Cs),
    {?deco(AG), AB, Cs2, AN, BN}.

verify_ipa({AG0, AB, Cs0, AN, BN}, %the proof
           B, G, H, Q, E) ->
    %we may need to decompress the proof at this point.
    [AG|Cs] = simplify_v([AG0|Cs0]),
    C1 = hd(lists:reverse(Cs)),
    C1b = add(add(AG, commit(B, H, E), E), 
             mul(AB, Q, E), E),
    EB = eq(C1, C1b, E),
    if
        not(EB) -> false;
        true ->
    
            X = point_to_entropy(C1),
            Xi = basics:inverse(X, ?order),
            GN = get_gn(Xi, G, E),
            HN = get_gn(X, H, E),
            CNa = add(add(mul(AN, GN, E),
                          mul(BN, HN, E),
                          E),
                      mul(?mul(AN, BN), Q, E),
                      E),
            %T1 = erlang:timestamp(),
            CNb = fold_cs(X, Xi, Cs, E),
            %T2 = erlang:timestamp(),
            eq(CNa, CNb, E)
    end.

gen_point(E) ->
    secp256k1:to_jacob(
      secp256k1:gen_point(E)).
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

test(1) ->
    A = range(100, 108),
    S = length(A),
    E = secp256k1:make(),
    {G, H, Q} = basis(S, E),
    Bv = [0,0,0,1,1,0,0,0],%103+104 = 207
    Bv2 = [1,0,0,0,0,1,0,0],%100+105 = 205
    Proof = make_ipa(
              A, Bv,%103+104 = 207
              G, H, Q, E),
    {_, 207, _, _, _} = Proof,
    Proof2 = make_ipa(
              A, Bv2,%103+104 = 207
              G, H, Q, E),
    true = verify_ipa(Proof, Bv, G, H, Q, E),
    true = verify_ipa(Proof2, Bv2, G, H, Q, E),
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
    Proof = make_ipa(
              A, B,
              G, H, Q, E),
    T2 = erlang:timestamp(),
    true = verify_ipa(Proof, B, G, H, Q, E),
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
              G, H, Q, E),
    P2 = compress(Proof),
    Proof2 = decompress(P2),%non-identical because jacobian format is not deterministic.
    P2 = compress(Proof2),
    success;
test(4) ->
    %speed test.
    verkle_app:start(normal, []),
    Gs = ?p#p.g,
    E = ?p#p.e,
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
                          commit(V, Gs, E)
              end, range(0, Many)),
    T2 = erlang:timestamp(),
    lists:map(fun(_) ->
                          store:precomputed_multi_exponent(V, MEP)
              end, range(0, Many)),
    T3 = erlang:timestamp(),
    {timer:now_diff(T2, T1)/Many,%0.115
     timer:now_diff(T3, T2)/Many}.%0.066
    
                     
    


    
    

