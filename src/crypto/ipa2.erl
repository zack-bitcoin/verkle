-module(ipa2).
-export([make_ipa/5, verify_ipa/5,
         commit/2, eq/2, 
         gen_point/0,
         basis/1, dot/2,
         test/1]).
%inner product arguments using pedersen commitments.

%learn more about inner product arguments here https://dankradfeist.de/ethereum/2021/07/27/inner-product-arguments.html

%uses secp256k1 the library.

%-define(order, 115792089237316195423570985008687907852837564279074904382605163141518161494337).

%-define(mul(A, B), ((A * B) rem ?order)).
%-define(add_mod(C), %assumes C is positive and less than ?prime
%        if (C>= ?order ) -> C - ?order;
%           true -> C end).

-define(sanity_checks, false).

dot(A, B) -> dot(A, B, fr:encode(0)).
dot([], [], Acc) -> Acc;
dot([A|AT], [B|BT], Acc) ->
    %dot product of two scalar vectors.
    Acc2 = fr:mul(A, B),
    Acc3 = fr:add(Acc, Acc2),
    dot(AT, BT, Acc3).
fv_add(As, Bs) ->
    %adding 2 scalar vectors by adding each component.
    lists:zipwith(
      %fun(A, B) -> C = A+B, ?add_mod(C) end,
      fun(A, B) -> fr:add(A, B) end,
      As, Bs).
fv_mul(S, Bs) ->
    %multiplying a scalar vector by a scalar.
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

add(A, B) ->
    %fq:e_add(A, B).
    ed:e_add(A, B).

mul(X, G) ->
    mul2(X, G).
mul2(X, G) ->
    %multiply point G by scalar X.
    %X is a montgomery encoded binary.
%    true = is_binary(X),
%    true = 32 == size(X),
%    true = is_binary(G),
%    true = (((32*4) == size(G)) or
%            ((32*5) == size(G))),
    %fq:e_mul2(G, X).
    %ed:e_mul(G, X).
    ed:e_mul2(G, X).
%    case ed:decode(X) of
%        0 -> ed:extended_zero();
%        R -> ed:e_mul(G, <<R:256/little>>)
%    end.
mul1(X, G) ->
    %mul2(X, G).
    ed:e_mul(G, X).
    %multiply point G by scalar X.
    %X is a little endian integer.
%    true = is_binary(X),
%    true = 32 == size(X),
%    true = is_binary(G),
%    true = (32*4) == size(G),
    %fq:e_mul1(G, X).
eq(G, H) ->
    %secp256k1:jacob_equal(G, H, E).
    %fq:eq(G, H).
    ed:e_eq(G, H).
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
    %fq:e_simplify_batch(X).
    %fq:e_simplify_batch(X).
    ed:normalize(X).

points_to_entropy(L) ->
    %lists:map(fun(X) -> fq:hash_point(X) end,
    lists:map(fun(X) -> ed:compress_point(X) end,
              L).

%    L2 = simplify_v(L),
    %io:fwrite({size(hd(L2)), L2}),
%    lists:map(fun(<<X:512, _/binary>>) ->
%                      fr:encode(X rem fr:prime())
%              end, L2).
   
%todo. update below here to not use secp256k1. 

make_ipa(A, B, G, H, Q) ->
    %proving a statement of the form
    %C = AG+BH+AB*Q
    AG = commit(A, G),
    AB = dot(A, B),
    %io:fwrite({size(Q), size(AB)}),%64, 32
    C1 = add(add(AG, commit(B, H)), 
             mul(AB, Q)),%AB is int, Q is e-point
    %[X] = points_to_entropy([C1]),
    X = fr:encode(1),
    Xi = fr:inv(X),
    {Cs0, AN, BN} = 
        make_ipa2(C1, A, G, B, H, 
                  Q, [C1], X, Xi), 
    [AGf|Cs] = simplify_v([AG|Cs0]),
    {AGf, AB, Cs, AN, BN}.
    
make_ipa2(C1, [A], [G], [B], [H], Q, Cs, _, _) ->
    %maybe at this point we should compress some of this data so it is smaller to send.
    if
        ?sanity_checks ->
            C2 = add(add(mul(A, G),
                         mul(B, H)),
                     mul(fr:mul(A, B), Q)),
            %io:fwrite("last C1\n"),
            %io:fwrite(base64:encode(fq:extended2affine(C1))),
            %io:fwrite("\n"),
            %io:fwrite("last C2\n"),
            %io:fwrite(base64:encode(fq:extended2affine(C2))),
            %io:fwrite("\n"),
            io:fwrite("B is: "),
            io:fwrite(integer_to_list(fr:decode(B))),
            io:fwrite("\n"),
            %Bool = fq:eq(C1, C2),
            Bool = ed:e_eq(C1, C2),
            if
                not(Bool) ->
                    io:fwrite("sanity check\n"),
                    1=2;
                true -> 
                    ok
            end;
        true -> ok
    end,
    {Cs, A, B};
make_ipa2(C1, A, G, B, H, Q, Cs, X, Xi)  ->
    if
        ?sanity_checks ->
            C1b =  add(add(commit(A, G), 
                          commit(B, H)),
                      mul(dot(A, B), Q)),
            %Bool = fq:eq(C1, C1b),
            Bool = ed:e_eq(C1, C1b),
            if
                not(Bool) ->
                    io:fwrite("sanity check\n"),
                    io:fwrite("\n"),
                    1=2;
                true -> 
                    io:fwrite("B is: "),
                    lists:map(
                      fun(X) -> 
                              io:fwrite(integer_to_list(fr:decode(X))),
                              io:fwrite(" ")
                      end,
                      B),
                    io:fwrite("\n"),
                    ok
            end;
        true -> ok
    end,

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
    C12 = add(mul(X,Cl),
             mul(Xi, Cr)),
    C2 = add(C1, C12),
    G2 = v_add(v_mul(Xi, Gr), Gl),
    H2 = v_add(v_mul(X, Hr), Hl),
    %G20 = v_add(simplify_v(v_mul(Xi, Gr)), Gl),
    %H20 = v_add(simplify_v(v_mul(X, Hr)), Hl),
    %G2 = fq:extended2extended_niels(G20),
    %H2 = fq:extended2extended_niels(H20),
               
    make_ipa2(C2, A2, G2, B2, 
              H2, Q, [Cl, Cr|Cs], X, Xi).

get_gn(_, [G]) -> G;
get_gn(X, G) ->
    S = length(G),
    S2 = S div 2,
    {Gl, Gr} = lists:split(S2, G),
    Gr2 = v_mul(X, Gr),
    %Gr3 = simplify_v(Gr2),
    %G2 = v_add(Gl, Gr3),
    G2 = v_add(Gr2, Gl),
    get_gn(X, G2).

foldh_mul(_, _, [C]) -> 
    [C];
foldh_mul(X, Xi, [L, R|C]) -> 
    [mul(X, L), mul(Xi, R)|
     foldh_mul(X, Xi, C)].
fold_cs(X, Xi, Cs) ->
    Cs3 = foldh_mul(X, Xi, Cs),
    lists:foldl(fun(A, B) ->
                        add(A, B)
                %end, fq:e_zero(), 
                end, ed:extended_zero(), 
                Cs3).

%-define(comp(X), secp256k1:compress(X)).
%-define(deco(X), secp256k1:decompress(X)).

verify_ipa({AG0, AB, Cs0, AN, BN}, %the proof
           B, G, H, Q) ->
    %we may need to decompress the proof at this point.
    [AG|Cs] = simplify_v([AG0|Cs0]),
    C1 = hd(lists:reverse(Cs)),
    C1b = add(add(AG, commit(B, H)), 
             mul(AB, Q)),
    EB = eq(C1, C1b),
    if
        not(EB) -> 
            io:fwrite("verify ipa false 1\n"),
            false;
        true ->
    
            %[X] = points_to_entropy([C1]),
            X = fr:encode(1),
            Xi = fr:inv(X),
            GN = get_gn(Xi, G),
            HN = get_gn(X, H),
            CNa = add(add(mul(AN, GN),
                          mul(BN, HN)),
                      mul(fr:mul(AN, BN), Q)),
            %T1 = erlang:timestamp(),
            CNb = fold_cs(X, Xi, Cs),
            %T2 = erlang:timestamp(),
            B2 = eq(CNa, CNb),
            if
                B2 -> true;
                true ->
                    io:fwrite("verify ipa false 2\n"),
                    false
                    %io:fwrite({size(CNa), size(CNb), base64:encode(fq:extended2affine(CNa)), base64:encode(fq:extended2affine(CNb))})
            end
    end.

gen_point() -> ed:gen_point().
%    fq:affine2extended(
%      fq:gen_point()).
basis(S) ->
    G = lists:map(fun(_) ->
                           gen_point()
                   end, range(0, S)),
    H = lists:map(fun(_) ->
                           gen_point()
                   end, range(0, S)),
    Q = gen_point(),
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
    {G, H, Q} = basis(S),


    Bv = encode_list([10,0,3,1,1,2,0,10]),%103+104 = 207
    Bv2 = encode_list([0,0,0,0,0,0,0,1]),%100+105 = 205
    io:fwrite("test 1 0 \n"),
    Proof = make_ipa(
              A, Bv,%103+104 = 207
              G, H, Q),
    io:fwrite("test 1 1 \n"),
    true = verify_ipa(Proof, Bv, G, H, Q),
    %N207 = fr:encode(207),
    %{_, N207, _, _, _} = Proof,
    io:fwrite("test 1 3 \n"),
    Proof2 = make_ipa(
              A, Bv2,
              G, H, Q),
    %100 = fr:decode(element(2, Proof2)),
    io:fwrite("test 1 4 \n"),
    true = verify_ipa(Proof2, Bv2, G, H, Q),
    success;
test(2) ->
    %comparing the speed between versions
    A = range(100, 356),
    %A = range(100, 132),
    S = length(A),
    {G, H, Q} = basis(S),
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
    {G, H, Q} = basis(S),
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
    %G2 = ok,
    %E = ok,
    {Gs, _, _} = parameters2:read(),
    Many = 10,
    V = lists:map(fun(_) ->
                          <<R:256>> = 
                              crypto:strong_rand_bytes(32),
                          fr:encode(R)
                  end, range(0, 256)),
    256 = length(V),
    MEP = parameters2:multi_exp(),
    T1 = erlang:timestamp(),
    lists:map(fun(_) ->
                      commit(V, Gs)
              end, range(0, Many)),
    T2 = erlang:timestamp(),
    lists:map(fun(_) ->
                          store2:precomputed_multi_exponent(V, MEP)
              end, range(0, Many)),
    T3 = erlang:timestamp(),
    lists:map(fun(_) ->
                       %secp256k1:simple_exponent(V, Gs, fq:e_zero())
                      %multi_exponent:simple_exponent(V, Gs, fq:e_zero())
                      ok
              end, range(0, Many)),
    T4 = erlang:timestamp(),
    D1 = timer:now_diff(T2, T1)/Many,
    D2 = timer:now_diff(T3, T2)/Many,
    %{speedup, D1/D2};
    {{normal, timer:now_diff(T2, T1)/Many},%0.115
     {with_precompute, timer:now_diff(T3, T2)/Many}%,%0.066
     %timer:now_diff(T4, T3)/Many
    };%0.69
test(5) ->
    io:fwrite("testing the palindrone bug\n"),
    A0 = range(100, 108),
    A = encode_list(A0),
    S = length(A),
    {G, H, Q} = basis(S),
    Bv2 = encode_list([1,0,0,0,0,0,0,0]),
    Proof2 = make_ipa(
              A, Bv2,
              G, H, Q),
    %{AGf, AB, Cs, AN, BN}.
    true = verify_ipa(Proof2, Bv2, G, H, Q),
    success.
    

    
                     
    


    
    

