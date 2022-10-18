-module(ipa).
-export([make_ipa/5, verify_ipa/5,
         commit/2, %eq/2, 
         %gen_point/0,
         gen_point/1,
         basis/1, dot/2,
         base64_tree/1,
         test/1]).
%inner product arguments using pedersen commitments.

%learn more about inner product arguments here https://dankradfeist.de/ethereum/2021/07/27/inner-product-arguments.html

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
      fun(A, B) -> fr:add(A, B) end,
      As, Bs).
fv_mul(S, Bs) ->
    %multiplying a scalar vector by a scalar.
    lists:map(fun(X) -> fr:mul(X, S) end,
              Bs).

commit(V, G) ->
    %pedersen commitment
    %V1*G1 + V2*G2 + V3*G3 + ...
    %V is montgomery encoded integers, g is elliptic curve points.
    multi_exponent:doit(V, G).

add(A, B) ->
    ed:e_add(A, B).
mul(X, G) -> mul2(X, G).
mul2(X, G) ->
    %multiply point G by scalar X.
    %X is a montgomery encoded binary.
    ed:e_mul2(G, X).
mul1(X, G) ->
    ed:e_mul(G, X).
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
    R.

simplify_v(X) -> ed:normalize(X).
point_to_entropy(L) -> 
    stem2:hash_point(L).

make_ipa(A, B, G, H, Q) ->
    %proving a statement of the form
    %C = AG+BH+AB*Q

    %the receiver already knows B, G, H, and Q. 
    %We send them C, AG, and AB, 
    AG = commit(A, G),
    AB = dot(A, B),
    C1 = add(add(AG, commit(B, H)), 
             mul(AB, Q)),%AB is int, Q is e-point
    X = point_to_entropy(C1),
    Xi = fr:inv(X),
    {Cs0, AN, BN} = 
        make_ipa2(C1, A, G, B, H, 
                  Q, [C1], X, Xi), 
    [AGf|Cs] = simplify_v([AG|Cs0]),
    {AGf, AB, Cs, AN, BN}.
    
make_ipa2(C1, [A], [G], [B], [H], Q, Cs, _, _) ->
    if
        ?sanity_checks ->
            C2 = add(add(mul(A, G),
                         mul(B, H)),
                     mul(fr:mul(A, B), Q)),
            Bool = ed:e_eq(C1, C2),
            if
                not(Bool) ->
                    io:fwrite("final sanity check\n"),
                    1=2;
                true -> ok
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
            Bool = ed:e_eq(C1, C1b),
            if
                not(Bool) ->
                    io:fwrite(integer_to_list(length(A))),
                    io:fwrite(" sanity check\n"),
                    io:fwrite("\n"),
                    1=2;
                true -> ok
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
    C12 = add(mul(X,Cl), mul(Xi, Cr)),
    C2 = add(C1, C12),
    G2 = v_add(v_mul(Xi, Gr), Gl),
    H2 = v_add(v_mul(X, Hr), Hl),
               
    make_ipa2(C2, A2, G2, B2, 
              H2, Q, [Cl, Cr|Cs], X, Xi).

get_gn(_, [G]) -> G;
get_gn(X, G) ->
    S = length(G),
    S2 = S div 2,
    {Gl, Gr} = lists:split(S2, G),
    Gr2 = v_mul(X, Gr),
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
                end, ed:extended_zero(), 
                Cs3).

verify_ipa({AG0, AB, Cs0, AN, BN}, %the proof
           B, G, H, Q) ->
    [AG|Cs] = simplify_v([AG0|Cs0]),
    C1 = hd(lists:reverse(Cs)),
    C1b = add(add(AG, commit(B, H)), 
             mul(AB, Q)),
    EB = ed:e_eq(C1, C1b),
    if
        not(EB) -> 
            io:fwrite("verify ipa false 1\n"),
            false;
        true ->
    
            X = point_to_entropy(C1),
            Xi = fr:inv(X),
            GN = get_gn(Xi, G),
            HN = get_gn(X, H),
            CNa = add(add(mul(AN, GN),
                          mul(BN, HN)),
                      mul(fr:mul(AN, BN), Q)),
            CNb = fold_cs(X, Xi, Cs),
            B2 = ed:e_eq(CNa, CNb),
            if
                B2 -> true;
                true ->
                    io:fwrite("verify ipa false 2\n"),
                    false
            end
    end.

gen_point(I) ->
    A = <<I:256/little>>,
    H = hash:doit(A),
    ed:gen_point(H).
basis(S) ->
    G = lists:map(fun(R) -> gen_point(R)
                   end, range(0, S)),
    H = lists:map(fun(R) -> gen_point(R)
                   end, range(S, S*2)),
    Q = gen_point(S*2),
    {G, H, Q}.

range(X, X) -> [];
range(X, Y) when X < Y -> 
    [X|range(X+1, Y)].

encode_list(L) ->
    lists:map(fun(X) -> fr:encode(X) end, L).



fr_print([]) -> ok;
fr_print([H]) when is_list(H) -> 
    io:fwrite("["),
    fr_print(H),
    io:fwrite("]");
fr_print([H|T]) when is_list(H) -> 
    io:fwrite("["),
    fr_print(H),
    io:fwrite("],"),
    fr_print(T);
fr_print([H]) -> 
    fr_print(H);
fr_print([H|T]) -> 
    fr_print(H),
    io:fwrite(","),
    fr_print(T);
fr_print(X = <<_:256>>) -> 
    Y = fr:decode(X),
    P2 = fr:prime() div 2,
    Z = if 
        Y > P2 -> Y - fr:prime();
        true -> Y
        end,
    io:fwrite(integer_to_list(Z)).
            

test(0) ->
    A0 = range(100, 108),
    A = encode_list(lists:reverse(A0)),
    %A = A0,
    S = length(A),
    {G, H, Q} = basis(S),


    Bv = encode_list([10,0,3,1,1,2,0,10]),%103+104 = 207
    Bv2 = encode_list([1000000000000,0,0,0,0,0,0,10000000]),%100+105 = 205
    io:fwrite("test 1 0 \n"),
    Proof = make_ipa(
              A, Bv,%103+104 = 207
              G, H, Q),
    Proof;
%rp(ipa:base64_tree(ipa:test(0))).
test(1) ->

    A0 = range(100, 108),
    A = encode_list(lists:reverse(A0)),
    %A = A0,
    S = length(A),
    {G, H, Q} = basis(S),


    Bv = encode_list([10,0,3,1,1,2,0,10]),%103+104 = 207
    Bv2 = encode_list([1000000000000,0,0,0,0,0,0,10000000]),%100+105 = 205
    io:fwrite("test 1 0 \n"),
    Proof = make_ipa(
              A, Bv,%103+104 = 207
              G, H, Q),
    io:fwrite("test 1 1 \n"),
%    io:fwrite({Proof, Bv}), %{point point list point point} list

    {_, AB, _, _, _} = Proof,
    %io:fwrite(fr:decode(AB)), %2796
    %io:fwrite(base64:encode(ed:compress_point(mul(AB, Q)))),
    %1=2,
    true = verify_ipa(Proof, Bv, G, H, Q),
    %N207 = fr:encode(207),
    %{_, N207, _, _, _} = Proof,
    io:fwrite("test 1 3 \n"),
    Proof2 = make_ipa(
              A, Bv2,
              G, H, Q),
%    io:fwrite({size(hd(A)), length(A), size(hd(Bv2)), length(Bv2)}),%32, 8, 32, 8
    %100 = fr:decode(element(2, Proof2)),
    io:fwrite("test 1 4 \n"),
    true = verify_ipa(Proof2, Bv2, G, H, Q),
    success;
test(2) ->
    %comparing the speed between versions
    A = encode_list(range(100, 356)),
    %A = range(100, 132),
    S = length(A),
    {G, H, Q} = basis(S),
    B = encode_list(range(200, 200 + length(A))),
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
%     {verify, timer:now_diff(T6, T5)}%   9816297
};
%new version creates the proof 4.5x faster, and verifies 6x faster.

test(3) ->
    %testing compression.
    A = encode_list(range(100, 108)),
    S = length(A),
    {G, H, Q} = basis(S),
    Bv = encode_list([0,0,0,1,1,0,0,0]),%103+104 = 207
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
    {Gs, _, _} = parameters:read(),
    Many = 10,
    V = lists:map(fun(_) ->
                          <<R:256>> = 
                              crypto:strong_rand_bytes(32),
                          fr:encode(R)
                  end, range(0, 256)),
    256 = length(V),
    MEP = parameters:multi_exp(),
    T1 = erlang:timestamp(),
    lists:map(fun(_) ->
                      commit(V, Gs)
              end, range(0, Many)),
    T2 = erlang:timestamp(),
    lists:map(fun(_) ->
                          store:precomputed_multi_exponent(V, MEP)
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
    success;
test(6) ->
     A0 = [6557398279811269422222260660686945123758959220525701212948355841020816233267,
     3705093086744360691065964547167704750793463218034549685405621849768160725598],
    A0 = fr:decode(fr:encode(A0)),
    %A = fr:encode(A0),
    %A0 = fr:decode(A),
    
    %if it has more than 74 characters, then it breaks. fr encoded has like 77 characters, so this doesn't work.
    A0a = [%10,20,30,40,
           %50,60,70, %10],
           1,2,3,4,5,6,7,8,
           %100510237808490508376962983701062532245597166313109197768658377164801760055,
           %100510237808490508376962983701062532245597166313109197768658377164801760055,
           100530237808490508376962983701062532245597166313109197768658377164801760055,

           %200990237808490508376962983701062532245597166313109197768658377164801760055,
           %201590237808490508376962983701062532245597166313109197768658377164801760055,
           %201590237808490508376962983701062532245597166313109197768658377164801760055],
           5,
           %328490237808490508376962983701062532245597166313109197768658377164801760055,
           6,7,
           1,2,3,4
],
%900000000000000000000000000000000000000000000],
    A0a = fr:decode(fr:encode(A0a)),
    %if there are more than 32 digits, it breaks...
    A = encode_list(A0a),
    %A0a = fr:decode(A),
    B0b = [
           1,2,3,4,5,6,7,8,
           8,7,6,5,
           4,3,2, 1],
    %31552620236409682111491181490461037455464059572158722099773680689245815623],
    
           %3155262023640968211149118149046103745546405957215872209977368068924581562391],
    B0b = fr:decode(fr:encode(B0b)),
    B = fr:encode(B0b),
    %io:fwrite({B0b, B0}),
    S = length(A),
    {G, H, Q} = basis(S),
    Proof = make_ipa(A, B, G, H, Q),
    true = verify_ipa(Proof, B, G, H, Q),
    success;
test(7) ->
    %B = fr:encode([1, fr:prime() * 8 div 17]),
    B = fr:encode([1, fr:prime() -2]),
    %fr_print(B),
    %io:fwrite("\n"),
    A = fr:encode([1, 1]),
    %B = fr:encode([2,fr:prime() div 32, fr:prime() div 16, fr:prime() div 16]),
    %A = fr:encode([2, 3, 1, 1]),
    
    S = length(A),
    {G, H, Q} = basis(S),
    Proof = make_ipa(A, B, G, H, Q),
    true = verify_ipa(Proof, B, G, H, Q),
    success.

base64_tree(T) when is_tuple(T) ->
    L = tuple_to_list(T),
    L2 = base64_tree(L),
    list_to_tuple(L2);
base64_tree([]) -> [];
base64_tree([H|T]) ->
    [base64_tree(H)|
     base64_tree(T)];
base64_tree(B) when is_binary(B) ->
    base64:encode(B);
base64_tree(B) when is_integer(B)->
    B.


    
