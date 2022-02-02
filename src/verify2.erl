-module(verify2).
-export([proof/3%, 
         %update_proof/3, update_proofs/2, unfold/4
        ]).
-include("constants.hrl").


update_proof(L, Proof, CFG) ->
    LP = leaf:path(L, CFG),
    %take the slice of the path we will use, and reverse it.
    N = length(Proof),
    {LP2, _} = lists:split(N, LP),
    LP3 = lists:reverse(LP2),
    %LH = leaf:hash(L, CFG),
    LH = store2:leaf_hash(L, CFG),
    Proof2 = update_internal(LP3, LH, Proof, CFG),
    Proof2.

update_internal(_, _, [], _) -> [];
update_internal([<<N:?nindex>> | M], LH, Proof, CFG) ->
    P1 = hd(Proof),
    %Hash = element(N+1, P1),
    P2 = setelement(N+1, P1, LH),
    io:fwrite({P2}),
    NH = stem2:hash(P2),
    [P2|update_internal(M, NH, tl(Proof), CFG)].

update_proofs(X, CFG) ->
    update_proofs(X, CFG, dict:new(), []).
update_proofs([], _, D, L) ->
    L2 = lists:reverse(L),
    lists:map(
      fun(X) ->%do this to every list in the list of lists.
              lists:map(
                fun(Y) ->%update every element of the list
                        merge_find_helper(Y, D)
                            
                end, X)
      end, L2);
update_proofs([{Leaf, Proof}|T], CFG, D, L) ->
    %use D to remember which stems have been updated already.
    LP = leaf:path(Leaf, CFG),
    N = length(Proof),
    {LP2, _} = lists:split(N, LP),
    LP3 = lists:reverse(LP2),
    %LH = leaf:hash(Leaf, CFG),
    LH = store2:leaf_hash(Leaf, CFG),
    {D2, NewProof} = 
        update_proofs2(LP3, LH, Proof, D, CFG, []),
    update_proofs(T, CFG, D2, [NewProof|L]).
    
merge_find_helper(P, D) ->
    io:fwrite("merge find helper\n"),
    case dict:find(P, D) of
	error -> P;
	{ok, error} -> 1=2;
	{ok, P2} ->
	    merge_find_helper(P2, D)
    end.

update_proofs2(_, _, [], D, _, Proof) -> 
    {D, lists:reverse(Proof)};
update_proofs2([<<N:?nindex>>|M], LH, Proof, D, CFG, Proof2) -> 
    P1 = hd(Proof),
    P = merge_find_helper(P1, D),
    P2 = setelement(N+1, P, LH),
    %D2 = dict:store(P1, P2, D),
    D3 = dict:store(P, P2, D),
    NH = stem2:hash(P2),
    update_proofs2(M, NH, tl(Proof), D3, CFG, [P2|Proof2]).

%proof(Tree, Proof = {CommitG, Commits0, Open}, CFG) ->
proof(Root0, {Tree, CommitG, Open}, CFG) ->

    %multiproof:verify(Proof = {CommitG, Commits, Open_G_E}, Zs, Ys, ?p)
    %Zs are elements of the domain where we look up stuff.
    %Ys are values stored in pedersen commits. either hashes of leaves, or hashes of stems.
    %io:fwrite({Tree, Commits0}),
    
    %[root, [{1, p1}, [{0, L1},{1, L2}], [{3, p2},{0,L3}]]]
    io:fwrite("verify get parameters \n"),
    [Root|Rest] = Tree,
    %P = parameters:read(),
    Domain = parameters2:domain(),
    %B = secp256k1:jacob_equal(Root0, Root, ?p#p.e),
    B = fq2:eq(Root0, Root),
    if
        not(B) -> false;
        true ->
            io:fwrite("verify2 unfold \n"),
            benchmark:now(),
            %io:fwrite({Root, Rest}),
            %rest [[{251, {999995, <<0,1>>}}],
            %      [[{252, {999996, <<0,2>>}}],
            Tree2 = unfold(Root, Rest, [], CFG),
    %[{elliptic, index, hash}, ...]
            io:fwrite("verify split 3 parts \n"),
            benchmark:now(),
            {Commits, Zs0, Ys} = 
                get2:split3parts(Tree2, [],[],[]),
            io:fwrite("veirfy index2domain \n"),
            benchmark:now(),
            Zs = get2:index2domain(
                   %Zs0, ?p#p.domain),
                   Zs0, Domain),
            %io:fwrite({Zs}),%[1,4,1,3,2,1,2]
            %io:fwrite({Commits}),%[17,10,10,88,35,35,88]
            %should be [17,88,10,88,35,35,88]
            io:fwrite("verify multiproof \n"),
            benchmark:now(),
            B2 = multiproof2:verify(
                   {CommitG, Open}, 
                   Commits, Zs, fr:decode(Ys)),

            %sanity check
            %element(2, Open) = -G2

            io:fwrite("verify done \n"),
            benchmark:now(),
            if
                not(B) -> false;
                not(B2) -> false;
                true ->
                    {true, leaves(Rest)}
                    %get all the leaves
                        %ok
            end
    end.
    
    %[p2, root, p1, p1, root] %commitments
    %[0,  3,    1,  0,  1]  %indices
    %[L3, p2,   L2, L1, p1] %unhashed ys

    %[{1, p1}, [{0, L1},{1, L2}], [{3, p2},{0,L3}]]
leaves({_, X = {_, B}}) when is_binary(B) -> [X];
leaves([H|T]) ->
    leaves(H) ++ leaves(T);
leaves(_) ->  [].

unfold(Root, {Index, {Key, B}}, T, CFG) %leaf case
  when is_binary(B) ->
    Leaf = #leaf{key = Key, value = B},
    <<L:256>> = store2:leaf_hash(Leaf, CFG),
    lists:reverse([{Root, Index, <<L:256>>}|T]);
%unfold(Root, {Index, X ={_, _, _}}, T, CFG) %point case
%   ->
%    H = secp256k1:hash_point(X),
%    [{Root, Index, <<H:256>>}|T];
unfold(Root, [{Index, X}|R], T, CFG) %stem case
  when (is_binary(X) and (size(X) == (32*5)))
   ->
    %[{Root, Index, X}|T];
    <<H:256>> = fq2:hash_point(X),
    unfold(X, R, [{Root, Index, <<H:256>>}|T], CFG);
%unfold(Root, [[{Index, X = {_, _, _}}|P]|J], T) -> 
%    T2 = [{Root, Index, X}|T],
%    unfold(X, P, T2)
%        ++ unfold(Root, J, T);
unfold(Root, [H|J], T, CFG) ->
    unfold(Root, H, T, CFG)
        ++ unfold(Root, J, [], CFG);
unfold(_, [], _, _) -> [].