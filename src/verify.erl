-module(verify).
-export([proof/3, update_proof/3, update_proofs/2]).
-include("constants.hrl").


update_proof(L, Proof, CFG) ->
    LP = leaf:path(L, CFG),
    %take the slice of the path we will use, and reverse it.
    N = length(Proof),
    {LP2, _} = lists:split(N, LP),
    LP3 = lists:reverse(LP2),
    LH = leaf:hash(L, CFG),
    Proof2 = update_internal(LP3, LH, Proof, CFG),
    Proof2.

update_internal(_, _, [], _) -> [];
update_internal([<<N:?nindex>> | M], LH, Proof, CFG) ->
    P1 = hd(Proof),
    %Hash = element(N+1, P1),
    P2 = setelement(N+1, P1, LH),
    io:fwrite({P2}),
    NH = stem:hash(P2),
    [P2|update_internal(M, NH, tl(Proof), CFG)].

update_proofs(X, CFG) ->
    update_proofs(X, CFG, dict:new(), []).
update_proofs([], _, D, L) ->
    L2 = lists:reverse(L),
    lists:map(fun(X) ->%do this to every list in the list of lists.
		      lists:map(fun(Y) ->%update every element of the list
					merge_find_helper(Y, D)

				end, X)
	      end, L2);
update_proofs([{Leaf, Proof}|T], CFG, D, L) ->
    %use D to remember which stems have been updated already.
    LP = leaf:path(Leaf, CFG),
    N = length(Proof),
    {LP2, _} = lists:split(N, LP),
    LP3 = lists:reverse(LP2),
    LH = leaf:hash(Leaf, CFG),
    {D2, NewProof} = update_proofs2(LP3, LH, Proof, D, CFG, []),
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
    D2 = dict:store(P1, P2, D),
    D3 = dict:store(P, P2, D),
    NH = stem:hash(P2),
    update_proofs2(M, NH, tl(Proof), D3, CFG, [P2|Proof2]).

proof(Tree, Proof = {CommitG, Commits0, Open}, CFG) ->

    %multiproof:verify(Proof = {CommitG, Commits, Open_G_E}, Zs, Ys, ?p)
    %Zs are elements of the domain where we look up stuff.
    %Ys are values stored in pedersen commits. either hashes of leaves, or hashes of stems.
    %io:fwrite({Tree, Commits0}),
    
    %[root, [{1, p1}, [{0, L1},{1, L2}], [{3, p2},{0,L3}]]]
    [Root|Rest] = Tree,
    Tree2 = unfold(Root, Rest, [], CFG),
    %[{elliptic, index, hash}, ...]
    %io:fwrite({Tree2}),
    {Commits, Zs0, Ys} = 
        get:split3parts(Tree2, [],[],[]),
    Zs = get:index2domain(Zs0, ?p#p.domain),
    Ys2 = lists:map(fun(<<X:256>>) -> X end,
                    Ys),
    Commits0 = Commits,
    true = multiproof:verify({CommitG, Commits, Open}, Zs, Ys2, ?p),
    
    %[p2, root, p1, p1, root] %commitments
    %[0,  3,    1,  0,  1]  %indices
    %[L3, p2,   L2, L1, p1] %unhashed ys
    true.

    %[{1, p1}, [{0, L1},{1, L2}], [{3, p2},{0,L3}]]
unfold(Root, {Index, X = {Key, B}}, T, CFG) %leaf case
  when is_binary(B) ->
    Leaf = #leaf{key = Key, value = B},
    <<L:256>> = leaf:hash(Leaf, CFG),
    lists:reverse([{Root, Index, <<L:256>>}|T]);
%unfold(Root, {Index, X ={_, _, _}}, T, CFG) %point case
%   ->
%    H = secp256k1:hash_point(X),
%    [{Root, Index, <<H:256>>}|T];
unfold(Root, [{Index, X ={_, _, _}}|R], T, CFG) %point case
   ->
    %[{Root, Index, X}|T];
    H = secp256k1:hash_point(X),
    unfold(X, R, [{Root, Index, <<H:256>>}|T], CFG);
%unfold(Root, [[{Index, X = {_, _, _}}|P]|J], T) -> 
%    T2 = [{Root, Index, X}|T],
%    unfold(X, P, T2)
%        ++ unfold(Root, J, T);
unfold(Root, [H|J], T, CFG) ->
    unfold(Root, H, T, CFG)
        ++ unfold(Root, J, [], CFG);
unfold(Root, [], _, _) -> [].

    



%    Paths0 = lists:map(fun(L) -> leaf:path(L, CFG)
%                      end, Leaves),
%    Paths = lists:map(
%             fun(Path) ->
%                     lists:map(
%                       fun(<<P:?nindex>>) ->
%                               P end, Path)
%             end, Paths0),
%    Tree = get:paths2tree(Paths),
%    Zs0 = flatten(Tree, Structure, []),
%    Zs = get:index2domain(Zs0, ?p#p.domain),
%    io:fwrite({Root, Commits0}).
   


 
    %io:fwrite({RootHash}),
    %io:fwrite({length(Leaves), length(Commits), length(Zs),
    %          Leaves, Structure, Tree}).

    %need to show that roothash is the hash of 
%    Commits = lists:reverse(Commits0),
%    RH2 = stem:hash_point(hd(Commits)),
%    if
%        (RootHash == RH2) ->%check that the proof connects to this root hash.
%            proof_loop(leaf:path(Leaf, CFG),
%                       Leaf, Commits, CFG);
%        true ->

%%	    io:fwrite("false 1\n"),
%	    false
%proof_loop([<<N:?nindex>> | R], Leaf, P, CFG) 




 
unpack_tree([H|T], Acc, _) when is_integer(H) ->
    unpack_tree(T, [H|Acc], integers);
unpack_tree([H|T], Acc, _) ->
    unpack_tree(H, Acc, 0) ++ 
        unpack_tree(T, Acc, lists);
unpack_tree([], Acc, integers) -> 
    [lists:reverse(Acc)];
unpack_tree([], Acc, lists) -> [].
%unpack_tree([], Acc, 0) -> 
    

flatten(Tree, Structure, X) ->
    Tree2 = unpack_tree(Tree, [], 0),
    Tree3 = lists:zipwith(
              fun(L, S) ->
                      {A, _} = lists:split(S, L),
                      A
              end, Tree2, Structure),
    lists:foldl(fun(A, B) -> B ++ A end,
                [], Tree3).
 
flatten([]) -> [];
flatten([H|T]) when is_list(H) -> 
    flatten(H) ++ flatten(T);
flatten([H|T]) when is_integer(H) -> 
    [H|flatten(T)].

proof_old(RootHash, L, Proof, CFG) ->
    [H|F] = lists:reverse(Proof),
    %[H|F] = Proof,
    SH = stem:hash_point(H),
    if
	SH == RootHash ->
	    proof_internal(leaf:path(L, CFG), L, [H|F], CFG);
	true -> 
	    io:fwrite("false 1\n"),
	    false
    end.

proof_internal([<<N:?nindex>> | M], Leaf, P, CFG) when length(P) == 1->
    P1 = hd(P),
    Hash = element(N+1, P1),
    V = leaf:value(Leaf),
    LH = leaf:hash(Leaf, CFG),
    Hash == LH;
proof_internal([<<N:?nindex>>| Path ], Leaf, [P1, P2 | Proof], CFG) ->
    %if leaf is empty, and P2 is a leaf, then we do a different test.
    %pass if hash(leaf) is in P1, and N does _not_ point to leaf P2.
    LB = leaf:is_serialized_leaf(P2, CFG),
    LV = leaf:value(Leaf),
    if
	(LV == empty) and LB ->
	    Leaf2 = leaf:deserialize(P2, CFG),
	    LH = leaf:hash(Leaf2, CFG),
	    is_in(LH, tuple_to_list(P1)) 
		and not(get:same_end(leaf:path(Leaf2, CFG), 
				     [<<N:?nindex>>|Path], 
				     CFG));
	true ->
	    %Hash = element(N+1, P1),
            %Hash = 
	    case stem:hash_point(P2) of
		Hash -> proof_internal(Path, Leaf, [P2 | Proof], CFG);
		X ->
		    io:fwrite("false 3\n"),
		    %io:fwrite({X, Hash, [P1, P2|Proof]}),
		    false
	    end
    end;
proof_internal(_, _, _, _) ->
    io:fwrite("false 2\n"),
    false.
is_in(X, []) -> false;
is_in(X, [X|_]) -> true;
is_in(X, [A|T]) -> is_in(X, T).
