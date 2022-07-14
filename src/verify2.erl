-module(verify2).
-export([proof/3, update/3
         %update_proof/3 %update_proofs/2, unfold/4
        ]).
-include("constants.hrl").


update([OldRoot|ProofTree], Leaves, CFG) ->
    %walk down the tree, then update everything in reverse in the callback stack.
    Leaves2 = store2:sort_by_path2(Leaves, CFG),
    MEP = parameters2:multi_exp(),
    {Diff, Tree2} = 
        update_batch2(Leaves, ProofTree,
                      0, CFG, MEP),
    [fq:e_add(Diff, OldRoot)|Tree2].

empty_stem() ->
    [].

%leaves are made with leaf:new/4
update_batch2([], Tree, _Depth, _CFG, _MEP) 
->
    {0, Tree};
update_batch2(Leaves, Tree,
              Depth, CFG, MEP) ->
    %adding leaves to an existing stem.
    Leaves2 = store2:clump_by_path(
                Depth, Leaves, CFG),
    {Diffs, Tree2} = 
        update_merge(Leaves2, 
                     Tree, Depth, CFG, MEP, 
                     [], [], 0),
    256 = length(Leaves2),
    256 = length(Diffs),
    %diffs can contain zeros, for empty slots.

    %todo. this is crashing the precompute. format must be wrong somehow.

    EllDiff = store2:precomputed_multi_exponent(
                Diffs, MEP),
    {EllDiff, Tree2}.



%update_batch3(Leaves,
%              Tree = [{N, {Key, Value}},
%              Depth, CFG, MEP) ->
    %mixing new leaves with an existing leaf.
%    NewLeaf = leaf:new(Key, Value, 0, CFG),
    %creates a new stem
%    update_batch2([NewLeaf|Leaves], Root,
%                  [{N, fq:e_zero()}], 
%                  Depth, CFG, MEP);
%update_batch3(Leaves, Tree = {N, 0},
%              Depth, CFG, MEP) ->
    %adding leaves to an empty spot. 
    %creates a new stem
%    update_batch3(Leaves, [{N, fq:e_zero()}],
%                  Depth, CFG, MEP);
%update_batch3([L = #leaf{}], Tree = {N, 0},
%              Depth, CFG, MEP) ->
    %storing a leaf into an empty spot.
%    {N, {L#leaf.key, L#leaf.value}}.


update_merge([], Rest, _,_,_, Merged, Diffs, _) ->
    %finished updating this stem.
    Subtrees = lists:reverse(Merged) ++ Rest,
    {lists:reverse(Diffs), Subtrees};
update_merge([[]|Leaves], [], 
             _, _, _, R, Diff, _) ->
    update_merge(Leaves, [], ok, ok, ok, 
                 R, [0|Diff], ok);
update_merge([[]|Leaves], 
             Tree = [[{N, _}|_]|SubTree], Depth, 
             CFG, MEP, R, Diff, N) ->
    %not changing this element that is recorded in our proof.
    update_merge(Leaves, SubTree, Depth, CFG, MEP,
                 [hd(Tree)|R], [0|Diff], N+1);
update_merge([LH|Leaves], 
             Subtrees = [[{M, _}|_]|_], Depth, 
             CFG, MEP, R, Diff, N) 
  when (not(M == N)) ->
    %this part is not recorded in our proof, it cannot be changed.
    if
        not(LH == []) ->
            io:fwrite({LH, N, M, Subtrees});
        true -> ok
    %verify that we are not trying to change it.
    end,
    update_merge(Leaves, 
                 Subtrees, Depth, CFG, MEP, R, 
                 [0|Diff], N+1);
update_merge([LH|Leaves], [[{N, B}|S1]|Subtrees], 
             Depth, CFG, MEP, R, Diffs, N) 
  when is_binary(B) ->
    %io:fwrite({N, Leaves, Subtrees}),
    {Point, Tree2} = 
        update_batch2(LH, S1, Depth+1, CFG, MEP),
    New = stem2:hash_point(Point),
    Diff = fr:sub(New, stem2:hash_point(B)),
    update_merge(Leaves, Subtrees, Depth, CFG, MEP,
                 [Tree2|R], [Diff|Diffs], N+1);
update_merge([LH|Leaves], 
             [[{N, {Key, Value}}]|Subtrees], 
             Depth, CFG, MEP, R, Diffs, N) ->
    %there is already a leaf here.
    NewLeaf = leaf:new(Key, Value, 0, CFG),
    B = leaf_in_list(NewLeaf, LH),
    L2 = if
             B -> LH;
             true -> [NewLeaf|LH]
         end,
    update_merge(
      [L2|Leaves], 
      [[{N, 0}]
       |Subtrees],
      Depth, CFG, MEP, R, Diffs, N);
update_merge([LH|Leaves],
             [[{N, 0}]|Subtrees],
             Depth, CFG, MEP, R, Diffs, N) 
  when (length(LH) > 1) ->
    update_merge([LH|Leaves],
                 [[{N, fq:e_zero()}]|Subtrees],
                 Depth, CFG, MEP, R, Diffs, N);
update_merge([LH|Leaves],
             [[{N, 0}]|Subtrees],
             Depth, CFG, MEP, R, Diffs, N) ->
    #leaf{key = Key, value = Value} = hd(LH),
    Diff = store2:leaf_hash(hd(LH), CFG),
    update_merge(Leaves,
                 Subtrees,
                 Depth, CFG, MEP, 
                 [[{N, {Key, Value}}]|R], 
                 [Diff|Diffs], N+1).

    
    %todo.
    %new_hash. <<0:256>> is for empty. store2:leaf_hash(L, CFG) or stem2:hash(S)
    %diff = fr:sub(new_hash, old_hash)

    %EllDiff = store2:precomputed_multi_exponent(
    %            Diffs, MEP),
    %NewRoot = fq:e_add(EllDiff, Root),

    
leaf_in_list(_, []) ->
    false;
leaf_in_list(#leaf{key = K}, 
             [#leaf{key = K}|_]) -> 
    true;
leaf_in_list(Leaf, [_|T]) -> 
    leaf_in_list(Leaf, T).

    

update_batch([], 0, _, _, _, _) -> 
    %type 0 is empty
    {0,0,empty};
update_batch([], P, leaf, _, _, _) -> 
    {P, leaf, leaf_not_recorded};
update_batch([], P, stem, _, _, _) -> 
    {P, stem, stem_not_recorded};
update_batch([Leaf], 0, 0, _, CFG, _) ->
    %storing a leaf in a previously empty spot.
    {Leaf, leaf};
update_batch(Leaves, 0, 0, Depth, CFG, MEP) ->
    %storing multiple leaves in a previously empty spot.
    update_batch(Leaves, empty_stem(), stem, 
                 Depth, CFG, MEP);
update_batch(Leaves, Tree, leaf, Depth, CFG, MEP) 
->
    %storing new leaves in a spot that previously had a leaf.
    update_batch([Tree|Leaves], empty_stem(), stem,
                 Depth, CFG, MEP);
update_batch(Leaves, Tree, stem, Depth, CFG, MEP) 
->
    %storing leaves in an existing stem.
    Leaves2 = store2:clump_by_path(
                Depth, Leaves, CFG),
    lists:map(fun(Clump) ->
                      {P, Type, Tree2} = 
                          update_batch(Clump,  ok, ok, ok, ok, ok),
                      ok
              end, Leaves2),
    %todo
    %for each thing we are changing.
    %new_hash. <<0:256>> is for empty. store2:leaf_hash(L, CFG) or stem2:hash(S)
    
    %diff = fr:sub(new_hash, old_hash)
    %EllDiff = store2:precomputed_multi_exponent(
    %            Diffs, MEP),
    %NewRoot = fq:e_add(EllDiff, Root),
    io:fwrite("todo, copying from store2:batch"),
    ok;
update_batch([], P, _, _, _, _) -> P;
update_batch([Leaf], 0, 0, _, CFG, _) -> 
    ok. 
    




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
    B = fq:eq(Root0, Root),
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
                    %io:fwrite({Rest}),
                    {true, leaves(Rest)}
                    %get all the leaves
                        %ok
            end
    end.
    
    %[p2, root, p1, p1, root] %commitments
    %[0,  3,    1,  0,  1]  %indices
    %[L3, p2,   L2, L1, p1] %unhashed ys

    %[{1, p1}, [{0, L1},{1, L2}], [{3, p2},{0,L3}]]
leaves({Y, X = 0}) -> [{Y, X}];
leaves({_, X = {_, B}}) when is_binary(B) -> [X];
leaves([H|T]) ->
    leaves(H) ++ leaves(T);
leaves(_) ->  [].

unfold(Root, {Index, 0}, T, CFG) ->%empty case
    lists:reverse([{Root, Index, <<0:256>>}|T]);
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
    <<H:256>> = fq:hash_point(X),
    unfold(X, R, [{Root, Index, <<H:256>>}|T], CFG);
%unfold(Root, [[{Index, X = {_, _, _}}|P]|J], T) -> 
%    T2 = [{Root, Index, X}|T],
%    unfold(X, P, T2)
%        ++ unfold(Root, J, T);
unfold(Root, [H|J], T, CFG) ->
    unfold(Root, H, T, CFG)
        ++ unfold(Root, J, [], CFG);
unfold(_, [], _, _) -> [].
