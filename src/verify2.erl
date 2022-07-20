-module(verify2).
-export([proof/3, update/3, remove_empty/1,
         test/0
         %update_proof/3 %update_proofs/2, unfold/4
        ]).
-include("constants.hrl").


update([OldRoot|ProofTree], Leaves, CFG) ->
    %walk down the tree, then update everything in reverse in the callback stack.
    %Leaves2 = store2:sort_by_path2(Leaves, CFG),
    MEP = parameters2:multi_exp(),
    {Diff, Tree2} = 
        update_batch2(Leaves, ProofTree,
                      0, CFG, MEP),
    NewRoot = case Diff of
                  0 -> OldRoot;
                  _ -> fq:e_add(Diff, OldRoot)
              end,
    [NewRoot|Tree2].

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
    EllDiff = store2:precomputed_multi_exponent(
                Diffs, MEP),
    {EllDiff, Tree2}.

%for testing only.
remove_empty([[]|T]) ->
    remove_empty(T);
remove_empty([0|T]) ->
    remove_empty(T);
remove_empty([<<0:256>>|T]) ->
    remove_empty(T);
remove_empty([H|T]) ->
    [H|remove_empty(T)];
remove_empty([]) -> [].


update_merge([], Rest, _,_,_, Merged, Diffs, _)
->
    %finished updating this stem.
    Subtrees = lists:reverse(Merged) ++ Rest,
    {lists:reverse(Diffs), Subtrees};
update_merge([[]|Leaves], [], 
             _, _, _, R, Diff, _) ->
    %the proof ended, so there is nothing left to update. checking that we aren't trying to update anyting else.
    update_merge(Leaves, [], ok, ok, ok, 
                 R, [<<0:256>>|Diff], ok);
update_merge([[]|Leaves], 
             Tree = [[{N, _}|_]|SubTree], Depth, 
             CFG, MEP, R, Diff, N) ->
    %not changing this element that is recorded in our proof. 
    update_merge(
      Leaves, SubTree, Depth, CFG, MEP,
      [hd(Tree)|R], [<<0:256>>|Diff], N+1);
update_merge([LH|Leaves], 
             Subtrees = [[{M, _}|_]|_], Depth, 
             CFG, MEP, R, Diff, N) 
  when (not(M == N)) ->
    %this part is not recorded in our proof, it cannot be changed.
    %verify that we are not trying to change it.
    if
        not(LH == []) ->
            io:fwrite("verkls2 error. tried to edit inaccessible state."),
            io:fwrite({LH, N, M, Subtrees});
        true -> ok
    end,
    update_merge(Leaves, 
                 Subtrees, Depth, CFG, MEP, R, 
                 [<<0:256>>|Diff], N+1);
update_merge([LH|Leaves], [[{N, B}|S1]|Subtrees], 
             Depth, CFG, MEP, R, Diffs, N) 
  when is_binary(B) ->
    %adding one or more leaves to an existing stem.

    {Point, Tree2} = 
        update_batch2(LH, S1, Depth+1, CFG, MEP),
    {NewPoint, Diff} = 
        case Point of
            0 -> {B, <<0:256>>};
            _ ->
                NewPoint0 = fq:e_add(B, Point),
                NewN = stem2:hash_point(NewPoint0),
                OldN = stem2:hash_point(B),
                {NewPoint0, fr:sub(NewN, OldN)}
    %io:fwrite("merging stems diff calculation.\n"),
        end,
    update_merge(Leaves, Subtrees, Depth, CFG, MEP,
                 [[{N, NewPoint}|Tree2]|R], 
                 [Diff|Diffs], N+1);
update_merge([[{K, 0}]|Leaves], 
             [[{N, {OldK, OldV}}]|Subtrees],
             Depth, CFG, MEP, R, Diffs, N) ->
    %deleting a leaf.
    io:fwrite("deleting a leaf"),
    OldLeaf = leaf:new(OldK, OldV, 0, CFG),
    OldN = store2:leaf_hash(OldLeaf, CFG),
    update_merge(Leaves, Subtrees, Depth, CFG, MEP,
                 [{N, 0}|R], 
                 [fr:neg(OldN)|Diffs], N);
update_merge([LH|Leaves], 
             [[{N, {Key, Value}}]|Subtrees], 
             Depth, CFG, MEP, R, Diffs, N) ->
    %io:fwrite("add a leaf to a spot with an existing leaf\n"),
    %there is already a leaf here.
    %NewLeaf = leaf:new(Key, Value, 0, CFG),
    FL = leaf:new(Key, Value, 0, CFG),
                     
    B = leaf_in_list(FL, LH),
    B2 = (1 == length(LH)),
    if
        (B and B2) -> 
            %io:fwrite(LH),
            Leaf2 = hd(LH),
            OldN = store2:leaf_hash(
                     FL, CFG),
            NewN = store2:leaf_hash(
                     Leaf2, CFG),
            LeafDiff = 
                if
                    OldN == NewN -> 
                        %leaf unchanged.
                        io:fwrite("Leaf unchanged\n"),
                        <<0:256>>;
                        %fr:encode(0);
                    true ->
                        %io:fwrite("updating leaf diff calculation.\n"),
                        fr:sub(NewN, OldN)
                end,
            update_merge(
              Leaves, Subtrees, Depth, CFG, 
              MEP, [[{N, {leaf:key(Leaf2),
                          leaf:value(Leaf2)}}]|
                    R],
              [LeafDiff|Diffs], N+1);
        B -> 
            io:fwrite("adding leaves to a spot where there was a leaf, and changing the existing leaf\n"),
            update_merge(
              [LH|Leaves], 
              [[{N, 0}]
               |Subtrees],
              Depth, CFG, MEP, R, Diffs, N);
        true -> 
            %adding leaves to this spot where there was a leaf, without updating our leaf
            io:fwrite("adding a leaves to this spot where there is a leaf, and not changing the existing leaf\n"),
            update_merge(
              %[[NewLeaf|LH]|Leaves], 
              [[FL|LH]|Leaves], 
              [[{N, 0}]
               |Subtrees],
              Depth, CFG, MEP, R, Diffs, N)
    end;
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
    Key = leaf:key(hd(LH)),
    Value = leaf:value(hd(LH)),
    %#leaf{key = Key, value = Value} = hd(LH),
    io:fwrite("new leaf diff calculation\n"),
    Diff = store2:leaf_hash(hd(LH), CFG),
    %Diff = leaf:hash(hd(LH), CFG),
    update_merge(Leaves, Subtrees, Depth, CFG, 
                 MEP, [[{N, {Key, Value}}]|R], 
                 [Diff|Diffs], N+1);
update_merge(Ls, [X|T], Depth, CFG, MEP, R, Diffs, 
             N) when is_tuple(X)->
    update_merge(Ls, [[X|T]], Depth, CFG, MEP, R,
                 Diffs, N).


leaf_in_list(_, []) ->
    false;
leaf_in_list({K, 0}, 
             [#leaf{key = K}|_]) -> 
    true;
leaf_in_list(#leaf{key = K}, 
             [{K, 0}|_]) -> 
    true;
leaf_in_list(#leaf{key = K}, 
             [#leaf{key = K}|_]) -> 
    true;
leaf_in_list(Leaf, [_|T]) -> 
    leaf_in_list(Leaf, T).

merge_find_helper(P, D) ->
    io:fwrite("merge find helper\n"),
    case dict:find(P, D) of
	error -> P;
	{ok, error} -> 1=2;
	{ok, P2} ->
	    merge_find_helper(P2, D)
    end.

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
leaves(X = {_, B}) when is_binary(B) -> [];
leaves({_, X = {I, B}}) 
  when is_binary(B) and is_integer(I) -> [X];
leaves([H|T]) ->
    leaves(H) ++ leaves(T);
leaves([]) ->  [];
leaves(X) ->  
    %leaf getter error.
    io:fwrite({X}).
              

unfold(Root, {Index, 0}, T, CFG) ->%empty case
    lists:reverse([{Root, Index, <<0:256>>}|T]);
unfold(Root, {Index, {Key, B}}, T, CFG) %leaf case
  when is_binary(B) ->
    %Leaf = #leaf{key = Key, value = B},
    Leaf = leaf:new(Key, B, 0, CFG),
    <<L:256>> = store2:leaf_hash(Leaf, CFG),
    lists:reverse([{Root, Index, <<L:256>>}|T]);
unfold(Root, [{Index, X}|R], T, CFG) %stem case
  when (is_binary(X) and (size(X) == (32*5)))
   ->
    <<H:256>> = fq:hash_point(X),
    unfold(X, R, [{Root, Index, <<H:256>>}|T], CFG);
unfold(Root, [H|J], T, CFG) ->
    unfold(Root, H, T, CFG)
        ++ unfold(Root, J, [], CFG);
unfold(_, [], _, _) -> [].



test() ->
    CFG = trie:cfg(trie01),
    Leaves = [leaf:new(999999872, <<0,0>>, 0, CFG),
              leaf:new(999999744, <<0,0>>, 0, CFG)],
    Leaves2 = store2:clump_by_path(
                0, Leaves, CFG),
    %todo. each should have the same number of leaves.
    true = (length(remove_empty(Leaves))) ==
        (length(remove_empty(Leaves2))),
    success.
