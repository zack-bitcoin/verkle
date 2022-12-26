-module(verify_verkle).
-export([proof/2, update/3, remove_empty/1,
         test/0
        ]).
-include("constants.hrl").

fill_points(Points, [], Result) -> 
    {lists:reverse(Result), Points};
fill_points(Ps, [T|R], Result) when is_list(T) ->
    {T2, Ps2} = fill_points(Ps, T, []),
    fill_points(Ps2, R, [T2|Result]);
fill_points([P|PT], [{I, <<_:256>>}|R], Result) 
  when is_integer(I) ->
    fill_points(PT, R, [{I, P}|Result]);
fill_points([P|PT], [<<_:256>>|R], Result) ->
    fill_points(PT, R, [P|Result]);
fill_points(Ps, [T|R], Result) ->
    fill_points(Ps, R, [T|Result]).

update(PL = [OldRoot|ProofTree], Leaves, CFG) ->
    %walk down the tree, then update everything in reverse in the callback stack.

    MEP = parameters:multi_exp(),
    {Diff, Tree2} = 
        update_batch2(Leaves, tl(PL),
                      0, CFG, MEP),
    NewRoot = case Diff of
                  0 -> OldRoot;
                  %_ -> fq:e_add(Diff, OldRoot)
                  _ -> 
                      %io:fwrite({size(Diff), size(OldRoot)}),%{128, 32}
                      ed:e_add(Diff, OldRoot)
              end,
    [NewRoot|Tree2].

empty_stem() ->
    [].

%leaves are made with leaf_verkle:new/4
update_batch2([], Tree, _Depth, _CFG, _MEP) ->
    {0, Tree};
update_batch2(Leaves, Tree, Depth, CFG, MEP) ->
    %adding leaves to an existing stem.
    Leaves2 = store_verkle:clump_by_path(
                Depth, Leaves),
    %io:fwrite({Tree, Leaves2}),
    %tree is like [[{1, 0}],[{5,leaf}]]
    %leaves is like [[],[leaf, leaf],[],[],[],...]length 256
    {Diffs0, Tree2} = 
        update_merge(Leaves2, 
                     Tree, Depth, CFG, MEP, 
                     [], [], 0),
    %Diffs0 [<<fr:256>>, <<fr:256>>, {sub, <<El:1280>>, <<fr:32>>}, <<fr:256>>, ...]
    %Diffs is length 256 [<<fr:256>>, ...]
    %tree is like [{45, 0},{62, 0},{234,0}], if we have a bunch of empty slots.
    SubPoints = sub_points(Diffs0),
    Es = lists:map(fun({sub, X, _}) -> X end, 
                   SubPoints),
    Cs = stem_verkle:hash_points(Es),
    ECs = lists:zipwith(fun(A, B) -> {A, B} end,
                        Es, Cs),
    ECdict = 
        lists:foldl(fun({Key, Value}, A) -> 
                            dict:store(
                              Key, Value, A) 
                    end, dict:new(), ECs),
    {_, Tree3} = insert_stem_hashes2(ECdict, Tree2, []),
    %Diffs = calc_subs(Diffs0, Cs),
    Diffs = calc_subs(Diffs0, Es),
    %EllDiff = store_verkle:precomputed_multi_exponent(
    EllDiff = precomputed_multi_exponent:doit(
                Diffs, MEP),
    {EllDiff, Tree3}.

insert_stem_hashes2([], Tree, Result) ->
    %{[], [lists:reverse(Result)|Tree]};
    {[], lists:reverse(Result) ++ Tree};
insert_stem_hashes2(ECs, [], Result) ->
    {ECs, lists:reverse(Result)};
insert_stem_hashes2(
  ECs, [{I, P = <<_:1024>>}|T], 
  Result) ->
    D = case dict:find(P, ECs) of
            {ok, C} -> 
                %io:fwrite("insert stem update point\n"),
                C;
            _ -> P
        end,
    insert_stem_hashes2(
      ECs, T, [{I, D}|Result]);
    
insert_stem_hashes2(
  ECs, [{I, {mstem, uncalculated, E}}|T], 
  Result) ->
    %{C, ECs2} = get_remove(E, ECs, []),
    {ok, C} = dict:find(E, ECs),
    insert_stem_hashes2(
      ECs, T, [{I, {mstem, C, E}}|Result]);
insert_stem_hashes2(ECs, [H|T], Result) ->
    {ECs2, H2} = insert_stem_hashes2(ECs, H, []),
    insert_stem_hashes2(ECs2, T, [H2|Result]);
    %insert_stem_hashes2(ECs2, T, H2 ++ Result);
%insert_stem_hashes2(ECs, Tree = {_I, {_K, _V, _M}}, 
insert_stem_hashes2(ECs, Tree = {_I, {_K, _V}}, 
                    []) ->
    {ECs, Tree};
insert_stem_hashes2(ECs, Tree = {_I, {_K, _V, _M}}, 
                    []) ->
    {ECs, Tree};
insert_stem_hashes2(
  ECs, Tree = {I, {mstem, _, _}}, []) ->
    {ECs, Tree};
insert_stem_hashes2(ECs, Tree = {I, 0}, []) ->
    {ECs, Tree};
insert_stem_hashes2(_, Tree, _) ->
    io:fwrite("verify corrupted tree\n"),
    io:fwrite(Tree).
    


insert_stem_hashes([], T) -> T;
insert_stem_hashes(_, []) -> [];
insert_stem_hashes(ECs, [{I, {mstem, uncalculated, E}}|T]) ->
    {C, ECs2} = get_remove(E, ECs, []),
    [{I, {mstem, C, E}}|
     insert_stem_hashes(ECs2, T)];
insert_stem_hashes(ECs, [H|T]) ->
    [insert_stem_hashes(ECs, H)|
     insert_stem_hashes(ECs, T)];
insert_stem_hashes(_, X) -> X.

get_remove(Key, [{Key, Value}|L], Rest) ->
    {Value, L ++ Rest};
get_remove(Key, [H|L], Rest) ->
    get_remove(Key, L, [H|Rest]).

    
            


    

calc_subs(Diffs, []) ->
    Diffs;
calc_subs([{sub, _, Fr}|T], [Compressed|CT]) ->
    [fr:sub(stem_verkle:hash_point(Compressed), Fr)|
     calc_subs(T, CT)];
calc_subs([H|T], Cs) ->
    [H|calc_subs(T, Cs)].


sub_points([]) -> [];
sub_points([X = {sub, E, Fr}|T]) -> 
    [X|sub_points(T)];
sub_points([X|T]) -> 
    sub_points(T).

update_merge([], Rest, _,_,_, Merged, Diffs, _) ->
    %finished updating this stem.
    Subtrees = lists:reverse(Merged) ++ Rest,
    {lists:reverse(Diffs), Subtrees};
update_merge([[]|Leaves], [], 
             _, _, _, R, Diff, _) ->
    %the proof ended, so there is nothing left to update. checking that we aren't trying to update anyting else.
    %io:fwrite("the proof ended\n"),
    update_merge(Leaves, [], ok, ok, ok, 
                 R, [<<0:256>>|Diff], ok);
update_merge([[]|Leaves], 
             Tree = [[{N, _}|_]|SubTree], Depth, 
             CFG, MEP, R, Diff, N) ->
    %io:fwrite("not changing this element that is recorded in our proof\n"),
    update_merge(
      Leaves, SubTree, Depth, CFG, MEP,
      [hd(Tree)|R], [<<0:256>>|Diff], N+1);
update_merge([LH|Leaves], 
             Subtrees = [[{M, ML}|_]|_], Depth, 
             CFG, MEP, R, Diff, N) 
  when (not(M == N)) ->
    %this part is not recorded in our proof, it cannot be changed.
    %verify that we are not trying to change it.
    if
        not(LH == []) ->
            io:fwrite("verkle2 error. tried to edit inaccessible state."),
            io:fwrite({{updates, LH}, 
                       {at_slot, N}, 
                       {next_slot_in_proof, M}, 
                       {next_value_in_proof, ML}, 
                       {proof_tree, Subtrees}});
        true -> ok
    end,
    update_merge(Leaves, 
                 Subtrees, Depth, CFG, MEP, R, 
                 [<<0:256>>|Diff], N+1);
update_merge([LH|Leaves], [[{N, B}|S1]|Subtrees], 
             Depth, CFG, MEP, R, Diffs, N) 
  when is_binary(B) ->
    %io:fwrite("adding one or more leaves to an existing stem."),

    {Point, Tree2} = 
        update_batch2(LH, S1, Depth+1, CFG, MEP),
    OldN = stem_verkle:hash_point(B),
    %NewPoint0 = fq:e_add(B, Point),
    NewPoint0 = ed:e_add(B, Point),
    {NewPoint, Diff, Hash} = 
        %case (fq:eq(NewPoint0, fq:e_zero())) of
        case (ed:e_eq(NewPoint0, ed:extended_zero())) of
            true -> {NewPoint0, <<0:256>>, <<0:256>>};
            false ->
                {NewPoint0, 
                 {sub, NewPoint0, OldN}, 
                 uncalculated}
        end,
    update_merge(Leaves, Subtrees, Depth, CFG, MEP,
                 [[{N, {mstem, Hash, NewPoint}}|Tree2]|R], 
                 [Diff|Diffs], N+1);
update_merge([[{K, 0}]|Leaves], 
             %[[{N, {OldK, OldV, Meta}}]|Subtrees],
             [[{N, {OldK, OldV}}]|Subtrees],
             Depth, CFG, MEP, R, Diffs, N) ->
    %deleting a leaf.
    %io:fwrite("deleting a leaf"),
    OldLeaf = leaf_verkle:new(OldK, OldV, 0, CFG),
    %OldLeaf = leaf_verkle:new(OldK, OldV, Meta, CFG),
    OldN = store_verkle:leaf_hash(OldLeaf, CFG),
    update_merge(Leaves, Subtrees, Depth, CFG, MEP,
                 [{N, 0}|R], 
                 [fr:neg(OldN)|Diffs], N+1);
update_merge([LH|Leaves], 
             %[[{N, {Key, Value, Meta}}]|Subtrees], 
             [[{N, {Key, Value}}]|Subtrees], 
             Depth, CFG, MEP, R, Diffs, N) ->
    %io:fwrite("add one or more leaves to a spot with an existing leaf\n"),
    %there is already a leaf here.
    %NewLeaf = leaf_verkle:new(Key, Value, 0, CFG),
    %FL = leaf_verkle:new(Key, Value, Meta, CFG),
    FL = leaf_verkle:new(Key, Value, 0, CFG),
                     
    B = leaf_in_list(FL, LH),
    B2 = (1 == length(LH)),
    if
        (B and B2) -> 
            %io:fwrite(LH),
            Leaf2 = hd(LH),
            OldN = store_verkle:leaf_hash(
                     FL, CFG),
            NewN = store_verkle:leaf_hash(
                     Leaf2, CFG),
            LeafDiff = 
                if
                    OldN == NewN -> 
                        %leaf unchanged.
                        %io:fwrite("Leaf unchanged\n"),
                        <<0:256>>;
                        %fr:encode(0);
                    true ->
                        %io:fwrite("updating leaf diff calculation.\n"),
                        fr:sub(NewN, OldN)
                end,
            update_merge(
              Leaves, Subtrees, Depth, CFG, 
              %MEP, [[{N, {leaf_verkle:key(Leaf2),
              MEP, [[{N, {leaf_verkle:raw_key(Leaf2),
                          leaf_verkle:value(Leaf2),
                          leaf_verkle:meta(Leaf2)}}]|
                   %}}]|
                    R],
              [LeafDiff|Diffs], N+1);
        B -> 
            %io:fwrite("adding leaves to a spot where there was a leaf, and changing the existing leaf\n"),
            update_merge(
              [LH|Leaves], 
              [[{N, 0}]
               |Subtrees],
              Depth, CFG, MEP, R, Diffs, N);
        true -> 
            %adding leaves to this spot where there was a leaf, without updating our leaf
            %io:fwrite("adding a leaves to this spot where there is a leaf, and not changing the existing leaf\n"),
            update_merge(
              %[[NewLeaf|LH]|Leaves], 
              [[FL|LH]|Leaves], 
              [[{N, 0}]
               |Subtrees],
              Depth, CFG, MEP, R, Diffs, N)
    end;
update_merge([[]|Leaves],
             [[{N, 0}]|Subtrees],
             Depth, CFG, MEP, R, Diffs, N) ->
    %io:fwrite("left empty spot empty.\n"),
    update_merge(Leaves, Subtrees, Depth, CFG, MEP,
                 [{N, 0}|R], [fr:encode(0)|Diffs], 
                 N+1);
update_merge([LH|Leaves],
             [[{N, 0}]|Subtrees],
             Depth, CFG, MEP, R, Diffs, N) 
  when (length(LH) == 1) ->
    %io:fwrite("add a leaf to empty spot.\n"),
    Leaf = hd(LH),
    LeafDiff = store_verkle:leaf_hash(Leaf, CFG),
    update_merge(
      Leaves, Subtrees, Depth, CFG, MEP,
      [[{N, {leaf_verkle:raw_key(Leaf),
             leaf_verkle:value(Leaf),
             leaf_verkle:meta(Leaf)}}]|R], 
      [LeafDiff|Diffs], N+1);
update_merge([LH|Leaves],
             [[{N, 0}]|Subtrees],
             Depth, CFG, MEP, R, Diffs, N) 
  when (length(LH) > 1) ->
    %io:fwrite("add leaves to empty spot\n"),
    B = ed:extended_zero(),

    %todo. when generating S, we can look in LH to see what I's we need to support. So we don't have to support all 256 possibilities.
    S = lists:map(fun(I) ->
                          [{I, 0}]
                  end, range(0, 256)),
    update_merge([LH|Leaves], [[{N, B}|S]|Subtrees],
                 Depth, CFG, MEP, R, Diffs, N);
update_merge(Ls, [X|T], Depth, CFG, MEP, R, Diffs, 
             N) when is_tuple(X)->
    update_merge(Ls, [[X|T]], Depth, CFG, MEP, R,
                 Diffs, N).

range(N, N) -> [];
range(N, M) when N < M -> 
    [N|range(N+1, M)].

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
    %io:fwrite("merge find helper\n"),
    case dict:find(P, D) of
	error -> P;
	{ok, error} -> 1=2;
	{ok, P2} ->
	    merge_find_helper(P2, D)
    end.

decompress_proof(
  Open0 = {Open1, Open2, OpenL, Open4, Open5}, 
  Tree0, CommitG0) ->
    CPL = get_verkle:compressed_points_list(Tree0),
    false = CPL == [],
    [CommitG, Open1b |Decompressed2] = 
        ed:affine2extended(
          ed:decompress_points(
          [CommitG0, Open1] ++ 
              OpenL ++ CPL)),
    {OpenLb, Decompressed} = 
        lists:split(length(OpenL), Decompressed2),
    {Tree, _} = fill_points(
                  Decompressed, Tree0, []),
    Open = {Open1b, Open2, OpenLb, Open4, Open5},
    Root1 = hd(Decompressed),
    {Tree, Open, Root1, CommitG};
decompress_proof(Open, Tree0, CommitG0) 
  when is_list(Open)->
    CPL = get_verkle:compressed_points_list(Tree0),
    %lists:map(fun(X)-> io:fwrite(base64:encode(X)), io:fwrite("\n") end,
    %                    [CommitG0] ++ CPL),
    %1=2,
    false = CPL == [],
    [CommitG|Decompressed] = 
        ed:affine2extended(
          ed:decompress_points(
          [CommitG0] ++ CPL)),
    {Tree, _} = fill_points(
                  Decompressed, Tree0, []),
    Root1 = hd(Decompressed),
    {Tree, Open, Root1, CommitG}.
    

proof({Tree0, CommitG0, Open0}, CFG) ->
    {Tree, Open, Root1, CommitG} = 
       decompress_proof(Open0, Tree0, CommitG0), 

    %io:fwrite(Tree), %[pt, {i, pt}, [{i, pt}, {i, l}]...
    %1=2,

    %Tree, Open, Root1, CommitG, 

    %multiproof:verify(Proof = {CommitG, Commits, Open_G_E}, Zs, Ys, ?p)
    %Zs are elements of the domain where we look up stuff.
    %Ys are values stored in pedersen commits. either hashes of leaves, or hashes of stems.
    %io:fwrite({Tree, Commits0}),
    
    %[root, [{1, p1}, [{0, L1},{1, L2}], [{3, p2},{0,L3}]]]
    %io:fwrite("verify get parameters \n"),
    [Root|Rest] = Tree,
    Domain = parameters:domain(),
    %B = fq:eq(Root1, Root),
    B = ed:a_eq(Root1, Root),
    if
        not(B) -> 
            io:fwrite("verify fail, unequal roots\n"),
            false;
        true ->
            %io:fwrite("verify unfold \n"),
            benchmark:now(),
            %io:fwrite(Rest),
            %1=2,
            %rest is [{0, pt},[{186, pt},{115, l}], [{187, pt}, {115, l}],[{188, pt}, {115, l}]]
            Tree2 = unfold(Root, Rest, [], CFG),
            %io:fwrite("verify split 3 parts \n"),
            benchmark:now(),
            {Commits, Zs0, Ys} = 
                get_verkle:split3parts(Tree2, [],[],[]),
            %io:fwrite("veirfy index2domain \n"),
            benchmark:now(),
            Zs1 = get_verkle:index2domain2(
                   Zs0),
            Zs = fr:encode(Zs1),
            %io:fwrite("verify multiproof \n"),
            benchmark:now(),
            %io:fwrite({Zs, Ys}),
            B2 = multiproof:verify(
                   {CommitG, Open}, 
                   Commits, Zs, Ys),
            %io:fwrite("verify done \n"),
            benchmark:now(),
            if
                not(B2) -> 
                    io:fwrite("verify fail, multiproof verify\n"),
                    false;
                true ->
                    {true, leaves2(Rest, []), Tree}
            end
    end.
    
    %[p2, root, p1, p1, root] %commitments
    %[0,  3,    1,  0,  1]  %indices
    %[L3, p2,   L2, L1, p1] %unhashed ys

    %[{1, p1}, [{0, L1},{1, L2}], [{3, p2},{0,L3}]]

leaves({Y, X = 0}) -> [{Y, X}];%unused
leaves(X = {_, B}) when is_binary(B) -> [];
%leaves({_, X = {I, B, M}}) 
leaves({_, X = {I, B}}) 
  when is_binary(B) and 
       is_binary(I) and 
%       is_binary(M) and
       (size(I) == 32) -> 
    %1=2,
    [X];
leaves([H|T]) ->
    leaves(H) ++ leaves(T);
leaves([]) ->  [];
leaves(X) ->  
    %leaf getter error.
    io:fwrite({X}).

leaves2([], _SubPath) -> [];
leaves2([{N, B}|T], SubPath) when is_binary(B) ->
    leaves2(T, [N|SubPath]);
leaves2([[H|T]|T2], SubPath) ->
    leaves2([H|T], SubPath) ++ 
        leaves2(T2, SubPath);
leaves2([{N, X = {K, V}}], _) 
  when is_binary(K) and is_binary(V) ->
    [X];
leaves2([{N, 0}], SubPath) -> 
    [{[N|SubPath], 0}];
leaves2(X, SubPath) -> 
    io:fwrite({X, SubPath}),
    1=2.


    

    
              

unfold(Root, {Index, 0}, T, CFG) ->%empty case
    lists:reverse([{Root, Index, <<0:256>>}|T]);
%unfold(Root, {Index, {Key, B, Meta}}, T, CFG) %leaf case
unfold(Root, {Index, {Key, B}}, T, CFG) %leaf case
  when is_binary(B) ->
    %Leaf = #leaf{key = Key, value = B},
    %io:fwrite("verify unfold leaf\n"),
    %Leaf = leaf_verkle:new(Key, B, Meta, CFG),
    Leaf = leaf_verkle:new(Key, B, 0, CFG),
    <<L:256>> = store_verkle:leaf_hash(Leaf, CFG),
    lists:reverse([{Root, Index, <<L:256>>}|T]);
unfold(Root, [{Index, X}|R], T, CFG) %stem case
  when (is_binary(X) and (size(X) == (32*4)))
   ->
    <<H:256>> = stem_verkle:hash_point(X),
    unfold(X, R, [{Root, Index, <<H:256>>}|T], CFG);
unfold(Root, [H|J], T, CFG) ->
    unfold(Root, H, T, CFG)
        ++ unfold(Root, J, [], CFG);
unfold(_, [], _, _) -> [];
unfold(_, {0, X}, _, _) -> 
    io:fwrite({size(X), X}).



test() ->
    CFG = tree:cfg(tree01),
    Leaves = [leaf_verkle:new(999999872, <<0,0>>, 0, CFG),
              leaf_verkle:new(999999744, <<0,0>>, 0, CFG)],
    Leaves2 = store_verkle:clump_by_path(
                0, Leaves),
    %todo. each should have the same number of leaves.
    true = (length(remove_empty(Leaves))) ==
        (length(remove_empty(Leaves2))),
    success.
