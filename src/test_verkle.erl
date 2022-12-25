-module(test_verkle).
-export([test/0, test/1, load_db/1, proof_test/2]).

-define(ID, tree01).
-include("constants.hrl").

test() ->
    CFG = tree:cfg(?ID),
    V = [
         %23,
         1,
         2,
         3,
         4,
         5
        ],
    test_helper(V, CFG).
test(N) ->
    CFG = tree:cfg(?ID),
    %test_helper([N], CFG).
    test(N, CFG).
test_helper([], _) -> success;
test_helper([N|T], CFG) -> 
    io:fwrite("test "),
    io:fwrite(integer_to_list(N)),
    io:fwrite("\n"),
    success = test(N, CFG),
    test_helper(T, CFG).

test(1, CFG) ->

    %making a proof, and not editing it.
    %compares fast proofs with normal proofs.
    %so this gives an idea of how it is for a light node.
    Loc = 1,
    Times = 10000,
    Prove = 3,
    Leaves = 
        lists:map(
          fun(N) -> 
                  Key0 = Times + 1 - N,
                  %<<Key:256>> = <<(-Key0):256>>,
                  Key = 1000000000 - (Key0*256),
                  leaf_verkle:new(Key, <<N:16>>, <<0>>, CFG)
          %end, Many),
          end, range(1, Times+1)),
    %Many = lists:map(fun(#leaf{key = K}) -> K end,
    Many = lists:map(fun(Leaf) -> 
                             leaf_verkle:raw_key(Leaf) 
                     end, Leaves),
    io:fwrite("load up the batch database\n"),
    T1 = erlang:timestamp(),
    {NewLoc, stem, _} = 
        store_verkle:batch(Leaves, Loc, CFG),
    T2 = erlang:timestamp(),
    io:fwrite("make proof\n"),
    %Keys = [<<5:256>>|Many],
    %Keys = [<<5:256>>],
    %Keys = [hd(Many), hd(tl(Many))],
    {Keys, _} = lists:split(Prove, Many),
    {Proof, _} = 
        get_verkle:batch(Keys, NewLoc, CFG),
    T3 = erlang:timestamp(),
    io:fwrite("make fast proof\n"),
    {FastProof, _} = 
        get_verkle:batch(Keys, NewLoc, CFG, fast),

    T4 = erlang:timestamp(),
    io:fwrite("verify proof\n"),
    Root = stem_verkle:root(stem_verkle:get(NewLoc, CFG)),
    {true, Leaves2, _} = 
        verify_verkle:proof(Proof, CFG),
    T5 = erlang:timestamp(),
    {true, Leaves2, _} = 
        verify_verkle:proof(FastProof, CFG),
    T6 = erlang:timestamp(),
    %io:fwrite({lists:reverse(Leaves2)}),
    %io:fwrite({length(Leaves2), length(Keys)}),
    true = (length(Leaves2) == length(Keys)),
    if
        true ->
            io:fwrite("measured in millionths of a second. 6 decimals. \n"),
            io:fwrite("load tree with "),
            io:fwrite(integer_to_list(Times)),
            io:fwrite(" elements: "),
            io:fwrite(integer_to_list(timer:now_diff(T2, T1))),
            io:fwrite("\nmake normal proof: "),
            io:fwrite(integer_to_list(timer:now_diff(T3, T2))),
            io:fwrite("\nmake fast proof: "),
            io:fwrite(integer_to_list(timer:now_diff(T4, T3))),
            io:fwrite("\nverify normal proof: "),
            io:fwrite(integer_to_list(timer:now_diff(T5, T4))),
            io:fwrite("\nverify fast proof: "),
            io:fwrite(integer_to_list(timer:now_diff(T6, T5))),
            io:fwrite("\n");
        true -> ok
    end,
    success;
    %FastProof;
test(2, CFG) ->
    Loc = 1,
    Times = 3,
    Leaves = 
        lists:map(
          fun(N) -> 
                  %Key0 = Times + 1 - N,
                  %<<Key:256>> = <<(-Key0):256>>,
                  Key = 1000000000 - (128 * N),
                  %#leaf{key = Key, value = <<N:16>>}
                  leaf_verkle:new(Key, <<N:16>>, <<0>>, CFG)
          end, range(1, Times+1)),
    %Many = lists:map(fun(#leaf{key = K}) -> K end,
    Many = lists:map(fun(Leaf) -> 
                     leaf_verkle:raw_key(Leaf) end,
                     Leaves),
    {NewLoc, stem, _} = 
        store_verkle:batch(Leaves, Loc, CFG),
    {{ProofTree, Commit, Opening}, _} = 
        get_verkle:batch([<<5:256>>,<<6:256>>|Many], 
                   NewLoc, CFG),
    {true, _, DecompressedTree} = 
        verify_verkle:proof(
          {ProofTree, Commit, Opening}, CFG),
    %io:fwrite(ProofTree),
    Leaf01 = hd(Leaves),
    Leaf02 = hd(tl(Leaves)),
    DeleteKey = leaf_verkle:raw_key(Leaf02),
    Leaf1 = Leaf01#leaf{value = <<0,0>>, meta = <<2>>},%editing existing leaf.
    Leaf2 = leaf_verkle:new(5, <<0,1>>, <<2>>, CFG),%creating a new leaf.
    Leaf3 = {DeleteKey, 0},
    %io:fwrite({Leaf1, Leaf2}),
    %Leaf2 = {Leaf02#leaf.key, 0},
    %Leaf3 = leaf_verkle:new(5, <<0,0>>, <<0>>, CFG),%writing to the previously empty location.
    %io:fwrite({Leaf0, Leaf1}),
    %NewRoot0 = hd(ProofTree),
    %Leaves2 = [Leaf2|Leaves],
    %Leaves2 = [Leaf2, hd(Leaves)|tl(tl((Leaves)))],
    Leaves2 = [Leaf1, Leaf2|tl(tl(Leaves))],
    %io:fwrite(Leaves2),
    io:fwrite("test trie to store.\n"),

    %in this part we are storing the new data directly. This is so we can get a root hash, and verify that updating the proof worked correctly.
    {Loc3, _, _} = 
        store_verkle:batch(Leaves2, 1, CFG),
    io:fwrite("test trie stored\n"),
    RootStem = stem_verkle:get(Loc3, CFG),
    %io:fwrite(DecompressedTree),

    %notice that this proof is based on NewLoc, from before the leaves were stored. 
    ProofTree2 = 
        verify_verkle:update(
          %DecompressedTree, [Leaf1, Leaf2, Leaf3],
          DecompressedTree, [Leaf1, Leaf2, Leaf3],
          CFG),
    %after the update, we store meta data in the tree for leaves that have been changed.
    NewRoot2 = hd(ProofTree2),
    Loc2 = store_verkle:verified(
                  NewLoc, ProofTree2, CFG),
    RootStem4 = stem_verkle:get(Loc2, CFG),

    HP3 = stem_verkle:hash(stem_verkle:get(Loc2, CFG)),
    HP4 = stem_verkle:hash(stem_verkle:get(Loc3, CFG)),
    CheckStem2 = stem_verkle:get(Loc2, CFG),
    CheckStem3 = stem_verkle:get(Loc3, CFG),
    true = element(5, CheckStem3) == element(5, CheckStem2),
    true = ed:e_eq(element(2, CheckStem2), element(2, CheckStem3)),
%    io:fwrite({HP3 == HP4, 
%               lists:reverse(tuple_to_list(element(5, CheckStem2))),
%               lists:reverse(tuple_to_list(element(5, CheckStem3))),
%               stem_verkle:get(Loc2, CFG), 
%               stem_verkle:get(Loc3, CFG)}),
    HP3 = HP4,
   
    %5 is the new leaf.
    {{Proof1, Commit1, Opening1}, _} = 
        get_verkle:batch([<<5:256>>, DeleteKey, <<6:256>>], Loc3, CFG),
    Root1 = stem_verkle:root(stem_verkle:get(Loc3, CFG)),
    %io:fwrite({size(Root1), size(hd(Proof1))}),
    {true, FLeaves0, _} = 
        verify_verkle:proof(
          %Root1,
          {Proof1, Commit1, Opening1}, CFG),

    %io:fwrite(FLeaves0),
                                 
    {{Proof2, Commit2, Opening2}, _} = 
        get_verkle:batch([<<5:256>>], Loc2, CFG),
    Root2 = stem_verkle:root(stem_verkle:get(Loc2, CFG)),
    {true, _FLeaves, _} = 
        verify_verkle:proof(
          %Root2,
          {Proof2, Commit2, Opening2}, CFG),
    HP1 = stem_verkle:hash_point(ed:decompress_point(hd(Proof1))),
    HP2 = stem_verkle:hash_point(ed:decompress_point(hd(Proof2))),
    HP1 = HP2,

    %this is for the leaf being edited.
    {{Proof3, _, _}, _} = 
        get_verkle:batch([leaf_verkle:raw_key(Leaf1)], 
                   Loc3, CFG),
    {{Proof4, _, _}, Meta2} = 
        get_verkle:batch([leaf_verkle:raw_key(Leaf1)], 
                   Loc2, CFG),
%    io:fwrite(dict:find(leaf_verkle:raw_key(Leaf1),
%                        Meta2)),%returns <<0>>, should be <<2>>.

    %this is for the leaf being deleted.
    {{Proof5, _, _}, _} = 
        get_verkle:batch([DeleteKey], Loc3, CFG),
    {{Proof6, _, _}, _} = 
        get_verkle:batch([DeleteKey], Loc2, CFG),

    %io:fwrite(Proof5),
    HP1 = stem_verkle:hash_point(ed:decompress_point(hd(Proof1))),
    HP2 = stem_verkle:hash_point(ed:decompress_point(hd(Proof2))),
    Case2  = not(ed:a_eq(ed:decompress_point(hd(Proof3)), ed:decompress_point(hd(Proof4)))),
    Case3  = not(ed:a_eq(ed:decompress_point(hd(Proof5)), ed:decompress_point(hd(Proof6)))),
    if
        (not(HP1 == HP2)) ->
        %(not(Proof1 == Proof2)) ->
            io:fwrite("failed to create element\n"),
            io:fwrite(
              {Proof1, Proof2, 
               hd(tl(Proof1)) == hd(tl(Proof2)), 
               size(hd(Proof1)), size(hd(Proof2)), 
               %Root2, NewRoot2, 
               %size(Root2), size(NewRoot2), 
               %ed:e_eq(Root2, NewRoot2), 
               ed:e_eq(ed:decompress_point(hd(Proof2)), NewRoot2), 
               ed:e_eq(ed:decompress_point(hd(Proof1)), NewRoot2), 
               (HP1 == HP2)});
        Case2 ->
            io:fwrite("failed to edit element\n"),
            io:fwrite({Proof3, Proof4});
        Case3 ->
            io:fwrite("failed to delete element\n"),
            io:fwrite({Proof5, Proof6});
        true -> ok
    end,
    %true = fq:eq(NewRoot2, RootStem#stem.root),
    %true = fq:eq(RootStem#stem.root, RootStem4#stem.root),

    success;
test(3, CFG) ->
    Loc = 1,
    StartingElements = 10000,
    UpdateElements = 3000,
    Leaves = 
        lists:map(
          fun(N) -> 
                  Key = crypto:strong_rand_bytes(32),
                  %Key = hash:doit(<<N:256>>),
                  leaf_verkle:new(Key, <<N:16>>, <<0>>, CFG)
                  %Key0 = StartingElements + 1 - N,
                  %Key = 100000000000000000000000000000000000000000000000000000000000000000000000000000 - (Key0 * 111),
                  %leaf_verkle:new(Key, <<N:16>>, <<>>, CFG)
          end, range(1, StartingElements+1)),
    %Many = lists:map(fun(#leaf{key = K}) -> K end,
    Many = lists:map(fun(Leaf) -> 
                     leaf_verkle:raw_key(Leaf) end,
                     Leaves),
    {Updating, NotUpdating} = 
        lists:split(UpdateElements, Many),
    UpdatedLeaves = 
        lists:map(
          fun(N) -> 
                  leaf_verkle:new(N, <<2, 7>>, <<0>>, CFG)
%                  #leaf{key = N, 
%                        value = <<2,7>>}
                  
          end, Updating),
    %Leaf5 = leaf_verkle:new(5, <<0,0>>, <<0>>, CFG),
    %LGK = hd(NotUpdating),
    %LeafGone = {LGK, 0},
                        
    %loading the db 
    T0 = erlang:timestamp(),
    {Loc2, _, _} = 
        store_verkle:batch(Leaves, Loc, CFG),
    %making the verkle proof
    T1 = erlang:timestamp(),
    {{ProofTree, Commit, Opening}, _} = 
        get_verkle:batch(Updating, Loc2, CFG),
    %verifying the verkle proof
    T2 = erlang:timestamp(),

    %{ok, _PID} = fprof:start(),
    %fprof:trace([start, {procs, all}]),


    {true, _, DecompressedTree} = 
        verify_verkle:proof(
          {ProofTree, Commit, Opening}, CFG),

    %fprof:trace([stop]),
    %fprof:profile(),
    %fprof:analyse(),
    %fprof:stop(),

    %updating the proof.
    T3 = erlang:timestamp(),

    
    ProofTree2 = verify_verkle:update(
               DecompressedTree, 
                   UpdatedLeaves, CFG),
    %io:fwrite({ProofTree, ProofTree2}),


    %storing the new data in the db
    T4 = erlang:timestamp(),
    Loc3 = store_verkle:verified(
                  Loc2, ProofTree2, CFG),
    T5 = erlang:timestamp(),
    

    io:fwrite("measured in millionths of a second. 6 decimals. \n"),
    io:fwrite("tree has "),
    io:fwrite(integer_to_list(StartingElements)),
    io:fwrite(" elements. we are updating "),
    io:fwrite(integer_to_list(UpdateElements)),
    io:fwrite(" of them.\n loading the db: "),
    io:fwrite(integer_to_list(timer:now_diff(T1, T0))),
    io:fwrite("\n making the proof: "),
    io:fwrite(integer_to_list(timer:now_diff(T2, T1))),
    io:fwrite("\n verifying proof: "),
    io:fwrite(integer_to_list(timer:now_diff(T3, T2))),
    io:fwrite("\n root hash of the updated proof: "),
    io:fwrite(integer_to_list(timer:now_diff(T4, T3))),
    io:fwrite("\n storing the new data in the database: "),
    io:fwrite(integer_to_list(timer:now_diff(T5, T4))),
    io:fwrite("\n\n"),

    success;
test(23, CFG) ->
    Loc = 1,
    StartingElements = 2000,
    Leaves = 
        lists:map(
          fun(N) -> 
                  Key0 = StartingElements + 1 - N,
                  %Key = 100000000000000 - (Key0 * 111),
                  Key = 100000000000000000000000000000000000000000000000000000000000000000000000000000 - (Key0 * 128),
                  %#leaf{key = Key, 
                  %      value = <<N:16>>}
                  N2 = hash:doit(<<N:256>>),
                  %leaf_verkle:new(Key, <<N:16>>, <<0>>, CFG)
                  leaf_verkle:new(N2, <<N:16>>, <<0>>, CFG)
          end, range(1, StartingElements+1)),
    Keys = lists:map(fun(Leaf) -> 
                     leaf_verkle:raw_key(Leaf) end,
                     Leaves),
    LeafDeletes = lists:map(fun(Key) ->
                                    {Key, 0}
                            end, Keys),
    
    {Loc2, _, _} = 
        store_verkle:batch(Leaves, Loc, CFG),
    {{ProofTree, Commit, Opening}, _} = 
        get_verkle:batch(Keys, Loc2, CFG),
    {true, Leaves2} = 
        verify_verkle:proof(
          {ProofTree, Commit, Opening}, CFG),
    %io:fwrite({Leaves2, LeafDeletes}),
    ProofTree2 = verify_verkle:update(
               ProofTree, LeafDeletes, CFG),
    Loc3 = store_verkle:verified(Loc2, ProofTree2, CFG),
    
    %io:fwrite(get_verkle:batch(Keys, Loc3, CFG)),
    
    success;
test(4, CFG) ->
    %test of updating a point.
    Loc = 1,
    Key = 27,
    UnusedKey = 11,
    Leaf1 = leaf_verkle:new(Key, <<27:16>>, <<0>>, CFG),
    Leaf2 = leaf_verkle:new(Key, <<29:16>>, <<0>>, CFG),
    {Loc2, stem, _} = store_verkle:batch([Leaf1], Loc, CFG),
    {{ProofTree, Commit, Opening}, _} = 
        get_verkle:batch([<<Key:256>>],
                   Loc2, CFG),
    {true, _, DecompressedTree} = 
        verify_verkle:proof(
          {ProofTree, Commit, Opening}, CFG),
    ProofTree2 = 
        verify_verkle:update(DecompressedTree, [Leaf2], CFG),
    RootHash2 = stem_verkle:hash_point(hd(ProofTree2)),

    {Loc4, stem, _} = store_verkle:batch([Leaf2], Loc, CFG),
    RootHash1 = stem_verkle:hash(stem_verkle:get(Loc4, CFG)),

    RootHash2 = RootHash1,

    success;
test(5, CFG) ->
    {_, _} = test_batch(20, 1, CFG),
    {_, _} = test_batch(20, 2, CFG),
    {_, _} = test_batch(2000, 1, CFG),
    {_, _} = test_batch(2000, 2, CFG),
    success;
test(6, CFG) ->
    %try updating a proof by inserting 2 elements into the same empty slot of a stem. todo.
    Loc = 1,
    Leaf1 = leaf_verkle:new(
              1, <<2:16>>, <<0>>, CFG),
    Leaf2 = leaf_verkle:new(
              257, <<2:16>>, <<0>>, CFG),
    Leaf3 = leaf_verkle:new(
              5, <<2:16>>, <<0>>, CFG),
    Leaves = [Leaf1, Leaf2, Leaf3],
    Keys = lists:map(
             fun(L) ->
                     leaf_verkle:raw_key(L) end,
             Leaves),
%    {Loc2, stem, _} = 
%        store_verkle:batch(Leaves, Loc, CFG),
    {{ProofTree, Commit, Opening}, _} =
        get_verkle:batch(Keys, Loc, CFG),
    {true, _, ProofTree2} = 
        verify_verkle:proof(
          {ProofTree, Commit, Opening}, CFG),
    Leaf1b = Leaf1#leaf{value = <<0,0>>, meta = <<2>>},
    Leaf2b = Leaf2#leaf{value = <<0,1>>, meta = <<3>>},
    Leaf3b = Leaf3#leaf{value = <<0,4>>, meta = <<3>>},
    ProofTree3 = 
        verify_verkle:update(
          ProofTree2, [Leaf1b, Leaf2b], CFG),%this version fails.
          %ProofTree2, [Leaf1b, Leaf3b], CFG),%this version works
    Root = hd(ProofTree3),
    io:fwrite(ProofTree3).
    
                              
    
    
    
test_batch(Times, ProveMany, CFG) ->
    Loc = 1,
    %Times = 20,
    %ProveMany = 2,
    Leaves = 
        lists:map(
          fun(N) -> 
                  Key0 = Times + 1 - N,
                  %Key = 1000000000 - (Key0*256),
                  Key = 1000000000 - (Key0),
                  leaf_verkle:new(Key, <<N:16>>, <<0>>, CFG)
          end, range(1, Times+1)),
    Keys = lists:map(fun(Leaf) -> 
                             leaf_verkle:raw_key(Leaf) 
                     end, Leaves),
    {NewLoc, stem, _} = 
        store_verkle:batch(Leaves, Loc, CFG),

    {First, _} = lists:split(ProveMany, Keys),
    {Proof, _} = get_verkle:batch(
                   First, NewLoc, CFG, small),
    SP = get_verkle:serialize_proof(Proof),
    Proof = get_verkle:deserialize_proof(SP),
    {true, _, _} = verify_verkle:proof(
                     Proof, CFG),
    %io:fwrite(Proof),
    {size(SP), SP}.

range(A, B) when (A < B) ->
    [A|range(A+1, B)];
range(A, A) -> [].


load_db(Elements) ->
    CFG = tree:cfg(?ID),
    Leaves = 
        lists:map(
          fun(N) -> 
                  %Key0 = Elements + 1 - N,
                  %Key = 100000000000000 - (Key0 * 111),
                  %Key = 100000000000000000000000000000000000000000000000000000000000000000000000000000 - (Key0 * 111),
                  %#leaf{key = Key, 
                  %      value = <<N:16>>}
                  N2 = hash:doit(<<N:256>>),
                  %N2 = crypto:strong_rand_bytes(32),
                  leaf_verkle:new(N2, <<N:16>>, <<0>>, CFG)
          end, range(1, Elements+1)),
    {Loc2, _, _} = 
        store_verkle:batch(Leaves, 1, CFG),
    Loc2.
proof_test(Loc2, UpdateMany) ->
    CFG = tree:cfg(?ID),
    Updating0 = range(0, UpdateMany),
    Updating = lists:map(
                 fun(N) ->
                         hash:doit(<<N:256>>)
                 end, Updating0),
    UpdatedLeaves = 
        lists:map(
          fun(N) ->
                  leaf_verkle:new(N, <<2, 7>>, <<0>>, CFG)
          end, Updating),
    Leaf5 = leaf_verkle:new(5000000000000000000000, 
                     <<0,0>>, <<0>>, CFG),
    <<LGK:256>> = 
        hash:doit(<<(UpdateMany + 1):256>>),
    LeafGone = {LGK, 0},
    
    %making the verkle proof
    T1 = erlang:timestamp(),
    {{ProofTree, Commit, Opening}, _} = 
        get_verkle:batch(Updating, Loc2, CFG),

    io:fwrite("verifying the proof\n"),
    %{ok, _PID} = fprof:start(),
    %fprof:trace([start, {procs, all}]),

    %verifying the verkle proof
    T2 = erlang:timestamp(),
    {true, _, DecompressedTree} = 
        verify_verkle:proof(
          {ProofTree, Commit, Opening}, CFG),


    %fprof:trace([stop]),
    %fprof:profile(),
    %fprof:analyse(),
    %fprof:stop(),

    %updating the proof.
    T3 = erlang:timestamp(),

    
    ProofTree2 = verify_verkle:update(
               %ProofTree, UpdatedLeaves, CFG),
               DecompressedTree, UpdatedLeaves, CFG),

    %storing the new data in the db
    T4 = erlang:timestamp(),
    Loc3 = store_verkle:verified(
                  Loc2, ProofTree2, CFG),
    T5 = erlang:timestamp(),
    
    io:fwrite("measured in millionths of a second. 6 decimals. \n"),
    %io:fwrite("tree has "),
    %io:fwrite(integer_to_list(StartingElements)),
    io:fwrite(" we are updating "),
    io:fwrite(integer_to_list(UpdateMany)),
    io:fwrite(" of them."),% loading the db: "),
    %io:fwrite(integer_to_list(timer:now_diff(T1, T0))),
    io:fwrite("\n making the proof: "),
    io:fwrite(integer_to_list(timer:now_diff(T2, T1))),
    io:fwrite("\n verifying proof: "),
    io:fwrite(integer_to_list(timer:now_diff(T3, T2))),
    io:fwrite("\n root hash of the updated proof: "),
    io:fwrite(integer_to_list(timer:now_diff(T4, T3))),
    io:fwrite("\n storing the new data in the database: "),
    io:fwrite(integer_to_list(timer:now_diff(T5, T4))),
    io:fwrite("\n\n"),

    success.
    



    
    
