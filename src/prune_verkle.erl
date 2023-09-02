-module(prune_verkle).
-export([doit_stem/3, test/1]).

doit([], [], [], [], D, _) ->
    %returns the list of every leaf that was deleted.
    D;
doit([P|PointersT], [T|TypesT], 
     [P|PointersK], [T|TypesK], 
     Deleted, CFG) ->
    %if both sides are the same, there is nothing to prune in that branch.
    doit(PointersT, TypesT, PointersK, TypesK, 
         Deleted, CFG);
doit([_|PointersT], [0|TypesT], 
     [_|PointersK], [_|TypesK], 
     Deleted, CFG) ->
    %if the old version was empty, there is nothing to prune in that branch.
    doit(PointersT, TypesT, PointersK, TypesK, 
         Deleted, CFG);
doit([P|PointersT], [1|TypesT], 
     [K|PointersK], [1|TypesK], 
     Deleted, CFG) ->
    %if the old version was a stem, and that stem was edited
    %io:fwrite("change stem\n"),
    D2 = doit_stem(P, K, [], CFG),
    doit(PointersT, TypesT, PointersK, TypesK,
         Deleted ++ D2, CFG);
doit([P|PointersT], [1|TypesT], 
     [_|PointersK], [0|TypesK], 
     Deleted, CFG) ->
    %if the old version was a stem, and that stem was deleted
    io:fwrite("a stem was somehow deleted. should be impossible.\n"),
    doit(PointersT, TypesT, PointersK, TypesK,
         Deleted ++ D2, CFG);
    %io:fwrite("change stem\n"),
    %D2 = doit_stem(P, 1, [], CFG),
    %doit(PointersT, TypesT, PointersK, TypesK,
    %     Deleted ++ D2, CFG);
doit([_P|PointersT], [1|TypesT], 
     [_K|PointersK], [2|TypesK], 
     Deleted, CFG) ->
    %if the old version was a stem, and all but one was deleted, so now it is a leaf.
    %there is a leak here, but it is uncalled because we never delete anything, so the leak doesn't happen.
    io:fwrite("a stem became a leaf. this should be impossible\n"),
    doit(PointersT, TypesT, PointersK, TypesK, Deleted, CFG);
doit([T|PointersT], [2|TypesT], 
     [K|PointersK], [T2|TypesK], 
     Deleted, CFG) when ((T2 == 0) or (T2 == 2))->
    %io:fwrite("remove leaf\n"),
    %if a leaf was edited or removed
    L = leaf_verkle:get(T, CFG),
    leaf_verkle:delete(T, CFG),
    doit(PointersT, TypesT, PointersK, TypesK,
         [L|Deleted], CFG);
doit([T|PointersT], [2|TypesT], 
     [K|PointersK], [1|TypesK], 
     Deleted, CFG) ->
    %the old version was a leaf, but it got expanded to being a stem.
    %there is a leak here. if the old leaf was deleted, it is leaked.
    doit(PointersT, TypesT, PointersK, TypesK, Deleted, CFG).


doit_stem(Trash, Keep, CFG) ->
    doit_stem(Trash, Keep, [], CFG).
doit_stem(Trash, Keep, Deleted, CFG) ->
    %trash and keep are pointers to consecutive root stems.
    %return a list of every leaf that got deleted, along with their meta data.
    %walk down the tree. if things are different, you can delete the trash side. if they are the same, then don't delete anything.
    %io:fwrite("prune verkle doit_Stem keep: "),
    %io:fwrite(integer_to_list(Keep)),
    %io:fwrite("\n"),
    T1 = stem_verkle:get(Trash, CFG),
    K1 = stem_verkle:get(Keep, CFG),
    if
        T1 == K1 -> Deleted;
        true -> 
            stem_verkle:delete(Trash, CFG),
            PointersT = stem_verkle:pointers(T1),
            PointersK = stem_verkle:pointers(K1),
            TypesT = stem_verkle:types(T1),
            TypesK = stem_verkle:types(K1),
            doit(tuple_to_list(PointersT), 
                 tuple_to_list(TypesT), 
                 tuple_to_list(PointersK), 
                 tuple_to_list(TypesK), 
                 Deleted, CFG)
    end.

range(A, B) when (A < B) ->
    [A|range(A+1, B)];
range(A, A) -> [].

test(0) ->
    CFG = tree:cfg(tree01),
    Loc = 1,
    Times = 5,
    Leaves = 
        lists:map(
          fun(N) -> 
                  Key = N,
                  leaf_verkle:new(Key, <<N:16>>, <<0>>, CFG)
          end, range(1, Times+1)),
    Leaves2 = 
        lists:map(
          fun(N) -> 
                  %Key = N * 2,
                  Key = N+1,
                  leaf_verkle:new(Key, <<(N+5):16>>, <<1>>, CFG)
          end, range(1, Times+1)),
    
    %Many = lists:map(fun(Leaf) -> 
    %                 leaf_verkle:raw_key(Leaf) end,
    %                 Leaves),
    T1 = bits:top(tree01_v_stem),
    {Loc2, stem, _} = 
        store_verkle:batch(Leaves, Loc, CFG),
    T2 = bits:top(tree01_v_stem),
    {Loc3, stem, _} = 
        store_verkle:batch(Leaves2, Loc2, CFG),
    T3 = bits:top(tree01_v_stem),
    Result = doit_stem(Loc2, Loc3, CFG),
    io:fwrite({Loc, Loc2, Loc3, Result}),
    
    Result.
    
            
