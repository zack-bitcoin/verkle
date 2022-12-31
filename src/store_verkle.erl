-module(store_verkle).
-export([batch/3,
         test/1,
         leaf_hash/2,
         clump_by_path/2,
         verified/3
        ]).
-include("constants.hrl").
-define(sanity, false).

batch(Leaves0, RP, CFG) ->%returns {location, stem/leaf, #stem{}/#leaf{}}
    %put them in an ordered list.
    %io:fwrite("store sorting 0\n"),
    % 2%
    Leaves = sort_by_path2(Leaves0, CFG),
    %io:fwrite("store parameters 1\n"),
    MEP = parameters:multi_exp(),
    %io:fwrite("store storing 1\n"),
    batch(Leaves, RP, stem, 0, CFG, MEP).

batch([], 0, _, _, _CFG, _) ->
    %type 0 is empty
    {0, 0, empty};
batch([], P, leaf, _, _CFG, _) ->
    %don't read the leaf here, because we aren't changing it.
    {P, leaf, leaf_not_recorded};
batch([], P, stem, _, _CFG, _) ->
    %don't read the stem here, because we aren't changing it.
    {P, stem, stem_not_recorded};
batch([Leaf], 0, 0, _, CFG, _) ->
    %io:fwrite("storing a leaf in a previously empty spot.\n"),
    Loc = leaf_verkle:put(Leaf, CFG),
    {Loc, leaf, Leaf};
batch(Leaves0, 0, 0, Depth, CFG, MEP) ->
    %io:fwrite("storing multiple leaves in a previously empty spot.\n"),
    batch(Leaves0, 
          1, %1 is always an empty stem.
          stem, Depth, CFG, MEP);
batch([Leaf0], RP, leaf, Depth, CFG, MEP) ->
    %io:fwrite("storing a leaf where there is already a leaf.\n"),
    RootLeaf = leaf_verkle:get(RP, CFG),
    RootKey = leaf_verkle:key(RootLeaf),
    Key2 = leaf_verkle:key(Leaf0),
    B = Key2 == RootKey,
    B2 = leaf_verkle:value(RootLeaf) == 
        leaf_verkle:value(Leaf0),
    if
        B2 and B -> 
            %1=2,
            {RP, leaf, RootLeaf};
        B -> 
            Loc = leaf_verkle:put(Leaf0, CFG),
            {Loc, leaf, Leaf0};
        true ->
            batch([Leaf0, RootLeaf], 1, stem,
                  Depth, CFG, MEP)
    end;
batch(Leaves0, RP, leaf, Depth, CFG, MEP) ->
    %io:fwrite("storing leaves where there is already a leaf.\n"),
    RootLeaf = leaf_verkle:get(RP, CFG),
    RootKey = leaf_verkle:key(RootLeaf),
    Keys = lists:map(fun(X) -> leaf_verkle:key(X) 
                     end, Leaves0),
    B = is_in(RootKey, Keys),
    Leaves2 = if
                  B -> Leaves0;
                  true -> [RootLeaf|Leaves0]
              end,
    batch(Leaves2, 1, stem, 
          Depth, CFG, MEP);
batch(Leaves, RP, stem, Depth, CFG, MEP) ->
    %cut the list into sub lists that get included in each sub-branch.
    % %6
    Leaves2 = clump_by_path(
                Depth, Leaves),
    %depth first recursion over the sub-lists on teh sub-trees to calculate the pointers and hashes for this node.
    true = is_integer(RP),
    RootStem = stem_verkle:get(RP, CFG),
    #stem{
           hashes = Hashes,
           pointers = Pointers,
           types = Types,
           root = Root
         } = RootStem,
    % %0
    HPT1 = lists:map(
             fun(I) -> {element(I, Hashes),
                        element(I, Pointers),
                        element(I, Types)}
             end, range(1, size(Hashes))),
    %io:fwrite({HPT1, Leaves2}),
    RHPT = lists:zipwith(
           fun(Leaves3, {H, P, T}) -> 
                   T2 = case T of
                            0 -> 0;
                            1 -> stem;
                            2 -> leaf
                        end,
                   {P2, Type, Tree} = 
                       batch(Leaves3, P, 
                             T2, Depth+1, CFG, MEP),
                   H2 = hash_thing(%  3%
                          P2, Type, Tree, H, CFG),
                   Sub = fr:sub(H2, H),
                   {Sub, H2, P2, Type}
           end,
            Leaves2, HPT1),

    % 0.65%
    {Rs, Hashes2, Pointers2, Types20} = 
        split4ways(RHPT),
    Types2 = lists:map(
               fun(X) ->
                       case X of
                           stem -> 1;
                           leaf -> 2;
                           empty -> 0;
                           0 -> 0
                       end
               end, Types20),
    %4.59

    % 51%
    %io:fwrite(Rs), [<<0,0,0,0...>>,...]
    EllDiff = precomputed_multi_exponent:doit(Rs, MEP),

    % 3.6%
    NewRoot = ed:e_add(EllDiff, Root),
    if
        (NewRoot == error) -> io:fwrite({EllDiff, Root});
        true -> ok
    end,
    [Affine] = ed:extended2affine_batch([NewRoot]),
    %clumping is 6%
    %hashing is 2.45%
    %reading + writing is ???
    %multi exponent is 30.5%
    %[{location, type, #stem{}/#leaf{}}, ...]
    NewStem = 
        RootStem#stem{
          hashes = list_to_tuple(Hashes2),
          pointers = list_to_tuple(Pointers2),
          types = list_to_tuple(Types2),
          root = NewRoot
         },
    Loc = stem_verkle:put(NewStem, Affine, CFG), 
    {Loc, stem, NewStem}.

%after you verify that a verkle proof is correct, and you update that verkle proof with the new data, you can use this function to store the new data into the database.
verified(Loc, ProofTree, CFG) ->
    %io:fwrite("verified start\n"),
    RootStem = stem_verkle:get(Loc, CFG),
    
    RootStem2 = verified2(tl(ProofTree), RootStem, CFG),
    RootStem3 = 
        RootStem2#stem{root = hd(ProofTree)},
    if
        ?sanity ->
            stem_verkle:check_root_integrity(RootStem3);
        true -> ok
    end,
    Loc2 = stem_verkle:put(RootStem3, CFG),
    Loc2.
    

verified2([], %this is a lists in lists tree of the things that have changed in the consensus state. We are storing these changes.
          Stem, %this is the current Stem stored on the hard drive. it has pointers to other stems or leaves.
          _) -> 
    %io:fwrite("verified2 finished\n"),
    %there is nothing left to change.
    Stem;
%verified2([{N, 0}], Stem, CFG) -> 
%    verified3(N, Stem, 0, 0, <<0:256>>);
verified2([[{N, 0}]|T], Stem, CFG) -> 
    %there is a spot that was deleted from the stem.
    %io:fwrite("verified2 delete a spot 0\n"),
    Stem2 = verified3(N, Stem, 0, 0, <<0:256>>),
    verified2(T, Stem2, CFG);
verified2([{N, 0}|T], Stem, CFG) -> 
    %there is a spot that was deleted from the stem.
    %io:fwrite("verified2 delete a spot 1\n"),
    Stem2 = verified3(N, Stem, 0, 0, <<0:256>>),
    verified2(T, Stem2, CFG);
verified2([[{N, {Key, Value, Meta}}]|T], 
          Stem, CFG) -> 
    %a leaf was updated, so we need to store the new version.
    %io:fwrite("verified2 update a leaf\n"),
    %io:fwrite(integer_to_list(N)),
    %io:fwrite("\n"),
    Leaf = leaf_verkle:new(Key, Value, Meta, CFG),
    Loc = leaf_verkle:put(Leaf, CFG),
    Stem2 = verified3(
              N, Stem, 2, Loc, 
              leaf_hash(Leaf, CFG)),
    verified2(T, Stem2, CFG);
verified2([[{N, {Key, Value}}]|T], 
          Stem, CFG) -> 
    %io:fwrite("verified2 leaf unchanged\n"),
    %a leaf was unchanged.
    %Leaf = leaf_verkle:new(Key, Value, Meta, CFG),
    %Leaf = leaf_verkle:new(Key, Value, 0, CFG),
    %Loc = element(N+1, Stem#stem.pointers),%leave it unchanged
    %Stem2 = verified3(
    %          N, Stem, 2, Loc, 
    %          leaf_hash(Leaf, CFG)),
    %verified2(T, Stem2, CFG);
    verified2(T, Stem, CFG);
verified2([[{N, B = <<_:1024>>}|T1]|T2], Stem, CFG) ->
    Hash = stem_verkle:hash_point(B),
    verified2([[{N, {mstem, Hash, B}}|T1]|T2], Stem, CFG);
verified2([[{N, {mstem, Hash, B}}|T1]|T2], Stem, CFG) 
  when is_binary(B) -> 
    %io:fwrite("verified2 stem\n"),
    ChildStem = 
        case element(N+1, Stem#stem.types) of
            1 ->%so we need to add the T1 elements to the child stem at position N+1
                io:fwrite("adding elements to a cihld stem\n"),
                ChildStem0 = verified2(T1, stem_verkle:get(element(N+1, Stem#stem.pointers), CFG), CFG),
                ChildStem0#stem{root = B};
            0 ->%so we are creating a new stem for the T1 elements in place of this empty spot at position N+1.
                %io:fwrite("there was an empty spot, possibly creating a stem at that spot\n"),
                S = stem_verkle:new_empty(CFG),
                ChildStem0 = verified2(T1, S, CFG),
                ChildStem0#stem{root = B};
            2 ->%there was a leaf at position N+1. we are creating a new stem, and we need to merge the list of T1 elements with that extra leaf, and store them all in the new stem.
                %io:fwrite("there was a leaf, possibly creating a stem at that spot\n"),
                S = stem_verkle:new_empty(CFG),
                S2 = verified2(T1, S, CFG),
                S2#stem{root = B}
        end,
    if
        ?sanity ->
            stem_verkle:check_root_integrity(ChildStem);
        true -> ok
    end,
    Loc = stem_verkle:put(ChildStem, CFG),
    false = (Hash == uncalculated),
    Stem2 = verified3(N, Stem, 1, Loc, Hash),
    verified2(T2, Stem2, CFG).


verified3(N, Stem, Type, Loc, Hash) ->
    Stem2 = Stem#stem{
      types = setelement(
                N+1, Stem#stem.types, Type),
      pointers = setelement(
                   N+1, Stem#stem.pointers, Loc),
      hashes = setelement(
                 N+1, Stem#stem.hashes, Hash)
     },
    Stem2.

is_in(X, [X|_]) -> true;
is_in(X, [_|T]) ->
    is_in(X, T);
is_in(_, []) -> false.


                
range(X, X) -> [X];
range(X, Y) when (X < Y) -> 
    [X|range(X+1, Y)].

clump_by_path(D, Leaves) ->
    Paths0 = lists:map(
               fun(L) -> 
                       D8 = (31 - D)*8,
                      <<_:D8, B:8, _/binary>> =
                           leaf_verkle:raw_key(L),
                      {B, L} end,
              Leaves),
    Paths = lists:sort(fun({A, _}, {B, _}) ->
                               A < B
                       end, Paths0),
                               
    {Gs, _, _} = parameters:read(),
    clump_by_path2(
      0, length(Gs), Paths, []).
clump_by_path2(I, I, _, _) -> [];
clump_by_path2(I, Limit, [{I, L}|T], C) -> 
    clump_by_path2(I, Limit, T, [L|C]);
clump_by_path2(I, Limit, T, C) -> 
    [C|clump_by_path2(I+1, Limit, T, [])].

split4ways(X) ->
    split4ways(X, [], [], [], []).
split4ways([], A, B, C, D) -> 
    {lists:reverse(A), 
     lists:reverse(B), 
     lists:reverse(C), 
     lists:reverse(D)};
split4ways([{A, B, C, D}|T], W, X, Y, Z) -> 
    split4ways(T, [A|W], [B|X], [C|Y], [D|Z]).

hash_thing(0, 0, empty, _, _) ->
    %type 0 is empty
    <<0:256>>;
hash_thing(_, leaf, leaf_not_recorded, 
           OldHash, _) -> OldHash;
hash_thing(_, stem, stem_not_recorded,
           OldHash, _) -> OldHash;
hash_thing(_, leaf, L = #leaf{}, _, CFG) -> 
    leaf_hash(L, CFG);
hash_thing(_, stem, S = #stem{}, _, _) -> 
    stem_verkle:hash(S).
leaf_hash(L = #leaf{}, CFG) ->
    <<N:256>> = leaf_verkle:hash(L, CFG),
    fr:encode(N).

path_n(_, 0, R) -> R;
path_n(B, N, R) -> 
    N8 = N*8,
    <<_:N8, C, _/binary>> = B,
    path_n(B, N-1, C + (R*256)).
    
    
sort_by_path2(L, CFG) ->
    %this time we want to sort according to the order of a depth first search.
    L2 = lists:map(
           fun(X) ->
                   N = path_n(
                         leaf_verkle:raw_key(X), 31, 0),
                   {N, X}
           end, L),
    L3 = lists:sort(fun({N1, _}, {N2, _}) ->
                       N1 < N2
               end, L2),
    lists:map(fun({_, X}) -> X end, L3).

test(3) ->
    io:fwrite("fprof of storing a batch"),
    CFG = tree:cfg(tree01),
    Loc = 1,
    Times = 200,
    Leaves = 
        lists:map(
          fun(N) -> 
                  <<Key0:256>> = 
                      crypto:strong_rand_bytes(32),
                  leaf_verkle:new(Key0, <<N:16>>, CFG)
                      %#leaf{key = Key0, value = <<N:16>>}%random version
          end, range(1, Times+1)),
    %Many = lists:map(fun(#leaf{key = K}) -> K end,
    %Many = lists:map(fun(Leaf) -> 
    %                         leaf_verkle:raw_key(Leaf) end,
    %                 Leaves),
    fprof:trace(start),
    store_verkle:batch(Leaves, Loc, CFG),
    fprof:trace(stop),
    fprof:profile(file, "fprof.trace"),
    fprof:analyse().
    

    

    
