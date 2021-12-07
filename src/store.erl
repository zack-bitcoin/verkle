-module(store).
-export([store/3, %non-batched store is not needed.
         batch/3]).
-include("constants.hrl").

store(Leaf, RP, CFG) ->
    batch([Leaf], RP, CFG).

batch(Leaves0, RP, CFG) ->%returns {location, stem/leaf, #stem{}/#leaf{}}
    %put them in an ordered list.
    Leaves = sort_by_path2(Leaves0, CFG),
    batch(Leaves, RP, stem, 0, CFG).

batch([], 0, 0, _, _CFG) ->
    %type 0 is empty
    {0, 0, empty};
batch([], P, leaf, _, _CFG) ->
    %don't read the leaf here, because we aren't changing it.
    {P, leaf, leaf_not_recorded};
batch([], P, stem, _, _CFG) ->
    %don't read the stem here, because we aren't changing it.
    {P, stem, stem_not_recorded};
batch([Leaf], 0, 0, _, CFG) ->
    %storing a leaf in a previously empty spot.
    Loc = leaf:put(Leaf, CFG),
    {Loc, leaf, Leaf};
batch(Leaves0, 0, 0, Depth, CFG) ->
    %storing multiple leaves in a previously empty spot.
    batch(Leaves0, 
          1, %1 is always an empty stem.
          stem, Depth, CFG);
batch(Leaves0, RP, leaf, Depth, CFG) ->
    RootLeaf = leaf:get(RP, CFG),
    batch([RootLeaf|Leaves0], 1, stem, Depth, CFG);
batch(Leaves, RP, stem, Depth, CFG) ->
    %cut the list into sub lists that get included in each sub-branch.
    Leaves2 = clump_by_path(Depth, Leaves, CFG),
    %depth first recursion over the sub-lists on teh sub-trees to calculate the pointers and hashes for this node.
    RootStem = stem:get(RP, CFG),
    #stem{
           hashes = Hashes,
           pointers = Pointers,
           types = Types,
           root = Root
         } = RootStem,
    %HPT1 = lists:zipwith3(
    %         fun(H, P, T) -> {H, P, T} end,
    %         Hashes, Pointers, Types),
    HPT1 = lists:map(
             fun(I) -> {element(I, Hashes),
                        element(I, Pointers),
                        element(I, Types)}
             end, range(1, size(Hashes))),
    %maybe we can't zip over batch here if batch is returning the entire stem and leaf. because this ends up filling the ram with all the stems and leaves we will be writing. TODO, stream the rest of the function into this zipwith.
    %io:fwrite({HPT1, Leaves2}),
    RHPT = lists:zipwith(
           fun(Leaves3, {H, P, T}) -> 
                   {P2, Type, Tree} = 
                       batch(Leaves3, P, 
                             T, Depth+1, CFG),
                   H2 = hash_thing(
                          P2, Type, Tree, H, CFG),
                   <<HN:256>> = H,
                   <<HN2:256>> = H2,
                   {(?sub(HN2, HN)), H2, P2, Type}
           end,
            Leaves2, HPT1),
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
    EllDiff = 
        secp256k1:multi_exponent(
          Rs, ?p#p.g, ?p#p.e),
    NewRoot = secp256k1:jacob_add(
                EllDiff, Root, ?p#p.e),
    %[{location, type, #stem{}/#leaf{}}, ...]
    NewStem = 
        RootStem#stem{
          hashes = list_to_tuple(Hashes2),
          pointers = list_to_tuple(Pointers2),
          types = list_to_tuple(Types2),
          root = NewRoot
         },
    Loc = stem:put(NewStem, CFG),
    {Loc, stem, NewStem}.

range(X, X) -> [X];
range(X, Y) when (X < Y) -> 
    [X|range(X+1, Y)].

clump_by_path(D, Leaves, CFG) ->
    Paths = lists:map(
              fun(L) -> 
                      <<B:?nindex>> = 
                          lists:nth(
                            D+1, leaf:path(
                                   L, CFG)),
                      {B, L} end,
              Leaves),
    Result0 = 
        clump_by_path2(
          0, length(?p#p.g), Paths, []),
    remove_pointers(Result0).
remove_pointers({_, B}) -> B;
remove_pointers([]) -> [];
remove_pointers([H|T]) -> 
    [remove_pointers(H)|
     remove_pointers(T)].
clump_by_path2(I, Limit, _, C) 
  when (I == Limit) -> C;
clump_by_path2(I, Limit, [], C) -> 
    [lists:reverse(C)|
     clump_by_path2(I+1, Limit, [], [])];
clump_by_path2(I, Limit, [{I, L}|T], C) -> 
    clump_by_path2(I, Limit, T, [{I, L}|C]);
clump_by_path2(I, Limit, T, C) -> 
    [lists:reverse(C)|
     clump_by_path2(I+1, Limit, T, [])].

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
    leaf:hash(L, CFG);
hash_thing(_, stem, S = #stem{}, _, _) -> 
    stem:hash(S).
sort_by_path2(L, CFG) ->
    %this time we want to sort according to the order of a depth first search.
    lists:sort(
      fun(A, B) ->
              K1 = leaf:path(A, CFG),
              K2 = leaf:path(B, CFG),
              K1 < K2
      end, L).
