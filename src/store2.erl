-module(store2).
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
    io:fwrite("store sorting 0\n"),
    % 2%
    Leaves = sort_by_path2(Leaves0, CFG),
    io:fwrite("store parameters 1\n"),
    MEP = parameters2:multi_exp(),
    io:fwrite("store storing 1\n"),
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
    %storing a leaf in a previously empty spot.
    Loc = leaf:put(Leaf, CFG),
    {Loc, leaf, Leaf};
batch(Leaves0, 0, 0, Depth, CFG, MEP) ->
    %storing multiple leaves in a previously empty spot.
    batch(Leaves0, 
          1, %1 is always an empty stem.
          stem, Depth, CFG, MEP);
batch(Leaves0, RP, leaf, Depth, CFG, MEP) ->
    RootLeaf = leaf:get(RP, CFG),
    batch([RootLeaf|Leaves0], 1, stem, 
          Depth, CFG, MEP);
batch(Leaves, RP, stem, Depth, CFG, MEP) ->
    %cut the list into sub lists that get included in each sub-branch.
    % %6
    Leaves2 = clump_by_path(
                Depth, Leaves),
    %depth first recursion over the sub-lists on teh sub-trees to calculate the pointers and hashes for this node.
    RootStem = stem2:get(RP, CFG),
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
                   {P2, Type, Tree} = 
                       batch(Leaves3, P, 
                             T, Depth+1, CFG, MEP),
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
    %{Gs, _, _} = parameters2:read(),
    %EllDiff = multi_exponent:doit(Rs, Gs),

    % 3.6%
    NewRoot = ed:e_add(EllDiff, Root),
    %NewRoot2 = fq:e_add(Root, EllDiff),
    %true = fq:eq(NewRoot, NewRoot2),
    %<<HP:256>> = fq:hash_point(NewRoot),
    if
        (NewRoot == error) -> io:fwrite({EllDiff, Root});
        true -> ok
    end,
    [Affine] = ed:extended2affine_batch([NewRoot]),
    %[<<HP:256>>] = ed:compress_points([Affine]),
    %io:fwrite({size(EllDiff), size(Root), fq:decode_extended(NewRoot)}),
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
    Loc = stem2:put(NewStem, Affine, CFG), 
    {Loc, stem, NewStem}.


verified(Loc, ProofTree, CFG) ->
    RootStem = stem2:get(Loc, CFG),
    RootStem2 = verified2(tl(ProofTree), RootStem, CFG),
    RootStem3 = 
        RootStem2#stem{root = hd(ProofTree)},
    if
        ?sanity ->
            stem2:check_root_integrity(RootStem3);
        true -> ok
    end,
    Loc2 = stem2:put(RootStem3, CFG),
    Loc2.
    

verified2([], Stem, _) -> Stem;
%verified2([{N, 0}], Stem, CFG) -> 
%    verified3(N, Stem, 0, 0, <<0:256>>);
verified2([[{N, 0}]|T], Stem, CFG) -> 
    Stem2 = verified3(N, Stem, 0, 0, <<0:256>>),
    verified2(T, Stem2, CFG);
verified2([{N, 0}|T], Stem, CFG) -> 
    Stem2 = verified3(N, Stem, 0, 0, <<0:256>>),
    verified2(T, Stem2, CFG);
verified2([[{N, {Key, Value}}]|T], Stem, CFG) -> 
    Leaf = leaf:new(Key, Value, 0, CFG),
    Loc = leaf:put(Leaf, CFG),
    Stem2 = verified3(
              N, Stem, 2, Loc, 
              leaf_hash(Leaf, CFG)),
    verified2(T, Stem2, CFG);
verified2([[{N, B = <<_:1024>>}|T1]|T2], Stem, CFG) ->
    Hash = stem2:hash_point(B),
    %Hash = ed:compress_point(B),
    verified2([[{N, {mstem, Hash, B}}|T1]|T2], Stem, CFG);
verified2([[{N, {mstem, Hash, B}}|T1]|T2], Stem, CFG) 
  when is_binary(B) -> 
    1 = element(N+1, Stem#stem.types),
    ChildStem0 = verified2(T1, stem2:get(element(N+1, Stem#stem.pointers), CFG), CFG),
    ChildStem = ChildStem0#stem{root = B},
    if
        ?sanity ->
            stem2:check_root_integrity(ChildStem);
        true -> ok
    end,
    %io:fwrite(size(ChildStem#stem.root)),
    Loc = stem2:put(ChildStem, CFG),
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
                
range(X, X) -> [X];
range(X, Y) when (X < Y) -> 
    [X|range(X+1, Y)].

clump_by_path(D, Leaves) ->
    Paths0 = lists:map(
               fun(L) -> 
                       D8 = (31 - D)*8,
                      <<_:D8, B:8, _/binary>> =
                           leaf:raw_key(L),
                      {B, L} end,
              Leaves),
    Paths = lists:sort(fun({A, _}, {B, _}) ->
                               A < B
                       end, Paths0),
                               
    {Gs, _, _} = parameters2:read(),
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
    stem2:hash(S).
leaf_hash(L = #leaf{}, CFG) ->
    <<N:256>> = leaf:hash(L, CFG),
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
                         leaf:raw_key(X), 31, 0),
                   {N, X}
           end, L),
    L3 = lists:sort(fun({N1, _}, {N2, _}) ->
                       N1 < N2
               end, L2),
    lists:map(fun({_, X}) -> X end, L3).

test(3) ->
    io:fwrite("fprof of storing a batch"),
    CFG = trie:cfg(trie01),
    Loc = 1,
    Times = 200,
    Leaves = 
        lists:map(
          fun(N) -> 
                  <<Key0:256>> = 
                      crypto:strong_rand_bytes(32),
                  leaf:new(Key0, <<N:16>>, CFG)
                      %#leaf{key = Key0, value = <<N:16>>}%random version
          end, range(1, Times+1)),
    %Many = lists:map(fun(#leaf{key = K}) -> K end,
    %Many = lists:map(fun(Leaf) -> 
    %                         leaf:raw_key(Leaf) end,
    %                 Leaves),
    fprof:trace(start),
    store2:batch(Leaves, Loc, CFG),
    fprof:trace(stop),
    fprof:profile(file, "fprof.trace"),
    fprof:analyse().
    

    

    
