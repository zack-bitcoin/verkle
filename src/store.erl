-module(store).
-export([store/3, %non-batched store is not needed.
         batch/3,
         multi_exponent_parameters/1,
         test/0
        ]).
-include("constants.hrl").

store(Leaf, RP, CFG) ->
    batch([Leaf], RP, CFG).

batch(Leaves0, RP, CFG) ->%returns {location, stem/leaf, #stem{}/#leaf{}}
    %put them in an ordered list.
    io:fwrite("store sorting 0\n"),
    Leaves = sort_by_path2(Leaves0, CFG),
    io:fwrite("store storing 1\n"),
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
                   {(?sub2(HN2, HN)), %often times this is calculating 0. we should know it is zero without doing the subtraction. todo 
                    H2, P2, Type}
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
%    EllDiff = 
%        secp256k1:multi_exponent(
%          Rs, ?p#p.g, ?p#p.e),
    EllDiff = precomputed_multi_exponent(Rs),
%    true = secp256k1:jacob_equal(EllDiff, EllDiff2, ?p#p.e),
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
                      %todo, instead of doing nth here, maybe we should look at the key as an integer and do some modulus and division to get the part we want.
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
multi_exponent_parameters2(_, X, 0) -> [X];
multi_exponent_parameters2(Base, X, Times) ->
    [X|multi_exponent_parameters2(
         Base, 
         secp256k1:jacob_add(Base, X, ?p#p.e),
         Times - 1)].
multi_exponent_parameters(C) ->
    Gs = ?p#p.g,
    F = secp256k1:det_pow(2, C),
    L = lists:map(
          fun(G) ->
                  X = multi_exponent_parameters2(
                        G, secp256k1:jacob_zero(), 
                        F),
                  X3 = 
                      secp256k1:simplify_Zs_batch(
                        X),
                  list_to_tuple(X3)
          end, Gs),
    list_to_tuple(L).
chunkify(_, _, 0) -> [];
chunkify(R, C, Many) -> 
    [(R rem C)|
     chunkify(R div C, C, Many-1)].
matrix_diagonal_flip([[]|_]) -> [];
matrix_diagonal_flip(M) ->
    Col = lists:map(fun(X) -> hd(X) end, M),
    Tls = lists:map(fun(X) -> tl(X) end, M),
    [Col|matrix_diagonal_flip(Tls)].
get_domain([], [], D, R) ->
    {lists:reverse(D),
     lists:reverse(R)};
get_domain([D|DT], [0|RT], Ds, Rs) ->
    get_domain(DT, RT, Ds, Rs);
get_domain([D|DT], [R|RT], Ds, Rs) ->
    get_domain(DT, RT, [D|Ds], [R|Rs]).

precomputed_multi_exponent(Rs0) ->
    %we want to do part of the bucket algorithm, but since the generator points are all known ahead of time, we want to use precalculated values where possible.
    %in bucketify/5, instead of storing G3 in the 5th bucket, look up G3*5, and just add that to the running sum. 
    %so we don't need bucketify2. saving 2*2^c additions.
    %but, bucketify has 1 extra addition per bucket, so 2^c extra additions.

    %normal bucket algorithm costs (256/c)(n + 2^c).

    %c=10, n=2, -> 25.6*(2+1024) -> 26000


    %compare bucket efficiency to another strategy:

    %n = many things multi-exponentiating.

    %n=1. double and add.
    %256 doubles, 128 adds.
    
    %n = 2. double and add, with simultanious doubling.
    %256 doubles, 256 adds.

    %if we remember 2^C multiples of each G.
    %256 doubles, 128*n/c adds

    %n = 2, C = 10 -> 128*2/8 -> 32.
    {Domain, Rs} = get_domain(
                     ?p#p.domain, Rs0, [], []),
    C = 8,
    F = secp256k1:det_pow(2, C),
    B = 256,
    %bitcoin has 19 leading zeros in hexidecimal format. around 80 bits per block.
    Lim = ceil(B / C),
    R_chunks = 
        lists:map(
          fun(R) -> L = chunkify(R, F, Lim),
                    lists:reverse(L),
                    L
          end, Rs),
    Ts = matrix_diagonal_flip(R_chunks),
    Ss = lists:map(
           fun(T) ->
                   %this is the slow part.
                   pme2(T, Domain, 0, 
                        secp256k1:jacob_zero())
           end, Ts),
    Result = secp256k1:me3(lists:reverse(Ss), 
                  secp256k1:jacob_zero(), 
                           F, ?p#p.e),
    Result.
                      
    %Now the problem has been broken into 256/C instances of multi-exponentiation.
    %each multi-exponentiation has length(Gs) parts. What is different is that instead of the exponents having 256 bits, they only have C bits. each multi-exponentiation makes [T1, T2, T3...]
    %Each row is an instance of a multi-exponential problem, with C-bit exponents. We will use the precalculated parameters for this.
%io:fwrite(Ts),

    %    secp256k1:multi_exponent(
    %      Rs, ?p#p.g, ?p#p.e),
%    lists:zipwith(fun(D, R) ->
%                      pme2(D, R)
%              end, ?p#p.domain, Rs),
    %then sum up the results.
%    ok.
pme2([], [], _MEP, Acc) -> Acc;
pme2([0|T], [_|Domain], MEP, Acc) ->
    pme2(T, Domain, MEP, Acc);
pme2([Power|T], [Gid|Domain], MEP, Acc) ->
%    X = element(
%          Power+1,
%          element(
%            Gid, MEP)),
    X = parameters:multi_exp(Gid, Power+1),
    Acc2 = secp256k1:jacob_add(
             X, Acc, ?p#p.e),
    pme2(T, Domain, MEP, Acc2).
    

many(_, 0) -> [];
many(A, N) when N > 0 -> 
    [A|many(A, N-1)].

test() ->
    verkle_app:start(normal, []),
    R1 = [1|many(0, 255)],
    R2 = [0,1|many(0, 254)],
    R3 = [2|many(0, 255)],
    R4 = [0,2|many(0, 254)],
    R = R4,
    Old0 = secp256k1:multi_exponent(
            R, ?p#p.g, ?p#p.e),
    Old = secp256k1:to_affine(Old0),
    New = precomputed_multi_exponent(R), 
    MEP = parameters:multi_exp(),
    %Saved0 = element(2, element(1, MEP)),
    Saved0 = element(2, element(2, MEP)),
    Saved = secp256k1:to_affine(secp256k1:jacob_add(Saved0, Saved0, ?p#p.e)),
    %Saved1 = element(2, element(2, MEP)),
    %io:fwrite({Old, New, Saved0}),
    secp256k1:jacob_equal(Old0, New, ?p#p.e).
    
