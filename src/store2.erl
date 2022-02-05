-module(store2).
-export([store/3, %non-batched store is not needed.
         batch/3,
         multi_exponent_parameters/2,
         test/1,
         precomputed_multi_exponent/2,
         leaf_hash/2
        ]).
%-include("constants.hrl").
-define(nindex, 8).
-record(stem, { root
                , types
                , pointers
                , hashes
	      }).
-record(leaf, { key
	      , value
	      , meta = 0 %meta is data we want to remember that doesn't get hashed into the merkle tree.
	      }).

store(Leaf, RP, CFG) ->
    batch([Leaf], RP, CFG).

batch(Leaves0, RP, CFG) ->%returns {location, stem/leaf, #stem{}/#leaf{}}
    %put them in an ordered list.
    io:fwrite("store sorting 0\n"),
    % 2%
    Leaves = sort_by_path2(Leaves0, CFG),
    io:fwrite("store parameters 1\n"),
    MEP = parameters2:multi_exp(),
    io:fwrite("store storing 1\n"),
    batch(Leaves, RP, stem, 0, CFG, MEP).

batch([], 0, 0, _, _CFG, _) ->
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
                Depth, Leaves, CFG),
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
    %maybe we can't zip over batch here if batch is returning the entire stem and leaf. because this ends up filling the ram with all the stems and leaves we will be writing. consider streaming the rest of the function into this zipwith.
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
    EllDiff = precomputed_multi_exponent(Rs, MEP),

    % 3.6%
    NewRoot = fq2:e_add(EllDiff, Root),
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
    Loc = stem2:put(NewStem, CFG), %   %60!!
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
    {Gs, _, _} = parameters2:read(),
    Result0 = 
        clump_by_path2(
          0, length(Gs), Paths, []),
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
    leaf_hash(L, CFG);
hash_thing(_, stem, S = #stem{}, _, _) -> 
    stem2:hash(S).
leaf_hash(L, CFG) ->
    <<N:256>> = leaf:hash(L, CFG),
    fr:encode(N).
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
         fq2:e_add(X, Base),
         Times - 1)].
det_pow(0, _) -> 0;
det_pow(_, 0) -> 1;
det_pow(A, 1) -> A;
det_pow(A, N) when ((N rem 2) == 0) -> 
    det_pow(A*A, N div 2);
det_pow(A, N) -> 
    A*det_pow(A, N-1).
multi_exponent_parameters(C, Gs) ->
    io:fwrite("calculating 256 multi exponent parameters\n"),
    F = det_pow(2, C),
    L = lists:zipwith(
          fun(G, R) ->
                  String = "ME # " ++ integer_to_list(R) ++ "\n",
                  %io:fwrite(String),
                  X = multi_exponent_parameters2(
                        G, fq2:e_zero(), F),
                  X3 = fq2:e_simplify_batch(X),
                  list_to_tuple(X3)
          end, Gs, range(1, length(Gs))),
    io:fwrite("multi exponent parameters done\n"),
    list_to_tuple(L).
batch_chunkify2(_Rs, _, 0) -> [];
batch_chunkify2(Rs, C, Lim) -> 
    {N, Rs2} = batch_chunkify3(Rs, C, [], []),
    [N|batch_chunkify2(Rs2, C, Lim-1)].
batch_chunkify3([], C, N, A) -> 
    {lists:reverse(N), lists:reverse(A)};
batch_chunkify3(
  [<<N:8, A/binary>>|Rs], C, Ns, As) ->
    %I think this N is 8 bits long, becuase the value of C in parameters.erl is 8.
    batch_chunkify3(Rs, C, [N|Ns], [A|As]).
batch_chunkify(_Rs, _, 0) -> [];
batch_chunkify(Rs, F, Lim) -> 
    N = lists:map(fun(R) ->
                          R rem F
                  end, Rs),
    Rs2 = lists:map(fun(R) ->
                            R div F
                    end, Rs),
    [N|batch_chunkify(Rs2, F, Lim-1)].
    
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

precomputed_multi_exponent(Rs0, MEP) ->
    %we want to do part of the bucket algorithm, but since the generator points are all known ahead of time, we want to use precalculated values where possible.
    %n = 2, C = 10 -> 128*2/8 -> 32.
    Domain0 = parameters2:domain(),
    {Domain, Rs} = get_domain(% 0.4%
                     Domain0, Rs0, [], []),
    C = 8,
    F = det_pow(2, C),
    B = 256,
    %bitcoin has 19 leading zeros in hexidecimal format. around 80 bits per block.
    Lim = ceil(B / C),
%    R_chunks = 
%        lists:map(
%          fun(R) -> L = chunkify(R, F, Lim),
%                    lists:reverse(L),
%                    L
%          end, Rs),
    %Rs2 = lists:map(fun(R) -> <<R:256>> end, Rs),
    %Rs2 = to_binaries(Rs),%almost 0.
%    Rs2 = lists:map(fun(X) -> <<(fr:decode(X)):256>> end, Rs),
%    Ts = lists:reverse(
%            batch_chunkify2(Rs2, C, Lim)),%8.9

    % 14% of storage
    Ts = batch_chunkify(
           fr:decode(Rs), F, Lim),

    %  4.5% of storage
    Mepl = tuple_to_list(MEP),
    EZero = fq2:e_zero(),
    Ss = lists:map(
           fun(T) ->
                   pme22(T, Mepl, EZero)
           end, Ts),

    % 3.5% of storage
    Result = multi_exponent:me3(
               lists:reverse(Ss), 
               EZero, 
               fr:encode(F)),%  5%
    Result.
                      
    %Now the problem has been broken into 256/C instances of multi-exponentiation.
    %each multi-exponentiation has length(Gs) parts. What is different is that instead of the exponents having 256 bits, they only have C bits. each multi-exponentiation makes [T1, T2, T3...]
    %Each row is an instance of a multi-exponential problem, with C-bit exponents. We will use the precalculated parameters for this.
%io:fwrite(Ts),

pme22([], [], Acc) -> Acc;
pme22([0|T], [_|D], Acc) -> 
    pme22(T, D, Acc);
pme22([Power|T], [H|MEP], Acc) -> 
    X = element(Power+1, H),
    Acc2 = fq2:e_add(X, Acc),
    pme22(T, MEP, Acc2).
    
    

many(_, 0) -> [];
many(A, N) when N > 0 -> 
    [A|many(A, N-1)].

test(1) ->
    verkle_app:start(normal, []),
    R1 = ([1|many(0, 255)]),
    R2 = ([0,1|many(0, 254)]),
    R3 = ([2|many(0, 255)]),
    R4 = ([0,2|many(0, 254)]),
    R = R4,
    {Gs, _, _} = parameters2:read(),
    Old = multi_exponent:doit(fr:encode(R), Gs),
    MEP = parameters2:multi_exp(),
    New = precomputed_multi_exponent(
            R, MEP), 
    %Saved0 = element(2, element(1, MEP)),
%    Saved0 = element(2, element(2, MEP)),
%    Saved = secp256k1:to_affine(secp256k1:jacob_add(Saved0, Saved0, ?p#p.e)),
    %Saved1 = element(2, element(2, MEP)),
    %io:fwrite({Old, New, Saved0}),
    fq2:eq(Old, New);
test(2) ->
    io:fwrite("ftrace of precomputed multi exponent\n"),
    %multi exponent precompute speed comparison.
    %verkle_app:start(normal, []),
    Many = 20,
    Rs = lists:map(fun(_) ->
                           <<X:256>> = crypto:strong_rand_bytes(32),
                           fr:encode(X)
                   end, range(1, 256)),
    MEP = parameters2:multi_exp(),
    T1 = erlang:timestamp(),
    fprof:trace(start),
    lists:map(fun(_) ->
                      precomputed_multi_exponent(
                        Rs, MEP)%72000
              end, range(1, Many)),
    fprof:trace(stop),
%fprof:analyse().
    T2 = erlang:timestamp(),
%    lists:map(fun(_) ->
%                      secp256k1:multi_exponent(
%                        Rs, Gs, E)%125000
%              end, range(1, Many)),
    T3 = erlang:timestamp(),
    {timer:now_diff(T2, T1)/Many,
     timer:now_diff(T3, T2)/Many},
    fprof:profile(file, "fprof.trace"),
    fprof:analyse();
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
                  #leaf{key = Key0, value = <<N:16>>}%random version
          end, range(1, Times+1)),
    Many = lists:map(fun(#leaf{key = K}) -> K end,
                     Leaves),
    fprof:trace(start),
    store2:batch(Leaves, Loc, CFG),
    fprof:trace(stop),
    fprof:profile(file, "fprof.trace"),
    fprof:analyse().
    

    

    
