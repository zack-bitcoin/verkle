%The purpose of this file is to define stems as a data structure in ram, and give some simple functions to operate on them.

-module(stem_verkle).
-export([test/1,get/2,put/2,put/3,type/2,
         hash/1,hash_point/1,hash_points/1,
         pointers/1,
	 types/1,hashes/1,pointer/2,%new/5,%add/5,
	 new_empty/1,%recover/6, 
         empty_hashes/1, 
	 update_pointers/2, empty_tuple/0,
	 make/3, make/2, update/3, onify2/2,
	 put_batch/2, %serialize/2,
         root/1, check_root_integrity/1,
	 empty_trie/2]).
%-include("constants.hrl").
%-export_type([stem/0,types/0,empty_t/0,stem_t/0,leaf_t/0,pointers/0,empty_p/0,hashes/0,hash/0,empty_hash/0,stem_p/0,nibble/0]).
-define(sanity, false).
-record(stem, { root = ed:extended_zero()
                , types
                , pointers
                , hashes
	      }).
-define(nwidth, 256).

root(X) ->
    X#stem.root.
empty_tuple() -> 
    X = many(0, ?nwidth),
    list_to_tuple(X).
many(_, 0) -> [];
many(X, N) when (N > 0) -> 
    [X|many(X, N-1)].
new_empty(CFG) -> 
    #stem{hashes = empty_hashes(CFG),
         types = empty_tuple(),
         pointers = empty_tuple(),
         root = ed:extended_zero()}.
%unused_recover(M, T, P, H, Hashes, CFG) ->
%    Types = onify2(Hashes, CFG),
    %Types = list_to_tuple(onify(tuple_to_list(Hashes), CFG)),
%    S = #stem{hashes = Hashes, types = Types},
%    unused_add(S, M, T, P, H).
onify2(H, CFG) ->
    list_to_tuple(onify(tuple_to_list(H), CFG)).
onify([], _) -> [];
onify([H|T], CFG) ->
    HS = cfg:hash_size(CFG)*8,
    <<X:HS>> = H,
    case X of
	0 -> [0|onify(T, CFG)];
	_ -> [1|onify(T, CFG)]
    end.
	    
%onify([<<0:_>>|T]) -> [0|onify(T)];
%onify([_|T]) -> [1|onify(T)].
make(Hashes, ID) ->
    CFG = tree:cfg(ID),
    Types = onify2(Hashes, CFG),
    Pointers = empty_tuple(),
    make(Types, Pointers, Hashes).
make(Types, Pointers, Hashes) ->
    #stem{types = Types,
	  pointers = Pointers,
	  hashes = Hashes}.
%unused_new(N, T, P, H, CFG) ->
    %N is the nibble being pointed to.
    %T is the type, P is the pointer, H is the Hash
%    S = new_empty(CFG),
%    unused_add(S, N, T, P, H).
pointers(R) -> R#stem.pointers.
update_pointers(Stem, NP) ->
    Stem#stem{pointers = NP}.
types(R) -> R#stem.types.
hashes(R) -> R#stem.hashes.
pointer(N, R) ->
    T = pointers(R),
    element(N, T).
type(N, R) ->
    T = types(R),
    element(N, T).
serialize(S, CompressedRoot, CFG) ->
    if
        ?sanity ->
            check_root_integrity(S);
        true -> ok
    end,
    #stem{
           pointers = P,
           hashes = H,
           types = T,
           root = Root
         } = S,
    <<R1:512>> = CompressedRoot,
    X = serialize2(tuple_to_list(P), 
                   tuple_to_list(H), 
                   tuple_to_list(T), 
                   []),
    <<R1:512, X/binary>>.
serialize(S, CFG) ->
    if
        ?sanity ->
            check_root_integrity(S);
        true -> ok
    end,
    #stem{
           pointers = P,
           hashes = H,
           types = T,
           root = Root
         } = S,
    %TODO. this is slow and could be batched.
    [<<R1:512>>] = 
        ed:extended2affine_batch([Root]),% 2%
    X = serialize2(tuple_to_list(P), 
                   tuple_to_list(H), 
                   tuple_to_list(T), 
                   []),
    <<R1:512, X/binary>>.

serialize2([], [], [], R) -> 
    erlang:iolist_to_binary(
      lists:reverse(R));
serialize2([P|PT], [H|HT], [T|TT], R) -> 
    N = <<T, P:256, H/binary>>,
    serialize2(PT, HT, TT, [N|R]).

deserialize(<<R1:512, B/binary>>, CFG) -> 
%deserialize(<<R1:(256*5), B/binary>>, CFG) -> 
    X = empty_tuple(),
    %deserialize(1,X,X,cfg:path(CFG)*8,hash:hash_depth()*8,X, B).
    HS = cfg:hash_size(CFG),
    %Y = deserialize(1,X,X,X, B), % 50% of store and make_proof.
    Y = deserialize2([],[],[], B),
    R = ed:affine2extended(<<R1:512>>),
    %R = <<R1:(256*5)>>,
            
    Result = Y#stem{root = R},
    if
        ?sanity ->
            check_root_integrity(Result);
        true -> ok
    end,
    Result.
deserialize(?nwidth + 1, T,P,H, <<>>) -> 
    #stem{types = T, pointers = P, hashes = H};
deserialize(N, T0,P0,H0,X) when N < (?nwidth + 1) ->
    %<<T:2, P:Path, H:HashDepth, D/bitstring>> = X,
    <<T, P:256, H:256, D/binary>> = X,
    T1 = setelement(N, T0, T),
    P1 = setelement(N, P0, P),
    H1 = setelement(N, H0, <<H:256>>),
    deserialize(N+1, T1, P1, H1, D).

deserialize2(T, P, H, <<>>) ->
    #stem{types = list_to_tuple(
                    lists:reverse(T)),
          pointers = list_to_tuple(
                       lists:reverse(P)),
          hashes = list_to_tuple(
                     lists:reverse(H))};
deserialize2(TT, PT, HT, 
             <<T, P:256, H:256, R/binary>>) ->
    deserialize2([T|TT], [P|PT], [<<H:256>>|HT], R).

empty_hashes(CFG) ->
    %HS = cfg:hash_size(CFG),
    %X = hash:hash_depth()*8,
    %X = HS * 8,
    Y = many(<<0:256>>, ?nwidth),
    list_to_tuple(Y).

hash(S) ->
    if
        ?sanity ->
            check_root_integrity(S);
        true -> ok
    end,
    P = S#stem.root,
    hash_point(P).
hash_point(P) ->
    P2 = ed:e_mul(P, <<8:256/little>>),
    %P2 = ed:affine2extended(P),
    [<<X:256>>] = ed:compress_points([P2]),
    fr:encode(X).
hash_points(L) ->
    L2 = lists:map(fun(X) ->
                           ed:e_mul(X, <<8:256/little>>)
                   end, L),
    L3 = ed:compress_points(L2),
    lists:map(fun(<<X:256>>) -> fr:encode(X) end,
              L3).

update(Location, Stem, CFG) ->
    dump:update(Location, serialize(Stem, CFG), ids:stem(CFG)).

check_root_integrity(Stem) ->
    MEP = parameters:multi_exp(),
    Hashes = tuple_to_list(Stem#stem.hashes),
    R = store_verkle:precomputed_multi_exponent(
          Hashes,MEP),
    {Gs, Hs, Q} = parameters:read(),
    R2 = multi_exponent:doit(Hashes, Gs),
    true = ed:e_eq(R, R2),
    true = ed:e_eq(R, Stem#stem.root),
    true = ed:e_eq(R2, Stem#stem.root).
put(Stem, CompressedRoot, CFG) ->
    %compressed root is in affine format. 64 bytes.
    S = serialize(Stem, CompressedRoot, CFG),
    ID = ids:stem(CFG),
    dump:put(S, ID).
put(Stem, CFG) ->
    S = serialize(Stem, CFG),
    ID = ids:stem(CFG),
    dump:put(S, ID).
put_batch(Leaves, CFG) ->
    %unused
    SL = serialize_stems(Leaves, CFG),
    dump:put_batch(SL, ids:stem(CFG)).

serialize_stems(L, CFG) when false ->
    %L is like [{N, #stem{}}, {N2, #stem{}}, ...]
    ERoots = 
        lists:map(
          fun({_, #stem{
                 %pointers = P, hashes = H, 
                 %types = T, 
                 root = Root}}) ->
                  Root
          end, L),
    Roots = ed:extended2affine_batch(ERoots),
    Bins = lists:zipwith(
             fun({_, Stem = #stem{pointers = P, 
                           hashes = H, 
                           types = T}}, R) ->
                     if
                         ?sanity ->
                             check_root_integrity(Stem);
                         true -> ok
                     end,
                     B = serialize2(
                           tuple_to_list(P), 
                           tuple_to_list(H), 
                           tuple_to_list(T), 
                           []),
                     <<R/binary, B/binary>>
             end, L, Roots),
    lists:zipwith(fun({N, _}, B) ->
                          {N, B}
                  end, L, Bins);
serialize_stems([], _) -> [];
serialize_stems([{N, L}| T], CFG) ->
    [{N, serialize(L, CFG)}|serialize_stems(T, CFG)].
get(Pointer, CFG) -> 
    true = Pointer > 0,
    S = dump:get(Pointer, ids:stem(CFG)),
    deserialize(S, CFG).
empty_trie(Root, CFG) ->
    Stem = get(Root, CFG),
    update_pointers(Stem, empty_tuple()).

equal(S, T) ->
    %[R2, R3] = fq:e_simplify_batch(
    [R2, R3] = ed:normalize(
                 [S#stem.root, T#stem.root]),
    S2 = S#stem{
           root = R2
          },
    T2 = T#stem{
           root = R3
          },
    S2 == T2.

range(N, N) -> [N];
range(A, B) when A < B -> 
    [A|range(A+1, B)].
    
test(1) ->
    P = list_to_tuple(many(5, ?nwidth)),
    T = list_to_tuple(many(1, ?nwidth)),
    %P = {6,5,4,3,7,8,9,4,5,3,2,6,7,8,3,4},
    %T = {0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    %CFG = cfg:new(1, 9, 2, trie), %path value id meta hash_size
    io:fwrite("before start\n"),
    verkle_app:start(normal, []),
    CFG = tree:cfg(trie01),
%{cfg,5,2,trie01,2,32} path, value, id, meta, hash_size
%596 total, average 37.25
    H = empty_hashes(CFG),
    S = #stem{types = T, pointers = P, hashes = H},
    S2 = serialize(S, CFG),
    Sb = deserialize(S2, CFG),
    %io:fwrite({size(?p)}),%9
    %io:fwrite({S#stem.root, Sb#stem.root}),
    true = equal(S, Sb),
    %true = fq:eq(S#stem.root, Sb#stem.root),
    io:fwrite("before equal\n"),
    true = ed:e_eq(S#stem.root, Sb#stem.root),
    Hash = hash:doit(<<>>),
    %Stem = unused_add(S, 3, 1, 5, Hash),
    %hash(Stem),
    %testing reading and writing to the hard drive.
    Pointer = stem_verkle:put(S, CFG),
    Stem2b = get(Pointer, CFG),
    io:fwrite("next equal\n"),
    true = equal(Stem2b, S),
    success;
test(2) ->
    %binary vs bitstring speed.
    T1 = erlang:timestamp(),
    Many = 10000,
    R = range(1, Many),
    lists:foldl(fun(_, _) ->
                        <<45:33>>
                end, 0, R),
    T2 = erlang:timestamp(),
    lists:foldl(fun(_, _) ->
                        <<45:32>>
                end, 0, R),
    T3 = erlang:timestamp(),
    {timer:now_diff(T2, T1),
     timer:now_diff(T3, T2)};
test(3) ->
    %stem hash is the same as the finite field version.
    AB = ed:affine_base(),
    B = ed:affine2extended(AB),
    H = hash_point(B),

    H2 = ed25519:fhash_point(ed25519:fbase_point()),

    {H, fr:decode(H), H2}.


    

    
