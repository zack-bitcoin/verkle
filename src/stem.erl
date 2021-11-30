%The purpose of this file is to define stems as a data structure in ram, and give some simple functions to operate on them.

-module(stem).
-export([test/0,get/2,put/2,type/2,hash/1,pointers/1,
	 types/1,hashes/1,pointer/2,new/7,add/7,
	 new_empty/1,recover/8, empty_hashes/1, 
	 update_pointers/2, empty_tuple/0,
	 make/3, make/2, update/3, onify2/2,
	 put_batch/2, serialize/2,
         root/1,
	 empty_trie/2]).
-include("constants.hrl").
%-export_type([stem/0,types/0,empty_t/0,stem_t/0,leaf_t/0,pointers/0,empty_p/0,hashes/0,hash/0,empty_hash/0,stem_p/0,nibble/0]).
-record(stem, { types = empty_tuple()
                , pointers = empty_tuple()
                , hashes
                , root = secp256k1:jacob_zero()
	      }).
root(X) ->
    X#stem.root.
empty_tuple() -> 
    X = many(0, ?nwidth),
    list_to_tuple(X).
many(_, 0) -> [];
many(X, N) when (N > 0) -> 
    [X|many(X, N-1)].
add(S, N, T, P, <<H:256>>, Gs, E) ->
    %Gs are the generator points for the pedersen commits.
    #stem{
     types = Ty,
     pointers = Po,
     hashes = Ha,
     root = Root
    } = S,
    M = N+1,
    <<Old:256>> = element(M, Ha),
    %for generator M, subtract Old and add H.
    G = lists:nth(M, Gs),
    Diff = secp256k1:jacob_mul(G, H-Old, E),
    Root2 = secp256k1:jacob_add(Root, Diff, E),
    T2 = setelement(M, Ty, T),
    P2 = setelement(M, Po, P),
    H2 = setelement(M, Ha, <<H:256>>),
    #stem{types = T2, pointers = P2, 
          hashes = H2, root = Root2}.
new_empty(CFG) -> #stem{hashes = empty_hashes(CFG)}.
recover(M, T, P, H, Hashes, CFG, Gs, E) ->
    Types = onify2(Hashes, CFG),
    %Types = list_to_tuple(onify(tuple_to_list(Hashes), CFG)),
    S = #stem{hashes = Hashes, types = Types},
    add(S, M, T, P, H, Gs, E).
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
    CFG = trie:cfg(ID),
    Types = onify2(Hashes, CFG),
    Pointers = empty_tuple(),
    make(Types, Pointers, Hashes).
make(Types, Pointers, Hashes) ->
    #stem{types = Types,
	  pointers = Pointers,
	  hashes = Hashes}.
new(N, T, P, H, CFG, Gs, E) ->
    %N is the nibble being pointed to.
    %T is the type, P is the pointer, H is the Hash
    S = new_empty(CFG),
    add(S, N, T, P, H, Gs, E).
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
serialize(S, CFG) ->
    Path = cfg:path(CFG)*8,
    #stem{
           pointers = P,
           hashes = H,
           types = T,
           root = Root
         } = S,
    {R1, R2} = secp256k1:to_affine(Root),
    X = serialize(P, H, T, Path, 1),
    <<R1:256, R2:256, X/binary>>.
serialize(_, _, _, _, N) when N>?nwidth -> <<>>;
serialize(P, H, T, Path, N) -> 
    P1 = element(N, P),
    H1 = element(N, H),
    T1 = element(N, T),
    D = serialize(P, H, T, Path, N+1),
    << T1:2, P1:Path, H1/binary, D/bitstring >>.
deserialize(<<R1:256, R2:256, B/binary>>, CFG) -> 
    X = empty_tuple(),
    %deserialize(1,X,X,cfg:path(CFG)*8,hash:hash_depth()*8,X, B).
    HS = cfg:hash_size(CFG),
    Y = deserialize(1,X,X,cfg:path(CFG)*8,
                    HS*8,X, B),
    R = 
        case {R1, R2} of
            {0,0} -> secp256k1:jacob_zero();
            _ -> secp256k1:to_jacob({R1, R2})
        end,
            
    Y#stem{root = R}.
deserialize(?nwidth + 1, T,P,_,_,H, <<>>) -> 
    #stem{types = T, pointers = P, hashes = H};
deserialize(N, T0,P0,Path,HashDepth,H0,X) when N < (?nwidth + 1) ->
    <<T:2, P:Path, H:HashDepth, D/bitstring>> = X,
    T1 = setelement(N, T0, T),
    P1 = setelement(N, P0, P),
    H1 = setelement(N, H0, <<H:HashDepth>>),
    deserialize(N+1, T1, P1, Path, HashDepth,H1, D).
empty_hashes(CFG) ->
    HS = cfg:hash_size(CFG),
    %X = hash:hash_depth()*8,
    X = HS * 8,
    Y = many(<<0:X>>, ?nwidth),
    list_to_tuple(Y).

hash(S) ->
    P = S#stem.root,
    <<(secp256k1:hash_point(P)):256>>.

hash(S, CFG) when is_binary(S) ->
    hash(deserialize(S, CFG), CFG);
hash(S, CFG) when 
      is_tuple(S) and (size(S) == ?nwidth)->    
    hash2(1, S, <<>>, CFG);
hash(S, CFG) ->    
    H = S#stem.hashes,
    hash2(1, H, <<>>, CFG).
hash2(?nwidth + 1, _, X, CFG) -> 
    HS = cfg:hash_size(CFG),
    hash:doit(X, HS);
hash2(N, H, X, CFG) ->
    A = element(N, H),
    HS = cfg:hash_size(CFG),
    HS = size(A),
    hash2(N+1, H, <<A/binary, X/binary>>, CFG).
update(Location, Stem, CFG) ->
    dump:update(Location, serialize(Stem, CFG), ids:stem(CFG)).
put(Stem, CFG) ->
    dump:put(serialize(Stem, CFG), ids:stem(CFG)).
put_batch(Leaves, CFG) ->
    SL = serialize_stems(Leaves, CFG),
    dump:put_batch(SL, ids:stem(CFG)).
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
    
test() ->
    P = list_to_tuple(many(5, ?nwidth)),
    T = list_to_tuple(many(1, ?nwidth)),
    %P = {6,5,4,3,7,8,9,4,5,3,2,6,7,8,3,4},
    %T = {0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0},
    %CFG = cfg:new(1, 9, 2, trie), %path value id meta hash_size
    verkle_app:start(normal, []),
    CFG = trie:cfg(trie01),
%{cfg,5,2,trie01,2,32} path, value, id, meta, hash_size
%596 total, average 37.25
    H = empty_hashes(CFG),
    S = #stem{types = T, pointers = P, hashes = H},
    S2 = serialize(S, CFG),
    Sb = deserialize(S2, CFG),
    DB = ?p,
    %io:fwrite({size(?p)}),%9
    %io:fwrite({S#stem.root, Sb#stem.root}),
    true = secp256k1:jacob_equal(
             S#stem.root, Sb#stem.root, 
             DB#p.e),
    Hash = hash:doit(<<>>),
    Stem2 = add(S, 3, 1, 5, Hash, DB#p.g, DB#p.e),
    hash(Stem2),
    success.
    
