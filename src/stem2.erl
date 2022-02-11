%The purpose of this file is to define stems as a data structure in ram, and give some simple functions to operate on them.

-module(stem2).
-export([test/1,get/2,put/2,type/2,
         hash/1,hash_point/1,
         pointers/1,
	 types/1,hashes/1,pointer/2,new/5,add/5,
	 new_empty/1,recover/6, empty_hashes/1, 
	 update_pointers/2, empty_tuple/0,
	 make/3, make/2, update/3, onify2/2,
	 put_batch/2, serialize/2,
         root/1,
	 empty_trie/2]).
%-include("constants.hrl").
%-export_type([stem/0,types/0,empty_t/0,stem_t/0,leaf_t/0,pointers/0,empty_p/0,hashes/0,hash/0,empty_hash/0,stem_p/0,nibble/0]).
-record(stem, { root = fq:e_zero()
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
add(S, N, T, P, <<H:256>>) ->
    %Gs are the generator points for the pedersen commits.
    1=2,
    #stem{
     types = Ty,
     pointers = Po,
     hashes = Ha,
     root = Root
    } = S,
    {Gs, _, _} = parameters2:read(),
    M = N+1,
    <<Old:256>> = element(M, Ha),
    %for generator M, subtract Old and add H.
    G = lists:nth(M, Gs),
    %Diff = secp256k1:jacob_mul(G, H-Old, E),
    %Diff = fq:e_mul2(G, fr:encode(H-Old)),
    Diff = fq:e_mul2(
             G, fr:encode(fr:add(H, fr:neg(Old)))),
    %TODO maybe H and old are fr points???
    %Root2 = fq:e_add(Root, fq:extended2extended_niels(Diff)),
    Root2 = fq:e_add(Root, Diff),
    T2 = setelement(M, Ty, T),
    P2 = setelement(M, Po, P),
    H2 = setelement(M, Ha, <<H:256>>),
    #stem{types = T2, pointers = P2, 
          hashes = H2, root = Root2}.
new_empty(CFG) -> 
    #stem{hashes = empty_hashes(CFG),
         types = empty_tuple(),
         pointers = empty_tuple(),
         root = fq:e_zero()}.
recover(M, T, P, H, Hashes, CFG) ->
    Types = onify2(Hashes, CFG),
    %Types = list_to_tuple(onify(tuple_to_list(Hashes), CFG)),
    S = #stem{hashes = Hashes, types = Types},
    add(S, M, T, P, H).
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
new(N, T, P, H, CFG) ->
    %N is the nibble being pointed to.
    %T is the type, P is the pointer, H is the Hash
    S = new_empty(CFG),
    add(S, N, T, P, H).
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
    <<R1:512>> = fq:extended2affine(Root),% 2%
    %<<R1:(256*5)>> = Root,
    %X = serialize(P, H, T, 1),
    X = serialize2(tuple_to_list(P), 
                   tuple_to_list(H), 
                   tuple_to_list(T), 
                   []),
    <<R1:512, X/binary>>.
    %<<R1:(256*5), X/binary>>.
%serialize(_, _, _, N) when N>?nwidth -> <<>>;
%serialize(P, H, T, N) -> 
%    P1 = element(N, P),
%    H1 = element(N, H),
%    T1 = element(N, T),
%    D = serialize(P, H, T, N+1),
%    << T1, P1:256, H1/binary, %3.5%
%       D/binary >>. % 60%

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
    R = fq:affine2extended(<<R1:512>>),
    %R = <<R1:(256*5)>>,
            
    Y#stem{root = R}.
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
    P = S#stem.root,
    hash_point(P).
hash_point(P) ->
    fq:hash_point(P).

update(Location, Stem, CFG) ->
    dump:update(Location, serialize(Stem, CFG), ids:stem(CFG)).
put(Stem, CFG) ->
    S = serialize(Stem, CFG),
    ID = ids:stem(CFG),
    dump:put(S, ID).
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

equal(S, T) ->
    [R2, R3] = fq:e_simplify_batch(
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
    verkle_app:start(normal, []),
    CFG = trie:cfg(trie01),
%{cfg,5,2,trie01,2,32} path, value, id, meta, hash_size
%596 total, average 37.25
    H = empty_hashes(CFG),
    S = #stem{types = T, pointers = P, hashes = H},
    S2 = serialize(S, CFG),
    Sb = deserialize(S2, CFG),
    %io:fwrite({size(?p)}),%9
    %io:fwrite({S#stem.root, Sb#stem.root}),
    true = equal(S, Sb),
    true = fq:eq(S#stem.root, Sb#stem.root),
    Hash = hash:doit(<<>>),
    Stem2 = add(S, 3, 1, 5, Hash),
    hash(Stem2),
    %testing reading and writing to the hard drive.
    Pointer = stem2:put(Stem2, CFG),
    Stem2b = get(Pointer, CFG),
    true = equal(Stem2b, Stem2),
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
     timer:now_diff(T3, T2)}.

    

    
