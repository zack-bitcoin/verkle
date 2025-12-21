%The purpose of this file is to define stems as a data structure in ram, and give some simple functions to operate on them.

-module(stem_verkle).
-export([test/1,get/2,put/2,put/3,type/2,
         hash/1,hash_point/1,hash_points/1,
         pointers/1,
	 types/1,hashes/1,pointer/2,%new/5,%add/5,
	 new_empty/0,%recover/6, 
         empty_hashes/0, 
	 update_pointers/2, empty_tuple/0,
	 make/3, make/2, 
         %update/3, 
         onify2/1,
%	 put_batch/2, 
         serialize/2,
	 serialize/1,
         root/1, check_root_integrity/1,
%         delete/2,
	 empty_trie/1]).
%-include("constants.hrl").
%-export_type([stem/0,types/0,empty_t/0,stem_t/0,leaf_t/0,pointers/0,empty_p/0,hashes/0,hash/0,empty_hash/0,stem_p/0,nibble/0]).
-define(ID, tree01).
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
empty_tuple(Y) -> 
    X = many(Y, ?nwidth),
    list_to_tuple(X).
many(_, 0) -> [];
many(X, N) when (N > 0) -> 
    [X|many(X, N-1)].
new_empty() -> 
    #stem{hashes = empty_hashes(),
         types = empty_tuple(),
         pointers = empty_tuple(0),
         root = ed:extended_zero()}.
%unused_recover(M, T, P, H, Hashes, CFG) ->
%    Types = onify2(Hashes),
    %Types = list_to_tuple(onify(tuple_to_list(Hashes))),
%    S = #stem{hashes = Hashes, types = Types},
%    unused_add(S, M, T, P, H).
onify2(H) ->
    list_to_tuple(onify(tuple_to_list(H))).
onify([]) -> [];
onify([H|T]) ->
    %HS = cfg_verkle:hash_size(CFG)*8,
    <<X:256>> = H,
    case X of
	0 -> [0|onify(T)];
	_ -> [1|onify(T)]
    end.
	    
%onify([<<0:_>>|T]) -> [0|onify(T)];
%onify([_|T]) -> [1|onify(T)].
make(Hashes, ID) ->
    Types = onify2(Hashes),
    %Pointers = empty_tuple({0,0}),
    Pointers = empty_tuple(),
    make(Types, Pointers, Hashes).
make(Types, Pointers, Hashes) ->
    #stem{types = Types,
	  pointers = Pointers,
	  hashes = Hashes}.
%unused_new(N, T, P, H, CFG) ->
    %N is the nibble being pointed to.
    %T is the type, P is the pointer, H is the Hash
%    S = new_empty(),
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
serialize(S, CompressedRoot) ->
    if
        ?sanity ->
            check_root_integrity(S);
        true -> ok
    end,
    #stem{
           pointers = P,
           hashes = H,
           types = T,
           root = _Root
         } = S,
    <<R1:512>> = CompressedRoot,
    X = serialize2(tuple_to_list(P), 
                   tuple_to_list(H), 
                   tuple_to_list(T), 
                   []),
    <<R1:512, X/binary>>.
serialize(S) ->
    if
        ?sanity ->
            %check_root_integrity(S);
            ok;
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
    Result = <<R1:512, X/binary>>,
    Result.

serialize2([], [], [], R) -> 
    erlang:iolist_to_binary(
      lists:reverse(R));
serialize2([P|PT], [H|HT], [T|TT], R) -> 
    %10 billion people
    %each one wants to have 10 ongoing relationships with the chain
    if
	 not(is_integer(P)) -> io:fwrite({P});
	true -> ok
    end,
    true = is_integer(P),
    N = <<T, P:48, H/binary>>,
    serialize2(PT, HT, TT, [N|R]).

deserialize(<<R1:512, B/binary>>) -> 
    case ed:is_on_curve(<<R1:512>>) of
        true -> ok;
        false -> 
            io:fwrite("invalid elliptic curve point. Maybe you are reading outside of the data that has been written to.\n"),
            erlang:error(invalid_elliptic_curve_point)
    end,
    Y = deserialize2([],[],[], B),
    R = ed:affine2extended(<<R1:512>>),
    Result = Y#stem{root = R},
    if
        ?sanity ->
            check_root_integrity(Result);
        true -> ok
    end,
    Result.
deserialize2(T, P, H, <<>>) ->
    #stem{types = list_to_tuple(
                    lists:reverse(T)),
          pointers = list_to_tuple(
                       lists:reverse(P)),
          hashes = list_to_tuple(
                     lists:reverse(H))};
deserialize2(TT, PT, HT, 
             <<T, P:48, H:256, R/binary>>) ->
    deserialize2([T|TT], [P|PT], [<<H:256>>|HT], R);
deserialize2(_, _, _, B) ->
    io:fwrite("deserialize 2 failure\n"),
    io:fwrite(size(B)),
    1=2.

empty_hashes() ->
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
    [<<X:256>>] = ed:compress_points([P2]),
    fr:encode(X).
hash_points(L) ->
    L2 = lists:map(fun(X) ->
                           ed:e_mul(X, <<8:256/little>>)
                   end, L),
    L3 = ed:compress_points(L2),
    lists:map(fun(<<X:256>>) -> fr:encode(X) end,
              L3).

check_root_integrity(Stem) ->
    MEP = parameters:multi_exp(),
    Hashes = tuple_to_list(Stem#stem.hashes),
    R = precomputed_multi_exponent:doit(
          Hashes,MEP),
    {Gs, _Hs, _Q} = parameters:read(),
    %R2 = multi_exponent:doit(Hashes, Gs),
    %B1 = ed:e_eq(R, R2),
    B2 = ed:e_eq(R, Stem#stem.root),
    %B3 = ed:e_eq(R2, Stem#stem.root),
    if
        %not(B1 and B2 and B3) ->
        not(B2) ->
            %io:fwrite({B1, B2, B3, Stem}),
            erlang:error(root_lacks_integrity);
        true -> ok
    end.
put(Stem, ID, CompressedRoot) ->
    %compressed root is in affine format. 64 bytes.
    S = serialize(Stem, CompressedRoot),
    tree2:store(S, ID).
put(Stem, ID) ->
    S = serialize(Stem),
    tree2:store(S, ID).
get(Pointer, ID) -> 
    true = is_integer(Pointer),
    {ok, S} = tree2:read(Pointer, ID),
    deserialize(S).
empty_trie(Root) ->
    Stem = stem_verkle:get(Root),
    %update_pointers(Stem, empty_tuple({0,0})).
    update_pointers(Stem, empty_tuple()).
equal(S, T) ->
    [R2, R3] = ed:normalize(
                 [S#stem.root, T#stem.root]),
    S2 = S#stem{
           root = R2
          },
    T2 = T#stem{
           root = R3
          },
    ((R2 == R3) and (S#stem.hashes == T#stem.hashes)).
range(N, N) -> [N];
range(A, B) when A < B -> 
    [A|range(A+1, B)].
test(1) ->
    P = list_to_tuple(many(5, ?nwidth)),
    T = list_to_tuple(many(1, ?nwidth)),
    io:fwrite("before start\n"),
%596 total, average 37.25
    H = empty_hashes(),
    S = #stem{types = T, pointers = P, hashes = H},
    S2 = serialize(S),
    Sb = deserialize(S2),
    %io:fwrite({size(?p)}),%9
    <<A:(8*128)>> = S#stem.root,
    <<B:(8*128)>> = Sb#stem.root,
    %io:fwrite({S#stem.root, Sb#stem.root}),
    true = equal(S, Sb),
    %true = fq:eq(S#stem.root, Sb#stem.root),
    io:fwrite("before equal\n"),
    true = ed:e_eq(S#stem.root, Sb#stem.root),
    _Hash = sha256:doit(<<>>),
    %Stem = unused_add(S, 3, 1, 5, Hash),
    %hash(Stem),
    %testing reading and writing to the hard drive.
    Pointer = stem_verkle:put(S, ?ID),
    Stem2b = stem_verkle:get(Pointer, ?ID),
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
