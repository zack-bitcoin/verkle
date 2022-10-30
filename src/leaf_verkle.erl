-module(leaf_verkle).
-export([new/4,
         key/1, value/1, meta/1, path/2, path_maker/2, hash/2, put/2, get/2, serialize/2, deserialize/2,
         raw_key/1,
	 put_batch/2,
	is_serialized_leaf/2, test/1]).
-include("constants.hrl").
%-export_type([leaf/0,key/0,value/0,meta/0,leaf_p/0,path/0]).



is_serialized_leaf(X, CFG) ->
    P = cfg_verkle:path(CFG),
    M = cfg_verkle:meta(CFG),
    S = cfg_verkle:value(CFG),
    size(X) == (P + M + S).
    %is_record(X, leaf).
serialize(X, CFG) ->
    P = cfg_verkle:path(CFG) * 8,
    M = cfg_verkle:meta(CFG) * 8,
    S = cfg_verkle:value(CFG),
    S = size(X#leaf.value),
    M = size(X#leaf.meta),
    %io:fwrite({CFG, X}),
    %<<(X#leaf.key):P, 
    <<(X#leaf.key)/binary,
      %(X#leaf.meta):M,
      (X#leaf.value)/binary,
      (X#leaf.meta)/binary
    >>.
deserialize(A, CFG) ->
    L = cfg_verkle:value(CFG) * 8,
    P = cfg_verkle:path(CFG) * 8,
    MS = cfg_verkle:meta(CFG) * 8,
    <<Key:P, 
      Value:L,
      Meta:MS
    >> = A,
    %#leaf{key = Key, value = <<Value:L>>, meta = Meta}. 
    #leaf{key = <<Key:P>>, value = <<Value:L>>, meta = <<Meta:MS>>}. 
new(Key, Value, Meta, CFG) when is_integer(Key) ->
    new(<<Key:256>>, Value, Meta, CFG);
new(<<Key:256>>, Value, Meta0, CFG) ->
    P = cfg_verkle:path(CFG),
    L = cfg_verkle:value(CFG) * 8,
    M = cfg_verkle:meta(CFG) * 8,
    Meta = if
               Meta0 == 0 -> <<0:M>>;
               is_binary(Meta0) -> Meta0
           end,
    true = is_binary(Meta),
    case Value of
	empty -> ok;
	<<_:L>> -> ok;
	_ -> io:fwrite({leaf_value_failure, 
                        size(Value), 
                        L div 8})
    end,
    case Meta of
        <<_:M>> -> ok;
        _ -> io:fwrite({leaf_meta_failure, 
                        size(Meta), M div 8})
    end,
    #leaf{key = <<Key:256>>, value = Value, meta = Meta}. 
key(#leaf{key = <<K:256>>}) -> K.
raw_key(#leaf{key = K}) -> K;
raw_key({I, 0}) when is_integer(I) -> <<I:256>>;
raw_key({<<B:256>>, 0}) -> <<B:256>>.
path(L = #leaf{}, CFG) ->
    K = key(L),
    path_maker(K, CFG);
path({K, 0}, CFG) ->
    path_maker(K, CFG).
path_maker(K, CFG) ->
    T = cfg_verkle:path(CFG)*8,
    lists:reverse([<<N:?nindex>>||<<N:?nindex>> <= <<K:T>>]).

value(#leaf{value = V}) -> V.
meta(X) -> X#leaf.meta.
put_batch(Leaves, CFG) ->
    SL = serialize_leaves(Leaves, CFG),
    dump:put_batch(SL, ids_verkle:leaf(CFG)).
serialize_leaves([], _) -> [];
serialize_leaves([{N, L}| T], CFG) ->
    [{N, serialize(L, CFG)}|serialize_leaves(T, CFG)].

put(Leaf, CFG) ->
    dump:put(serialize(Leaf, CFG), 
	     ids_verkle:leaf(CFG)).
get(Pointer, CFG) ->
    L = dump:get(Pointer, ids_verkle:leaf(CFG)),
    deserialize(L, CFG).
hash(L, CFG) ->   
    HS = cfg_verkle:hash_size(CFG)*8,
    case L#leaf.value of
	empty -> <<0:HS>>;
	V ->
	    P = cfg_verkle:path(CFG) * 8,
            %hash:doit(<<(L#leaf.key):P, V/binary>>)
            hash:doit(<<(L#leaf.key)/binary, V/binary>>)
    end.
test(1) ->
    verkle_app:start(normal, []),
    CFG = tree:cfg(trie01),
%{cfg,32,2,trie01,2,32,ram,1},[]],
    %io:fwrite(CFG),
    X = new(1, <<0:16>>, 0, CFG),
    SX = serialize(X, CFG),
    %io:fwrite(integer_to_list(size(SX))),%26
    X = deserialize(serialize(X, CFG), CFG),
    true = is_serialized_leaf(SX, CFG),
    hash(X, CFG),
    success.
    
