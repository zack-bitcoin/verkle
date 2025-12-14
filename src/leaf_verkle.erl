-module(leaf_verkle).
-export([new/4,
         key/1, value/1, meta/1, path/2, path_maker/2, hash/2, put/2, get/2, serialize/2, deserialize/2,
         raw_key/1,
	is_serialized_leaf/2, test/1]).
-include("constants.hrl").

is_serialized_leaf(X, CFG) ->
    P = cfg_verkle:path(CFG),
    M = cfg_verkle:meta(CFG),
    S = cfg_verkle:value(CFG),
    size(X) == (P + M + S).
serialize(X, CFG) ->
    M = cfg_verkle:meta(CFG),
    S = cfg_verkle:value(CFG),
    S = size(X#leaf.value),
    M = size(X#leaf.meta),
    <<(X#leaf.key)/binary,
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
serialize_leaves([], _) -> [];
serialize_leaves([{N, L}| T], CFG) ->
    [{N, serialize(L, CFG)}|serialize_leaves(T, CFG)].
put(Leaf, CFG) ->
    tree2:store(serialize(Leaf, CFG)).
get(Pointer, CFG) ->
    {ok, L} = tree2:read(Pointer),
    deserialize(L, CFG).
hash(L, CFG) ->   
    HS = cfg_verkle:hash_size(CFG)*8,
    case L#leaf.value of
	empty -> <<0:HS>>;
	V ->
	    P = cfg_verkle:path(CFG) * 8,
            sha256:doit(<<(L#leaf.key)/binary, V/binary>>)
    end.
test(1) ->
    CFG = tree:cfg(tree01),
    X = new(1, <<0:16>>, 0, CFG),
    SX = serialize(X, CFG),
    X = deserialize(serialize(X, CFG), CFG),
    true = is_serialized_leaf(SX, CFG),
    hash(X, CFG),
    success.

