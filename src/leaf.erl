-module(leaf).
-export([new/4, key/1, value/1, meta/1, path/2, path_maker/2, hash/2, put/2, get/2, serialize/2, deserialize/2,
	 put_batch/2,
	is_serialized_leaf/2, test/0]).
-include("constants.hrl").
%-export_type([leaf/0,key/0,value/0,meta/0,leaf_p/0,path/0]).



is_serialized_leaf(X, CFG) ->
    P = cfg:path(CFG),
    M = cfg:meta(CFG),
    S = cfg:value(CFG),
    size(X) == (P + M + S).
    %is_record(X, leaf).
serialize(X, CFG) ->
    P = cfg:path(CFG) * 8,
    M = cfg:meta(CFG) * 8,
    S = cfg:value(CFG),
    S = size(X#leaf.value),
    %io:fwrite({CFG, X}),
    %<<(X#leaf.key):P, 
    <<(X#leaf.key)/binary,
      (X#leaf.meta):M,
      (X#leaf.value)/binary>>.
deserialize(A, CFG) ->
    L = cfg:value(CFG) * 8,
    P = cfg:path(CFG) * 8,
    MS = cfg:meta(CFG) * 8,
    <<Key:P, 
      Meta:MS,
      Value:L>> = A,
    %#leaf{key = Key, value = <<Value:L>>, meta = Meta}. 
    #leaf{key = <<Key:P>>, value = <<Value:L>>, meta = Meta}. 
new(Key, Value, Meta, CFG) ->
    P = cfg:path(CFG),
    ok = check_key(Key, P),
    L = cfg:value(CFG) * 8,
    case Value of
	empty -> ok;
	<<_:L>> -> ok;
	_ -> io:fwrite({value_is, size(Value), 
                        L div 8})
    end,
    %L = cfg:value(CFG) * 8,
    %<<_:L>> = Value,
    %#leaf{key = Key, value = Value, meta = Meta}. 
    #leaf{key = <<Key:256>>, value = Value, meta = Meta}. 
check_key(Key, LBytes) when is_integer(Key),
			    Key >= 0,
			    Key < (1 bsl (LBytes * 8)) ->
    ok;
check_key(Key, _) when is_integer(Key) ->
    {error, key_out_of_range};
check_key(_, _) ->
    {error, key_not_integer}.
key(#leaf{key = <<K:256>>}) -> K.
path(L = #leaf{}, CFG) ->
    K = key(L),
    path_maker(K, CFG);
path({K, 0}, CFG) ->
    path_maker(K, CFG).
path_maker(K, CFG) ->
    T = cfg:path(CFG)*8,
    lists:reverse([<<N:?nindex>>||<<N:?nindex>> <= <<K:T>>]).

value(#leaf{value = V}) -> V.
meta(X) -> X#leaf.meta.
put_batch(Leaves, CFG) ->
    SL = serialize_leaves(Leaves, CFG),
    dump:put_batch(SL, ids:leaf(CFG)).
serialize_leaves([], _) -> [];
serialize_leaves([{N, L}| T], CFG) ->
    [{N, serialize(L, CFG)}|serialize_leaves(T, CFG)].

put(Leaf, CFG) ->
    dump:put(serialize(Leaf, CFG), 
	     ids:leaf(CFG)).
get(Pointer, CFG) ->
    L = dump:get(Pointer, ids:leaf(CFG)),
    deserialize(L, CFG).
hash(L, CFG) ->   
    HS = cfg:hash_size(CFG)*8,
    case L#leaf.value of
	empty -> <<0:HS>>;
	V ->
	    P = cfg:path(CFG) * 8,
            %hash:doit(<<(L#leaf.key):P, V/binary>>)
            hash:doit(<<(L#leaf.key)/binary, V/binary>>)
    end.
test() ->
    verkle_app:start(normal, []),
    CFG = trie:cfg(trie01),
%{cfg,32,2,trie01,2,32,ram,1},[]],
    %io:fwrite(CFG),
    X = new(1, <<0:16>>, 0, CFG),
    SX = serialize(X, CFG),
    %io:fwrite(integer_to_list(size(SX))),%26
    X = deserialize(serialize(X, CFG), CFG),
    true = is_serialized_leaf(SX, CFG),
    hash(X, CFG),
    success.
    
