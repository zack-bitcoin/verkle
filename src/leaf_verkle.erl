-module(leaf_verkle).
-export([new/3, new/2,
         key/1, value/1, meta/1, path/2, path_maker/1, hash/1, put/2, get/2, 
	 serialize/1, deserialize/1,
         raw_key/1,
	 test/1]).
-include("constants.hrl").

serialize(X) ->
    %M = cfg_verkle:meta(CFG),
    %S = cfg_verkle:value(CFG),
    K = size(X#leaf.key),
    V = size(X#leaf.value),
    M = size(X#leaf.meta),
    <<K:16, V:16, M:16, 
      (X#leaf.key)/binary,
      (X#leaf.value)/binary,
      (X#leaf.meta)/binary
    >>.
deserialize(A) ->
    <<K:16, V:16, M:16, KVM/binary>> = A,
    %<<Key:(8*K), Value:(8*V), Meta:(8*M)>> = KVM,
    <<Key:K/binary, Value:V/binary, Meta:M/binary>> = KVM,
    
    %L = cfg_verkle:value(CFG) * 8,
    %P = cfg_verkle:path(CFG) * 8,
    %MS = cfg_verkle:meta(CFG) * 8,
    %<<Key:P, 
    %  Value:L,
    %  Meta:MS
    %>> = A,
    #leaf{key = Key, value = Value, meta = Meta}. 
new(Key, Value) ->
    new(Key, Value, <<>>).
new(Key, Value, Meta) when is_integer(Key) ->
    new(<<Key:256>>, Value, Meta);
new(<<Key:256>>, Value, Meta) ->
    true = is_binary(Meta),
%    L = cfg_verkle:value(CFG) * 8,
%    M = cfg_verkle:meta(CFG) * 8,
%    Meta = if
%               Meta0 == 0 -> <<0:M>>;
%               is_binary(Meta0) -> Meta0
%           end,
%    true = is_binary(Meta),
    if
	(Value == empty) -> ok;
	is_binary(Value) -> ok
    end,
%	_ -> io:fwrite({leaf_value_failure, 
%                        size(Value), 
%                        L div 8})
%    case Meta of
%        <<_:M>> -> ok;
%        _ -> io:fwrite({leaf_meta_failure, 
%                        size(Meta), M div 8})
%    end,
    #leaf{key = <<Key:256>>, value = Value, meta = Meta}. 
key(#leaf{key = <<K:256>>}) -> K.
raw_key(#leaf{key = K}) -> K;
raw_key({I, 0}) when is_integer(I) -> <<I:256>>;
raw_key({<<B:256>>, 0}) -> <<B:256>>.
path(L = #leaf{}, _CFG) ->
    K = key(L),
    path_maker(K);
path({K, 0}, _) ->
    path_maker(K).
path_maker(K) ->
    %T = cfg_verkle:path(CFG)*8,%bytes to store path
    %lists:reverse([<<N:?nindex>>||<<N:?nindex>> <= <<K:T>>]).
    lists:reverse([<<N:?nindex>>||<<N:?nindex>> <= <<K:256>>]).
value(#leaf{value = V}) -> V.
meta(X) -> X#leaf.meta.
%serialize_leaves([], _) -> [];
%serialize_leaves([{N, L}| T], CFG) ->
%    [{N, serialize(L)}|serialize_leaves(T, CFG)].
put(Leaf, ID) ->
    tree2:store(serialize(Leaf), ID).
get(Pointer, ID) ->
    {ok, L} = tree2:read(Pointer, ID),
    deserialize(L).
hash(L) ->   
    %HS = cfg_verkle:hash_size(CFG)*8,
    V = L#leaf.value,
    case V of
	empty -> <<0:256>>;
	<<_:256>> ->
            sha256:doit(<<(L#leaf.key)/binary, V/binary>>);
	_ ->
	    %1=2,
	    %P = cfg_verkle:path(CFG) * 8,
	    V2 = sha256:doit(V),
            sha256:doit(<<(L#leaf.key)/binary, V2/binary>>)
    end.
test(1) ->
%    CFG = tree:cfg(tree01),
    X = new(1, <<0:16>>, <<0:16>>),
    SX = serialize(X),
    X = deserialize(serialize(X)),
    hash(X),
    success.

