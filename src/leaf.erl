-module(leaf).
-export([new/4, key/1, value/1, meta/1, path/2, path_maker/2, hash/2, put/2, get/2, serialize/2, deserialize/2,
	 put_batch/2,
         leaf2fast/4, fast2leaf/1,
	is_serialized_leaf/2, test/0]).
-include("constants.hrl").
%-export_type([leaf/0,key/0,value/0,meta/0,leaf_p/0,path/0]).

fast2leaf(#fast_leaf{key = K, value = V, meta = M}
         ) ->
    #leaf{key = K, value = V, meta = M}.

leaf2fast(L = #leaf{key = K, value = V, meta = M},
          P, H, CFG) ->
    P2 = if
             (P == 0) ->
                 path_maker(K, CFG);
             true -> P
         end,
    H2 = if
             (H == 0) ->
                 <<X:256>> = hash(L, CFG),
                 fr:encode(X);
             true -> H
         end,
    #fast_leaf{
                key = K,
                value = V,
                meta = M,
                path = P2,
                hash = H2
              }.
        


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
    <<(X#leaf.key):P, 
      (X#leaf.meta):M,
      (X#leaf.value)/binary>>.
deserialize(A, CFG) ->
    L = cfg:value(CFG) * 8,
    P = cfg:path(CFG) * 8,
    MS = cfg:meta(CFG) * 8,
    <<Key:P, 
      Meta:MS,
      Value:L>> = A,
    #leaf{key = Key, value = <<Value:L>>, meta = Meta}. 
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
    #leaf{key = Key, value = Value, meta = Meta}. 
check_key(Key, LBytes) when is_integer(Key),
			    Key >= 0,
			    Key < (1 bsl (LBytes * 8)) ->
    ok;
check_key(Key, _) when is_integer(Key) ->
    {error, key_out_of_range};
check_key(_, _) ->
    {error, key_not_integer}.
key(L) -> L#leaf.key.
path(L = #fast_leaf{path = P}, CFG) ->
    P;
path(L = #leaf{}, CFG) ->
    K = key(L),
    path_maker(K, CFG);
path({K, 0, P}, _CFG) ->
    1=2,
    P;
path({K, 0}, CFG) ->
    %this means an empty leaf.
    1=2,
    path_maker(K, CFG).
path_maker(K, CFG) ->
    T = cfg:path(CFG)*8,
    lists:reverse([<<N:?nindex>>||<<N:?nindex>> <= <<K:T>>]).

value(L) -> L#leaf.value.
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
%hash(L = #fast_leaf{hash = H}, _CFG) ->   
%    H;
hash(L, CFG) ->   
    HS = cfg:hash_size(CFG)*8,
    case L#leaf.value of
	empty -> <<0:HS>>;
	V ->
	    P = cfg:path(CFG) * 8,
	    %HS2 = cfg:hash_size(CFG),
	    %Data = <<(L#leaf.key):P, V/binary>>,
            %io:fwrite("\n"),
            %io:fwrite(integer_to_list(size(Data))),
            hash:doit(<<(L#leaf.key):P, V/binary>>)
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
    
