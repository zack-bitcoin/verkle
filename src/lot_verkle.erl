-module(lot_verkle).
-export([new/1, new/2,
	 value/1, meta/1, 
	 hash/1, put/2, get/2, 
	 serialize/1, deserialize/1,
	 test/1]).
-include("constants.hrl").

serialize(X) ->
    V = size(X#lot.value),
    M = size(X#lot.meta),
    <<V:16, M:16, 
      (X#lot.value)/binary,
      (X#lot.meta)/binary
    >>.
deserialize(A) ->
    <<V:16, M:16, KVM/binary>> = A,
    <<Value:V/binary, Meta:M/binary>> = KVM,
    true = is_binary(Meta),
    #lot{value = Value, meta = Meta}. 
new(Value) ->
    new(Value, <<>>).
new(Value, Meta) ->
    true = is_binary(Meta),
    if
	(Value == empty) -> ok;
	is_binary(Value) -> ok
    end,
    #lot{value = Value, meta = Meta}. 
value(#lot{value = V}) -> V.
meta(X) -> X#lot.meta.
put(Leaf, ID) ->
    file_bytes:store(serialize(Leaf), ID).
get(Pointer, ID) ->
    {ok, L} = file_bytes:read(Pointer, ID),
    deserialize(L).
hash(L) ->   
    V = L#lot.value,
    S = size(V),
    if
	(S < 33) -> V;
	true -> sha256:doit(V)
    end.
test(1) ->
%    CFG = tree:cfg(tree01),
    X = new(1, <<0:16>>),
    SX = serialize(X),
    X = deserialize(serialize(X)),
    hash(X),
    success.

