-module(sha256).
-export([doit/1]).

doit(B) ->
    true = is_binary(B),
    <<X:256, _/bitstring>> = crypto:hash(sha256, B),%crypto:hmac(sha256, S, ""),
    <<X:256>>.
    
