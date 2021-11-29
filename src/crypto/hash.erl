-module(hash).
-export([doit/1]).

doit(X) when is_binary(X) ->
    crypto:hash(sha256, X).
