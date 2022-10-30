-module(hash_unused).
-export([doit/1, list_of_ints/1]).

doit(X) when is_binary(X) ->
    crypto:hash(sha256, X).

list_of_ints(L) ->
    list_of_ints2(doit(<<(hd(L)):256>>), tl(L)).

list_of_ints2(H, []) -> H;

list_of_ints2(Hash, [H|T]) -> 
    B = <<H:256>>,
    Hash2 = doit(<<B/binary, Hash/binary>>),
    list_of_ints2(Hash2, T).
