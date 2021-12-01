-module(verkle_app).

-behaviour(application).

-include("constants.hrl").
%% Application callbacks
-export([start/2, stop/1]).

%start(_StartType, _StartArgs) ->
start(normal, []) ->
    Size = 2,
    %Max = 20000000000,
    ID = trie01,
    %KeyLength = 5,%in bytes
    KeyLength = ?nwidth div ?nindex,%in bytes
    Amount = 1000000,
    Mode = ram,
    %Mode = hd,
    Meta = 2,
    HashSize = 32,
    verkle_sup:start_link(KeyLength, Size, ID, Amount, Meta, HashSize, Mode, "").

stop(_State) ->
    ok.
