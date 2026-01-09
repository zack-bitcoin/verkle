-module(verkle_app).

-behaviour(application).

-include("constants.hrl").
%% Application callbacks
-export([start/2, stop/1]).

start(normal, []) ->
    verkle_sup:start_link(tree01, ".").

stop(_State) ->
    ok.
