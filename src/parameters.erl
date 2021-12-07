-module(parameters).
-behaviour(gen_server).
-export([start_link/0,code_change/3,handle_call/3,handle_cast/2,handle_info/2,init/1,terminate/2]).
-export([read/0, div_e/1, div_e/0]).
-include("parameters256.hrl").

init(ok) -> 
    P = ?p,
    X = poly:all_div_e_parameters(P),
    {ok, {P, X}}.
start_link() -> gen_server:start_link({local, ?MODULE}, ?MODULE, ok, []).
code_change(_OldVsn, State, _Extra) -> {ok, State}.
terminate(_, _) -> io:format("died!"), ok.
handle_info(_, X) -> {noreply, X}.
handle_cast(_, X) -> {noreply, X}.
handle_call(div_e, _From, X = {_, D}) -> 
    {reply, D, X};
handle_call({div_e, M}, _From, X = {_, D}) -> 
    Y = element(M, D),
    {reply, Y, X};
handle_call(read, _From, X = {P, _}) -> 
    {reply, P, X};
handle_call(_, _From, X) -> {reply, X, X}.

read() ->
    gen_server:call(?MODULE, read).
div_e(M) ->
    gen_server:call(?MODULE, {div_e, M}).
div_e() ->
    gen_server:call(?MODULE, div_e).
