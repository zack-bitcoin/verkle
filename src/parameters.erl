-module(parameters).
-behaviour(gen_server).
-export([start_link/0,code_change/3,handle_call/3,handle_cast/2,handle_info/2,init/1,terminate/2]).
-export([read/0, div_e/1, div_e/0,
         multi_exp/0, multi_exp/1, multi_exp/2]).
-include("parameters256.hrl").

init(ok) -> 
    P = ?p,
    X = poly:all_div_e_parameters(P),
    S = store:multi_exponent_parameters(8),
    {ok, {P, X, S}}.
start_link() -> gen_server:start_link({local, ?MODULE}, ?MODULE, ok, []).
code_change(_OldVsn, State, _Extra) -> {ok, State}.
terminate(_, _) -> io:format("died!"), ok.
handle_info(_, X) -> {noreply, X}.
handle_cast(_, X) -> {noreply, X}.
handle_call(multi_exp, _From, X = {_, _, S}) -> 
    {reply, S, X};
handle_call({multi_exp, M}, _From, 
            X = {_, _, S}) -> 
    Y = element(M, S),
    {reply, Y, X};
handle_call({multi_exp, M, N}, _From, 
            X = {_, _, S}) -> 
    Y = element(M, S),
    Z = element(N, Y),
    {reply, Z, X};
handle_call(div_e, _From, X = {_, D, _}) -> 
    {reply, D, X};
handle_call({div_e, M}, _From, X = {_, D, _}) -> 
    Y = element(M, D),
    {reply, Y, X};
handle_call(read, _From, X = {P, _, _}) -> 
    {reply, P, X};
handle_call(_, _From, X) -> {reply, X, X}.

read() ->
    gen_server:call(?MODULE, read).
div_e(M) ->
    gen_server:call(?MODULE, {div_e, M}).
div_e() ->
    gen_server:call(?MODULE, div_e).
multi_exp() ->
    gen_server:call(?MODULE, multi_exp).
multi_exp(G) ->
    gen_server:call(?MODULE, {multi_exp, G}).
multi_exp(G, R) ->
    gen_server:call(?MODULE, {multi_exp, G, R}).
