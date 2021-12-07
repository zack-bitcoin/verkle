-module(parameters).
-behaviour(gen_server).
-export([start_link/0,code_change/3,handle_call/3,handle_cast/2,handle_info/2,init/1,terminate/2]).
-export([read/0]).
-include("parameters256.hrl").

init(ok) -> {ok, ?p}.
start_link() -> gen_server:start_link({local, ?MODULE}, ?MODULE, ok, []).
code_change(_OldVsn, State, _Extra) -> {ok, State}.
terminate(_, _) -> io:format("died!"), ok.
handle_info(_, X) -> {noreply, X}.
handle_cast(_, X) -> {noreply, X}.
handle_call(read, _From, X) -> {reply, X, X};
handle_call(_, _From, X) -> {reply, X, X}.

read() ->
    gen_server:call(?MODULE, read).
