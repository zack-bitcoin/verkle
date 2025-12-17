-module(verkle_sup).
-behaviour(supervisor).
-export([start_link/0,init/1,stop/0]).
-define(CHILD(I, Type), {I, {I, start_link, []}, permanent, 5000, Type, [I]}).
-include("constants.hrl").
-define(ID, tree01).

start_link() -> 
    %[32, 32, amoveo, 0, 8, mode?, location]
    %keylength is the number of bytes to encode the path that you follow on the verkle.
    %ID = tree01,
    supervisor:start_link({global, ?ID}, ?MODULE, []).
stop() -> 
    ID = ?ID,
    supervisor:terminate_child({global, ID}, ids_verkle:main()),
    dump_sup:stop(ids_verkle:stem()),
    supervisor:terminate_child({global, ID}, ids_verkle:stem()),
    dump_sup:stop(ids_verkle:leaf()),
    supervisor:terminate_child({global, ID}, ids_verkle:leaf()),
    halt().

init([]) ->
    A5 = ids_verkle:main(),
    A6 = ids_verkle:parameters(),
    Children = [
		{verkle_db, {tree2, start_link, [["database"]]}, permanent, 5000, worker, [tree2]},
		{A6, {parameters, start_link, []}, permanent, 5000, worker, [parameters]}
	       ],
    {ok, { {one_for_one, 5, 10}, Children} }.
