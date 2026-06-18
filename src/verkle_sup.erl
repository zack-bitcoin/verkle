-module(verkle_sup).
-behaviour(supervisor).
-export([start_link/2,init/1,stop/1]).
-define(CHILD(I, Type), {I, {I, start_link, []}, permanent, 5000, Type, [I]}).
-include("constants.hrl").
-define(ID, tree01).

start_link(Name, Location) -> 
    supervisor:start_link({global, Name}, ?MODULE, [Name, Location]).
stop(ID) -> 
    supervisor:terminate_child({global, ID}, ids_verkle:main(ID)),
    ok.

init([Name, Location]) ->
    A5 = ids_verkle:main(Name),
    A6 = ids_verkle:parameters(Name),                                    
    Children = [
		{A5, {file_bytes, start_link, [Name, Location]}, permanent, 5000, worker, [file_bytes]},
		{A6, {parameters, start_link, [Name]}, permanent, 5000, worker, [parameters]}
	       ],
    {ok, { {one_for_one, 5, 10}, Children} }.
