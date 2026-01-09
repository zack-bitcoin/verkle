-module(verkle_sup).
-behaviour(supervisor).
-export([start_link/2,init/1,stop/1]).
-define(CHILD(I, Type), {I, {I, start_link, []}, permanent, 5000, Type, [I]}).
-include("constants.hrl").
-define(ID, tree01).

start_link(Name, Location) -> 
    %[32, 32, amoveo, 0, 8, mode?, location]
    %keylength is the number of bytes to encode the path that you follow on the verkle.
    %ID = tree01,
    supervisor:start_link({global, Name}, ?MODULE, [Name, Location]).
stop(ID) -> 
    supervisor:terminate_child({global, ID}, ids_verkle:main(ID)),
    %dump_sup:stop(ids_verkle:stem(ID)),
    %supervisor:terminate_child({global, ID}, ids_verkle:stem(ID)),
    %dump_sup:stop(ids_verkle:leaf()),
    %supervisor:terminate_child({global, ID}, ids_verkle:leaf(ID)),
    ok.

init([Name, Location]) ->
    A5 = ids_verkle:main(Name),
    %io:fwrite("starting " ++ A5 ++ "\n"),    %tree01_verkle_main,"\n"],
    A6 = ids_verkle:parameters(Name),                                    
    %io:fwrite("starting " ++ atom_to_list(A6) ++ "\n"),
    %failed with [{global,tree01_v_parameters},ghq]}}
    Children = [
		{A5, {tree2, start_link, [Name, Location]}, permanent, 5000, worker, [tree2]},
		{A6, {parameters, start_link, [Name]}, permanent, 5000, worker, [parameters]}
	       ],
    {ok, { {one_for_one, 5, 10}, Children} }.
