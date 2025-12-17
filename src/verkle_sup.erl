-module(verkle_sup).
-behaviour(supervisor).
-export([start_link/5,init/1,stop/1]).
-define(CHILD(I, Type), {I, {I, start_link, []}, permanent, 5000, Type, [I]}).
-include("constants.hrl").
start_link(KeyLength, Size, ID, Meta, Location) -> 
    %[32, 32, amoveo, 0, 8, mode?, location]
    %keylength is the number of bytes to encode the path that you follow on the verkle.
    HashSize = 32,
    CFG = cfg_verkle:new(KeyLength, Size, ID, 
                  Meta, HashSize, hd),
    supervisor:start_link({global, cfg_verkle:id(CFG)}, ?MODULE, [CFG, Location]).
stop(ID) -> 
    CFG = tree:cfg(ID),
    supervisor:terminate_child({global, ID}, ids_verkle:main(CFG)),
    dump_sup:stop(ids_verkle:stem(CFG)),
    supervisor:terminate_child({global, ID}, ids_verkle:stem(CFG)),
    dump_sup:stop(ids_verkle:leaf(CFG)),
    supervisor:terminate_child({global, ID}, ids_verkle:leaf(CFG)),
    halt().

init([CFG, Location]) ->
    A5 = ids_verkle:main(CFG),
    A6 = ids_verkle:parameters(CFG),
    Children = [
		{verkle_db, {tree2, start_link, [["database"]]}, permanent, 5000, worker, [tree2]},
		{A5, {tree, start_link, [CFG]}, permanent, 5000, worker, [tree]},
		{A6, {parameters, start_link, [CFG]}, permanent, 5000, worker, [parameters]}
	       ],
    {ok, { {one_for_one, 5, 10}, Children} }.
