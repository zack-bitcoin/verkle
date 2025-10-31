-module(verkle_sup).
-behaviour(supervisor).
-export([start_link/7,init/1,stop/1]).
-define(CHILD(I, Type), {I, {I, start_link, []}, permanent, 5000, Type, [I]}).
-include("constants.hrl").
start_link(KeyLength, Size, ID, Amount, Meta, Mode, Location) -> 
    %keylength is the number of bytes to encode the path that you follow on the verkle.
    HashSize = 32,
    CFG = cfg_verkle:new(KeyLength, Size, ID, 
                  Meta, HashSize, Mode),
    supervisor:start_link({global, cfg_verkle:id(CFG)}, ?MODULE, [CFG, Amount, Mode, Location]).
stop(ID) -> 
    CFG = tree:cfg(ID),
    supervisor:terminate_child({global, ID}, ids_verkle:main(CFG)),
    dump_sup:stop(ids_verkle:stem(CFG)),
    supervisor:terminate_child({global, ID}, ids_verkle:stem(CFG)),
    dump_sup:stop(ids_verkle:leaf(CFG)),
    supervisor:terminate_child({global, ID}, ids_verkle:leaf(CFG)),
    %supervisor:terminate_child({global, ID}, ids_verkle:bits(CFG)),
    halt().

%verkle01_main).
    %halt().
init([CFG, Amount, Mode, Location]) ->
    %Size is the size of the data we store in the verkle.
    %Amount is only used for RAM mode, because we need to allocate the space used for bits.
    KeyLength = cfg_verkle:path(CFG),
    HashSize = cfg_verkle:hash_size(CFG),
    Size = cfg_verkle:value(CFG)+cfg_verkle:meta(CFG),
    ID = cfg_verkle:id(CFG),
    %IDS = atom_to_list(ID),
    %A2 = list_to_atom(IDS++"_bits"),
    A3 = ids_verkle:leaf(CFG),
    A4 = ids_verkle:stem(CFG),
    A5 = ids_verkle:main(CFG),
    A6 = ids_verkle:parameters(CFG),
    A7 = parameters,
    %L2 = Location ++ "data/" ++ IDS ++ "_verkle_bits.db",
    Children = [
		{list_to_atom("verkle_db"), {tree2, start_link, [["database"]]}, permanent, 5000, worker, [tree2]},
                {A3, {dump_sup, start_link, [A3, KeyLength+Size, Amount, Mode, Location]}, permanent, 5000, supervisor, [dump_sup]},
		%{A4, {dump_sup, start_link, [A4, (?nwidth div 4)+(?nwidth*(HashSize + KeyLength)) + (2*HashSize), Amount, Mode, Location]}, permanent, 5000, supervisor, [dump_sup]},
		{A4, {dump_sup, start_link, [A4, (?nwidth)+(?nwidth*(HashSize + KeyLength)) + (2*HashSize), Amount, Mode, Location]}, permanent, 5000, supervisor, [dump_sup]},%256 + (256 * (32 + 32)) + (2*32) = 16704
		{A5, {tree, start_link, [CFG]}, permanent, 5000, worker, [tree]},
		%{A6, {parameters, start_link, []}, permanent, 5000, worker, [parameters]},
		{A6, {parameters, start_link, [CFG]}, permanent, 5000, worker, [parameters]}
	       ],
    {ok, { {one_for_one, 5, 10}, Children} }.
