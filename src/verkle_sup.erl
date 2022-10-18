-module(verkle_sup).
-behaviour(supervisor).
-export([start_link/7,init/1,stop/1]).
-define(CHILD(I, Type), {I, {I, start_link, []}, permanent, 5000, Type, [I]}).
-include("constants.hrl").
start_link(KeyLength, Size, ID, Amount, Meta, Mode, Location) -> 
    %keylength is the number of bytes to encode the path that you follow on the verkle.
    HashSize = 32,
    CFG = cfg:new(KeyLength, Size, ID, 
                  Meta, HashSize, Mode),
    supervisor:start_link({global, cfg:id(CFG)}, ?MODULE, [CFG, Amount, Mode, Location]).
stop(ID) -> 
    CFG = trie:cfg(ID),
    supervisor:terminate_child({global, ID}, ids:main(CFG)),
    dump_sup:stop(ids:stem(CFG)),
    supervisor:terminate_child({global, ID}, ids:stem(CFG)),
    dump_sup:stop(ids:leaf(CFG)),
    supervisor:terminate_child({global, ID}, ids:leaf(CFG)),
    supervisor:terminate_child({global, ID}, ids:bits(CFG)),
    halt().

%verkle01_main).
    %halt().
init([CFG, Amount, Mode, Location]) ->
    %Size is the size of the data we store in the verkle.
    %Amount is only used for RAM mode, because we need to allocate the space used for bits.
    KeyLength = cfg:path(CFG),
    HashSize = cfg:hash_size(CFG),
    Size = cfg:value(CFG)+cfg:meta(CFG),
    ID = cfg:id(CFG),
    IDS = atom_to_list(ID),
    A2 = list_to_atom(IDS++"_bits"),
    A3 = ids:leaf(CFG),
    A4 = ids:stem(CFG),
    A5 = ids:main(CFG),
    A6 = ids:parameters(CFG),
    A7 = parameters,
    L2 = Location ++ "data/" ++ IDS ++ "_verkle_bits.db",
    Children = [{A3, {dump_sup, start_link, [A3, KeyLength+Size, Amount, Mode, Location]}, permanent, 5000, supervisor, [dump_sup]},
		%{A4, {dump_sup, start_link, [A4, (?nwidth div 4)+(?nwidth*(HashSize + KeyLength)) + (2*HashSize), Amount, Mode, Location]}, permanent, 5000, supervisor, [dump_sup]},
		{A4, {dump_sup, start_link, [A4, (?nwidth)+(?nwidth*(HashSize + KeyLength)) + (2*HashSize), Amount, Mode, Location]}, permanent, 5000, supervisor, [dump_sup]},
		{A5, {trie, start_link, [CFG]}, permanent, 5000, worker, [trie]},
		%{A6, {parameters, start_link, []}, permanent, 5000, worker, [parameters]},
		{A6, {parameters, start_link, [CFG]}, permanent, 5000, worker, [parameters]}
	       ],
    {ok, { {one_for_one, 5, 10}, Children} }.
