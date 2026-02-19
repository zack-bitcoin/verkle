-module(tree2).
-behaviour(gen_server).
-export([start_link/2,code_change/3,handle_call/3,handle_cast/2,handle_info/2,init/1,terminate/2, 
         read/2, store/2, test/0, root_hash/2, empty/0,
         reset/1, quick_save/1, reload/1]).

%Stores variables sized bytes onto the hard drive. returns the position in the file where the data is stored. 

-record(d, {name, location, top, file}).

init({Name, Location}) ->
    process_flag(trap_exit, true),
    %L = Location ++ "data/"++atom_to_list(Name)++".db",
    L = name2file(Name, Location),
    io:fwrite("starting tree 2 location is "),
    io:fwrite(L),
    io:fwrite("\n"),
    {ok, F} = file:open(L, [write, read, raw, binary]),
    Top = read_top_from_file(Name, Location),
    io:fwrite("tree2 read top as: " ++ integer_to_list(Top) ++ "\n"),
    Top2 = if
	       (Top == 1) -> 
		   Bytes = stem_verkle:serialize(stem_verkle:new_empty()),
		   S = size(Bytes),
		   Bytes2 = <<S:16, Bytes/binary>>,
		   file:pwrite(F, Top, Bytes2),
		   NewTop = Top + S+2,
		   NewTop;
	       true ->
		   Top
	   end,
    {ok, #d{name = Name, location = Location, top = Top2, file = F}}.
start_link(Name, Location) -> %keylength, or M is the size outputed by hash:doit(_). 
    %gen_server:start_link({local, ?MODULE}, ?MODULE, Name, []).
    A5 = ids_verkle:main(Name),
    gen_server:start_link({global, A5}, ?MODULE, {Name, Location}, []).
code_change(_OldVsn, State, _Extra) -> {ok, State}.
terminate(_, D) -> 
    file:close(D#d.file),
    file:write_file(top_file(D#d.name, D#d.location), term_to_binary(D#d.top)),
    io:format("tree2 died!"), ok.
handle_info(_, X) -> {noreply, X}.
handle_cast(reload, X) -> 
    #d{name = Name, file = F0, location = Location} = X,
    %file:close(F0),
    L = name2file(Name, Location),
    {ok, F} = file:open(L, [write, read, raw, binary]),
    Top = read_top_from_file(Name, Location),
    io:fwrite("tree2 reloaded. top is " ++ integer_to_list(Top) ++ "\n"),
    X2 = X#d{file = F, top = Top},
    {noreply, X2};
handle_cast(reset, X) -> 
    {noreply, X#d{top = 1}};
handle_cast(_, X) -> 
    {noreply, X}.
handle_call({read, Pointer}, _From, 
            X = #d{file = File}) -> 
    true = is_integer(Pointer),
    io:fwrite("tree2 read pointer " ++ integer_to_list(Pointer) ++ "\n"),
    {ok, <<Size:16>>} = file:pread(File, Pointer, 2),
    R = file:pread(File, Pointer+2, Size),
    {reply, R, X};
handle_call({store, Bytes}, _From, 
            X = #d{top = Top, file = File}) -> 
    S = size(Bytes),
    Bytes2 = <<S:16, Bytes/binary>>,
    file:pwrite(File, Top, Bytes2),
    NewTop = Top + S+2,
    {reply, Top, X#d{top = NewTop}};
handle_call(file, _From, X) -> 
    {reply, X#d.file, X};
handle_call(quick_save, _From, X) -> 
    TF = top_file(X#d.name, X#d.location),
    io:fwrite("tree2 is quick saving to file " ++ TF ++ "\n"),
    %file:write(TF, term_to_binary(X#d.top)),
    file:write_file(TF, term_to_binary(X#d.top)),
    %file:datasync(X#d.file),
    file:close(X#d.file),
    L = name2file(X#d.name, X#d.location),
    {ok, F} = file:open(L, [write, read, raw, binary]),
    X2 = X#d{file = F},
    {reply, ok, X2};
handle_call(_, _From, X) -> {reply, X, X}.

name2file(Name, Location) ->
    Location ++ "data/"++atom_to_list(Name)++".db".
top_file(Name, Location) ->
    %atom_to_list(Name) ++ "top".
    Location ++ "data/"++atom_to_list(Name)++"_top.db".
read_top_from_file(Name, Location) ->
    TF = top_file(Name, Location),
    case file:read_file(TF) of
        {ok, <<>>} -> 1;
        {ok, Out} -> binary_to_term(Out);
        {error, enoent} -> 
	    %stem_verkle:put(stem_verkle:new_empty()),%empty is always stored in 1. we don't need to record this in a database, it can be hardcoded in the software.
	    1;
        {error, Reason} ->
            io:fwrite(Reason),
            1=2
    end.

root_hash(Pointer, ID) ->
    S = stem_verkle:get(Pointer, ID),
    stem_verkle:hash(S).
 
store(Bytes, ID) -> 
    %gen_server:call(?MODULE, {store, Bytes}).
    gen_server:call({global, ids_verkle:main_id(ID)}, {store, Bytes}).

read(P, ID) ->
    %gen_server:call(?MODULE, {read, P}).
    gen_server:call({global, ids_verkle:main_id(ID)}, {read, P}).

reset(ID) ->
    %gen_server:cast(?MODULE, reset).
    gen_server:cast({global, ids_verkle:main_id(ID)}, reset).

quick_save(ID) ->
    %gen_server:call(?MODULE, quick_save).
    gen_server:call({global, ids_verkle:main_id(ID)}, quick_save).

reload(ID) ->
    %gen_server:call(?MODULE, reload).
    gen_server:call({global, ids_verkle:main_id(ID)}, reload).

empty() -> 1.



test() ->
    ID = tree01,
    reset(ID),
    D = <<"Test Data">>,
    P = store(D, ID),
    {ok, D} = read(P, ID),
    success.
