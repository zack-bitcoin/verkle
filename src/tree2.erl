-module(tree2).
-behaviour(gen_server).
-export([start_link/1,code_change/3,handle_call/3,handle_cast/2,handle_info/2,init/1,terminate/2, 
         read/1, store/1, test/0, root_hash/1, 
         reset/0, quick_save/0, reload/0]).

-record(d, {name, file, top}).

init(Name) ->
    io:fwrite("tree2 init\n"),
    process_flag(trap_exit, true),
    {ok, F} = file:open(Name, [write, read, raw, binary]),
    Top = read_top_from_file(Name),
    {ok, #d{name = Name, file = F, top = Top}}.
start_link([Name]) -> %keylength, or M is the size outputed by hash:doit(_). 
    gen_server:start_link({local, ?MODULE}, ?MODULE, Name, []).
code_change(_OldVsn, State, _Extra) -> {ok, State}.
terminate(_, D) -> 
    file:close(D#d.file),
    file:write(top_file(D#d.name), term_to_binary(D#d.top)),
    io:format("tree2 died!"), ok.
handle_info(_, X) -> {noreply, X}.
handle_cast(reload, X) -> 
    #d{name = Name, file = F0} = X,
    file:close(F0),
    {ok, F} = file:open(Name, [write, read, raw, binary]),
    Top = read_top_from_file(Name),
    X2 = X#d{file = F, name = Name, top = Top},
    {noreply, X2};
handle_cast(reset, X) -> 
    {noreply, X#d{top = 1}};
handle_cast(_, X) -> 
    {noreply, X}.
handle_call({read, Pointer, Size}, _From, 
            X = #d{file = File}) -> 
    {reply, file:pread(File, Pointer, Size), X};
handle_call({store, Bytes}, _From, 
            X = #d{top = Top, file = File}) -> 
    file:pwrite(File, Top, Bytes),
    S = size(Bytes),
    NewTop = Top + S,
    {reply, {Top, S}, X#d{top = NewTop}};
handle_call(file, _From, X) -> 
    {reply, X#d.file, X};
handle_call(quick_save, _From, X) -> 
    file:write(top_file(X#d.name), term_to_binary(X#d.top)),
    {reply, ok, X};
handle_call(_, _From, X) -> {reply, X, X}.

top_file(Name) ->
    Name ++ "top".
read_top_from_file(Name) ->
    case file:read_file(Name++"top") of
        {ok, <<>>} -> 1;
        {ok, Out} -> binary_to_term(Out);
        {error, enoent} -> 1;
        {error, Reason} ->
            io:fwrite(Reason),
            1=2
    end.
    

root_hash(Pointer) ->
    S = stem_verkle:get(Pointer),
    stem_verkle:hash(S).
   
store(Bytes) -> 
    gen_server:call(?MODULE, {store, Bytes}).

read({P, Size}) ->
    gen_server:call(?MODULE, {read, P, Size}).

reset() ->
    gen_server:cast(?MODULE, reset).

quick_save() ->
    gen_server:call(?MODULE, quick_save).

reload() ->
    gen_server:call(?MODULE, reload).


test() ->
    reset(),
    D = <<"Test Data">>,
    P = store(D),
    {ok, D} = read(P),
    success.
