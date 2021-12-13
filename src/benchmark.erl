-module(benchmark).
-export([doit/1]).

-define(ID, trie01).
-include("constants.hrl").

range(A, B) when (A < B) ->
    [A|range(A+1, B)];
range(A, A) -> [].

doit(1) ->
    verkle_app:start(normal, []),
    CFG = trie:cfg(?ID),
    Loc = 1,
    Times = 80000,
    %Times = 3,
    %Many = range(1, min(100, Times)),
    %Many = range(1, Times - 2),
    %Many = [1,2],
    io:fwrite("making leaves\n"),
    Leaves = 
        lists:map(
          fun(N) -> 
                  %Key0 = Times + 1 - N,
                  %<<Key:256>> = <<(-Key0):256>>,
                  %Key0 = 1234567*N,
                  <<Key0:256>> = 
                      crypto:strong_rand_bytes(32),
                  #leaf{key = Key0, value = <<N:16>>}
          %end, Many),
          end, range(1, Times+1)),
    io:fwrite("made leaves \n"),
    Many = lists:map(fun(#leaf{key = K}) -> K end,
                     Leaves),
    io:fwrite("benchmark for "),
    io:fwrite(integer_to_list(Times)),
    io:fwrite(" many elements \n"),
    io:fwrite("load up the batch database\n"),
    T1 = erlang:timestamp(),
    {NewLoc, stem, _} = 
        store:batch(Leaves, Loc, CFG),
    T2 = erlang:timestamp(),
    io:fwrite("make proof\n"),
    Proof = 
        get:batch(Many, NewLoc, CFG),
    T3 = erlang:timestamp(),
    io:fwrite("verify proof\n"),
    Root = stem:root(stem:get(NewLoc, CFG)),
    {true, Leaves2} = 
        verify:proof(Root, Proof, CFG),
    T4 = erlang:timestamp(),
    true = (length(Leaves2) == length(Many)),
    io:fwrite("measured in millionths of a second. 6 decimals. \n"),
    {{load_tree, timer:now_diff(T2, T1)},
     {make_proof, 
      timer:now_diff(T3, T2)},
     {verify, timer:now_diff(T4, T3)}}.
    
