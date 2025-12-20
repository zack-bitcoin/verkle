-module(benchmark).
-export([doit/0, doit/2, now/0]).

-define(ID, tree01).
-include("constants.hrl").

-define(sanity, false).

range(A, B) when (A < B) ->
    [A|range(A+1, B)];
range(A, A) -> [].

now() ->
    if
        ?sanity ->
            {_, B, C} = erlang:timestamp(),
            T = (1000*(B rem 1000)) + (C div 1000),
            io:fwrite(integer_to_list(T)),
            io:fwrite("\n"),
            ok;
        true ->
            ok
    end.

doit() ->
    doit(5000, 100).

doit(InTree, ToProve) ->
%{{load_tree,1 579 227},{make_proof,1 800 334},{verify,375 556}}
    
    Loc = 1,
    Times = InTree,
    Prove = ToProve,
    io:fwrite("making leaves\n"),
    Leaves = 
        lists:map(
          fun(N) -> 
                  <<Key0:256>> = 
                      crypto:strong_rand_bytes(32),
                  leaf_verkle:new(Key0, <<N:16>>)
          end, range(1, Times+1)),
    io:fwrite("made leaves \n"),
    Many = lists:map(fun(Leaf) -> 
                             leaf_verkle:raw_key(Leaf) end,
                     Leaves),
    io:fwrite("benchmark for "),
    io:fwrite(integer_to_list(Times)),
    io:fwrite(" many elements in the tree, and we are proving " ++ integer_to_list(Prove) ++ " of them\n"),
    io:fwrite("load up the batch database\n"),
    T1 = erlang:timestamp(),
    {NewLoc, stem, _} = 
        store_verkle:batch(Leaves, Loc),
    T2 = erlang:timestamp(),
    {Keys, _} = lists:split(Prove, Many),
    io:fwrite("make proof\n"),
    {Proof, _} = 
        get_verkle:batch(Many, NewLoc),
    T3 = erlang:timestamp(),
    io:fwrite("verify proof\n"),
    Root = stem_verkle:root(stem_verkle:get(NewLoc)),
    {true, Leaves2, _} = 
        verify_verkle:proof(Proof),
    T4 = erlang:timestamp(),
    true = (length(Leaves2) == length(Many)),
    io:fwrite("measured in millionths of a second. 6 decimals. \n"),
    {{load_tree, timer:now_diff(T2, T1)},
     {make_proof, 
      timer:now_diff(T3, T2)},
     {verify, timer:now_diff(T4, T3)}}.


%get proof overview
% lookup stems and leaves 25%
% make multiproof 8%
% calc random R 4% 
% calc G %45
% poly H %9
% opening G-E %2

% verify proof overview
% 70% is in multi_exponent:doit 

% storage overview
% 30% is the precomputed multi_exponent
    


    
