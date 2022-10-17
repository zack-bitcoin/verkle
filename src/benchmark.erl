-module(benchmark).
-export([doit/1, now/0]).

-define(ID, trie01).
-include("constants.hrl").

range(A, B) when (A < B) ->
    [A|range(A+1, B)];
range(A, A) -> [].

now() ->
    {_, B, C} = erlang:timestamp(),
    T = (1000*(B rem 1000)) + (C div 1000),
    io:fwrite(integer_to_list(T)),
    io:fwrite("\n").
    

doit(1) ->

%{{load_tree,23 866 703},
% {make_proof,17 454 552},
% {verify,6 873 304}}
    

    verkle_app:start(normal, []),
    CFG = trie:cfg(?ID),
    Loc = 2,
    Times = 5000,
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
                  leaf:new(Key0, <<N:16>>, 0, CFG)
                      %#leaf{key = Key0, value = <<N:16>>}%random version
                  %#leaf{key = N, value = <<N:16>>}%sequential version
          %end, Many),
          end, range(1, Times+1)),
    io:fwrite("made leaves \n"),
    Many = lists:map(fun(Leaf) -> 
                             leaf:key(Leaf) end,
                     Leaves),
    io:fwrite("benchmark for "),
    io:fwrite(integer_to_list(Times)),
    io:fwrite(" many elements \n"),
    io:fwrite("load up the batch database\n"),
    T1 = erlang:timestamp(),
    {NewLoc, stem, _} = 
        store2:batch(Leaves, Loc, CFG),
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
     {verify, timer:now_diff(T4, T3)}};

%many, go,    erl,   erl ordered
%1000  0.050  0.7   0.7
%10k   0.475  3.51   1.63

doit(2) ->
    %jubjub version
%{{load_tree,53 830 000},
% {make_proof,24 460 000},
% {verify,4 350 000}}
    CFG = trie:cfg(?ID),
    Loc = 1,
    Times = 20000,
    %Times = 100,
    %Many = range(1, min(100, Times)),
    %Many = range(, Times - 2),
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
                  %#leaf{key = Key0, value = <<N:16>>}%random version
                  leaf:new(N, <<N:16>>, 0, CFG)
                      %#leaf{key = N, value = <<N:16>>}%sequential version
          %end, Many),
          end, range(1, Times+1)),
    io:fwrite("made leaves \n"),
    %Many = lists:map(fun(#leaf{key = K}) -> K end,
    Many = lists:map(fun(Leaf) -> 
                             leaf:key(Leaf) end,
                     Leaves),
    io:fwrite("benchmark for "),
    io:fwrite(integer_to_list(Times)),
    io:fwrite(" many elements \n"),
    io:fwrite("load up the batch database\n"),
    T1 = erlang:timestamp(),
    {NewLoc, stem, _} = 
        store2:batch(Leaves, Loc, CFG),
    T2 = erlang:timestamp(),
    io:fwrite("make proof\n"),
    Proof = 
        get2:batch(Many, NewLoc, CFG),
    T3 = erlang:timestamp(),
    io:fwrite("verify proof\n"),
    Root = stem2:root(stem2:get(NewLoc, CFG)),
%    io:fwrite({NewLoc, 
%               stem2:get(NewLoc, CFG),
%               base64:encode(Root)}),
    {true, Leaves2} = 
        verify2:proof(Root, Proof, CFG),
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
    


    
