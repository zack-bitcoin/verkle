-module(unit_tests).
-export([doit/1]).

doit(0) ->
    S = success,
    io:fwrite("leaf\n"),
    S = leaf:test(1),
    io:fwrite("stem\n"),
    S = stem:test(1),
    io:fwrite("get\n"),
    S = get:test(1),
    lists:map(fun(N) ->
                      io:fwrite("fr "),
                      io:fwrite(integer_to_list(N)),
                      io:fwrite("\n"),
                      S = fr:test(N)
              end, [2,3,5,6,10,11,17,19,20,21,22]),
    lists:map(fun(N) ->
                      io:fwrite("ed "),
                      io:fwrite(integer_to_list(N)),
                      io:fwrite("\n"),
                      S = ed:test(N)
              end, [1,2,4,5,7,8,9,10,11,12]),
    lists:map(fun(N) ->
                      io:fwrite("poly "),
                      io:fwrite(integer_to_list(N)),
                      io:fwrite("\n"),
                      S = poly:test(N)
              end, [2,3]),
    lists:map(fun(N) ->
                      io:fwrite("multi exponent "),
                      io:fwrite(integer_to_list(N)),
                      io:fwrite("\n"),
                      S = 
                          multi_exponent:test(N)
              end, [0,1,5,6,7,8]),
    S = precomputed_multi_exponent:test(1),
    lists:map(fun(N) ->
                      S = ipa:test(N)
              end, [1,3,5,7]),
    S = verify2:test(),
    {_, _} = multiproof:test(7),
    S.
    
    
