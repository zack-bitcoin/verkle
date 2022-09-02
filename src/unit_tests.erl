-module(unit_tests).
-export([doit/1]).

doit(0) ->
    S = success,
    S = leaf:test(1),
    S = stem2:test(1),
    S = get2:test(1),
    lists:map(fun(N) ->
                      io:fwrite(integer_to_list(N)),
                      io:fwrite("\n"),
                      S = fr:test(N)
              end, [2,3,5,6,10,11,17,19,20,21,22]),
    lists:map(fun(N) ->
                      S = ed:test(N)
              end, [1,2,3,4,5,7,8,9]),
    lists:map(fun(N) ->
                      S = poly2:test(N)
              end, [2,3,4,5,6]),
    lists:map(fun(N) ->
                      S = 
                          multi_exponent:test(N)
              end, [0,1,5,6]),
    S = store2:test(1),
    lists:map(fun(N) ->
                      S = ipa2:test(N)
              end, [1,3,5]),
    S = verify2:test(),
    S = multiproof2:test(7),
    S.
    
    
