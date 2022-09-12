-module(fr_test).
-export([test/1]).

test(1) ->
    io:fwrite("test pow\n"),
    Q = fr:prime(),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    %A0 = 10,
    A = A0 rem Q,
    <<B0:256>> = crypto:strong_rand_bytes(32),
    %B0 = 10,
    B = B0 rem Q,
    AE = fr:encode(A),
    New = fr:decode(fr:pow(AE, <<B:256/little>>)),
    %New = decode(fr:pow(AE, B)),
%                     reverse_bytes(<<B:256>>))),
                     %reverse_bytes(<<B:256>>))),
    Old = basics:rlpow(A, B, Q),
    if
        (New == Old) -> ok;
        true -> io:write({New, Old})
    end,
    success.
    
