-module(c_ed).
-export([setup/1,

         %finite stuff
         neg/1, sub/2, add/2, mul/2, 
         square/1, pow/2, short_pow/2,

         %ed25519 stuff
         double/1, padd/2, pmul/2, pmul_long/2,
         pmul_long_fast/2,
         
         ctest/1
]).

-on_load(init/0).

init() ->
    ok = erlang:load_nif("./ebin/ed25519", 0),
    setup(0),
    ok.

setup(_) ->
    %defined in C.
    ok.
neg(_) ->
    ok.
sub(_, _) ->
    ok.
add(_, _) ->
    ok.
mul(_, _) ->
    ok.
square(_) ->
    ok.
pow(_, _) ->
    ok.
short_pow(_, _) ->
    ok.

double(_) ->
    ok.
padd(_, _) ->
    ok.
pmul(_, _) ->
    ok.
pmul_long(_, _) ->
    ok.
pmul_long_fast(_, _) ->
    ok.
ctest(_) ->
    ok.



