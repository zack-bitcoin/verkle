-module(c_secp).
-export([
         %finite field
         pow/2, short_pow/2, mul/2, square/1, 
         sub/2, add/2, neg/1,

         %elliptic curve 
         padd/2, double/1, pmul/2, pmul_long/2]).
-on_load(init/0).
init() ->
    ok = erlang:load_nif("./ebin/c_secp", 0),
    %setup(0),
    ok.

%setup(_) ->
    %defined in C.
%    ok.

%finite field stuff
pow(_, _) ->
    ok.
short_pow(_, _) ->
    ok.
mul(_, _) ->
    ok.
square(_) ->
    ok.
sub(_, _) ->
    ok.
add(_, _) ->
    ok.
neg(_) ->
    ok.

%elliptic point stuff
padd(_, _) ->
    ok.
double(_) ->
    ok.
pmul(_, _) ->
    ok.
pmul_long(_, _) ->
    ok.
