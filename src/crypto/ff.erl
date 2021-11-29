-module(ff).
-export([sub/3, add/3, mul/3, divide/3, 
         pow/3, add_all/2,
         mod/2,
         inverse/2, batch_inverse/2, neg/2]).

mod(X,Y)->(X rem Y + Y) rem Y.
symetric_view([], _) -> [];
symetric_view([H|T], Y) ->
    [symetric_view(H, Y)|
     symetric_view(T, Y)];
symetric_view(X, Y) ->
    Y2 = Y div 2,
    if
        (X > Y2) -> X - Y;
        true -> X
    end.
sub(A, B, Base) ->
    mod(A - B, Base).
neg(A, Base) ->
    sub(0, A, Base).
add(A, B, Base) ->
    mod(A + B, Base).
mul(A, B, Base) ->
    mod(A * B, Base).
divide(A, B, N) ->
    B2 = inverse(B, N),
    mul(A, B2, N).
pow(_, 0, _) -> 1;
pow(A, B, N) ->
    basics:lrpow(A, B, N).

add_all([A], _) -> A;
add_all([A, B|T], Base) -> 
    add_all([add(A, B, Base)|T], Base).
inverse(A, Base) ->
    basics:inverse(A, Base).

pis([], _, _) -> [];
pis([H|T], A, B) -> 
    X = mul(H, A, B),
    [X|pis(T, X, B)].
batch_inverse(Vs, Base) ->
    [All|V2] = lists:reverse(pis(Vs, 1, Base)),%[v16, v15, v14, v13, v12, v1]
    AllI = inverse(All, Base),%i16
    VI = lists:map(
           fun(V) -> mul(AllI, V, Base) end,
           V2), %[i6, i56, i46, i36, i26]
    V3 = lists:reverse(pis(lists:reverse(Vs), 1, Base)),%[v16, v26, v36, v46, v56, v6]
    V4 = tl(V3)++[1],%[v26, v36, v46, v56, v6, 1]
    VI2 = [AllI|lists:reverse(VI)],%[i16, i26, i36, i46, i56, i6]
    lists:zipwith(fun(A, B) ->
                          mul(A, B, Base)
                  end, V4, VI2).
