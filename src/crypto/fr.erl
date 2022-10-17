-module(fr).
-export([
         mul/2, 
         add/2, 
         neg/1,
         sub/2, %inverse/1,
         inv/1,
         square/1,
         pow/2,
         short_pow/2,
         encode/1, decode/1,
         test/1,
         ctest/1,
         setup/1,
         batch_inverse/1,
         prime/0,
         reverse_bytes/1,
         add_all/1


        ]).
-on_load(init/0).
init() ->
    erlang:load_nif("./ebin/fr", 0).


%This is the finite field on top of the elliptic curve.

%uses montgomery notation for faster modular multiplication.

%binaries are in little endian order, so the bytes are already in order to fit into registers.

%8*(2^252+27742317777372353535851937790883648493)
-define(q, %57896044618658097711785492504343953926856930875039260848015607506283634007912).
        7237005577332262213973186563042994240857116359379907606001950938285454250989).
%904625697166532776746648320380374280107139544922488450750243867285681781373).
%6554484396890773809930967563523245729705921265872317281365359162392183254199).

%2^256 rem q
%-define(r1, 7237005577332262213973186563042994240413239274941949949428319933631315875101).
        %4365854490173040654744536428792730448269323145811170256246478247246014318553).

%maybe this is r2??            4365854490173040654744536428792730448269323145811170256246478247246014318553
% R1 57896044618658097711785492504343953926413053790601303191441976501629495632024

%r*r rem q
-define(r2, %23338732233167498087203954714173396606307505666509137570975855394539477764808).
1627715501170711445284395025044413883736156588369414752970002579683115011841).

%r*r*r rem n
%-define(r3, 6479107319630627712989486218399433800251238082664018703558868829414071968475).

%1/r rem n
%-define(ir, 4458503529701987551646482192314240623644693141688353256590997718326214331684).

prime() -> ?q.
reverse_bytes(<<X:256>>) -> <<X:256/little>>.

encode([]) -> [];
encode([H|T]) -> 
    [encode(H)|encode(T)];
encode(0) ->
    <<0:256>>;
%encode(1) ->
%<<29,149,152,141,116,49,236,214,112,207,125,115,244,
%  91,239,198,254,255,255,255,255,255,255,255,255,255,
%  255,255,255,255,255,15>>;
encode(A) when ((A < ?q) and (A > -1)) ->
    %mul(reverse_bytes(<<A:256>>),
    %    reverse_bytes(<<?r2:256>>));
    mul(<<A:256/little>>,
        <<?r2:256/little>>);
encode(A) when (A < 0)->
    neg(encode(-A));
encode(A) when (A > (?q-1)) ->
    encode(A rem ?q).


decode([]) -> [];
decode([A|B]) -> 
    [decode(A)|decode(B)];
decode(C = <<_:256>>) ->
    %X = mul(C, reverse_bytes(<<1:256>>)),
    X = mul(C, (<<1:256/little>>)),
    %<<Y:256>> = reverse_bytes(X),
    <<Y:256/little>> = X,
    Y.
    %binary:decode_unsigned(X, little).

%these functions are defined in c. 
setup(_) -> ok.
add(_, _) -> ok.
neg(_) -> ok.
sub(_, _) -> ok.
mul(_, _) -> ok.
square(_) -> ok.
inv(X) -> encode(ff:inverse(decode(X), ?q)).
pow(_, _) -> ok.
short_pow(_, _) -> ok.


add_all([]) -> fr:encode(0);
add_all([X]) -> X;
add_all([A,B|T]) ->
    add_all([add(A, B)|T]).

pis([], _) -> [];
pis([H|T], A) -> 
    X = mul(H, A),
    [X|pis(T, X)].
batch_inverse(Vs) ->
    [All|V2] = lists:reverse(pis(Vs, encode(1))),%[v16, v15, v14, v13, v12, v1]
    AllI = encode(ff:inverse(decode(All), ?q)),%i16
    VI = lists:map(
           fun(V) -> mul(AllI, V) end,
           V2), %[i6, i56, i46, i36, i26]
    V3 = lists:reverse(pis(lists:reverse(Vs), encode(1))),%[v16, v26, v36, v46, v56, v6]
    V4 = tl(V3)++[encode(1)],%[v26, v36, v46, v56, v6, 1]
    VI2 = [AllI|lists:reverse(VI)],%[i16, i26, i36, i46, i56, i6]
%    io:fwrite({{all, fr:decode(All)}, {v2, fr:decode(V2)}, 
%               {all_i, fr:decode(AllI)}, {vi, fr:decode(VI)}, 
%               {v3, fr:decode(V3)}, {v4, fr:decode(V4)},
%               {vi2, fr:decode(VI2)}}),
    lists:zipwith(fun(A, B) ->
                          mul(A, B)
                  end, V4, VI2).

-define(sub3(A, B),
    if
        B>A -> A + ?q - B;
        true -> A - B
    end).

ctest(_) ->
    ok.

range(N, N) -> [N];
range(A, B) when (A < B) -> 
    [A|range(A+1, B)].
test(2) ->
    io:fwrite("subtract test\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    A1 = A0 rem ?q,
    B1 = B0 rem ?q,
    A = encode(A1),
    B = encode(B1),
    S = decode(sub(A, B)),
    S = decode(sub(A, B)),
    S = (?q - B1 + A1) rem ?q,
    success;
test(3) ->
    io:fwrite("encode decode test\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    A1 = A0 rem ?q,
    A = encode(A1),
    A1 = decode(A),
    success;
%A = inverse(inverse(A));
test(4) ->
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    A1 = (A0 div 1) rem ?q,
    B1 = (B0 div 1) rem ?q,
    A = encode(A1),
    B = encode(B1),
    T1 = erlang:timestamp(),
    Many = 50000,
    lists:foldl(fun(_, _) ->
                      sub(A, B)
              end, 0, range(0, Many)),
    T2 = erlang:timestamp(),
    {c, timer:now_diff(T2, T1)/Many};
test(5) ->
    %testing addition.
    io:fwrite("addition test\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    A1 = A0 rem ?q,
    B1 = B0 rem ?q,
    A = encode(A1),
    B = encode(B1),
    S = decode(add(A, B)),
    S = decode(add(A, B)),
    S = (A1 + B1) rem ?q,
    success;
test(6) ->
    %testing multiplication.
    io:fwrite("multiply test \n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    A1 = A0 rem ?q,
    B1 = B0 rem ?q,
    A = encode(A1),
    B = encode(B1),
    S = decode(mul(A, B)),
    S = decode(mul(A, B)),
    S = (A1 * B1) rem ?q,
    success;
test(7) ->
    io:fwrite("multiply speed test \n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    A1 = (A0 div 1) rem ?q,
    B1 = (B0 div 1) rem ?q,
    A = encode(A1),
    B = encode(B1),
    Many = 50000,
    R = range(B0, B0 + Many),
    R2 = lists:map(
           fun(X) -> encode(X rem ?q) end, R),
    T1 = erlang:timestamp(),
    lists:map(fun(I) ->
                      mul(A, I)
              end, R2),
    T2 = erlang:timestamp(),
    lists:map(fun(I) ->
                      C0 = (A0 * I) rem ?q
              end, R),
    T3 = erlang:timestamp(),
    {{c, timer:now_diff(T2, T1)/Many},
     {erl, timer:now_diff(T3, T2)/Many}};
test(8) ->
    %more accurate multiplication speed test.
    Many = 100000,
    R = lists:map(fun(_) ->
                          <<A0:256>> = crypto:strong_rand_bytes(32),
                          <<B0:256>> = crypto:strong_rand_bytes(32),
                          {A0 rem ?q,
                           B0 rem ?q}
                  end, range(0, Many)),
    R2 = lists:map(fun({X, Y}) ->
                           {encode(X),
                            encode(Y)}
                   end, R),
    T1 = erlang:timestamp(),
    lists:foldl(fun({X, Y}, _) ->
                      (X*Y) rem ?q,
                        0
                end, 0, R),
    T2 = erlang:timestamp(),
    lists:foldl(fun({X, Y}, _) ->
                        mul(X, Y),
                        0
                end, 0, R2),
    T3 = erlang:timestamp(),
    %erl sub
    lists:foldl(fun({X, Y}, _) ->
                      if
                          X > Y -> X - Y;
                          true -> ?q - Y + X
                      end,
                        0
                end, 0, R),
    T4 = erlang:timestamp(),
    %c sub
    lists:foldl(fun({X, Y}, _) ->
                        sub(X, Y)
                end, 0, R2),
    T5 = erlang:timestamp(),
    lists:foldl(fun({X, Y}, _) ->
                      C = X+Y,
                      if
                          C > ?q -> C - ?q;
                          true -> C
                      end,
                        0
                end, 0, R),
    T6 = erlang:timestamp(),
    lists:foldl(fun({X, Y}, _) ->
                  add(X, Y),
                  0
          end, 0, R2),
    T7 = erlang:timestamp(),
    lists:foldl(fun(A, B) -> 0 end, 0, R2),
    T8 = erlang:timestamp(),
    Empty = timer:now_diff(T8, T7),
    MERL = timer:now_diff(T2, T1),
    MC = timer:now_diff(T3, T2),
    SERL = timer:now_diff(T4, T3),
    SC = timer:now_diff(T5, T4),
    AERL = timer:now_diff(T6, T5),
    AC = timer:now_diff(T7, T6),

    {{empty, Empty/Many},
     {mul, {erl, (MERL - Empty)/Many},
      {c, (MC - Empty)/Many}},
     {sub, {erl, (SERL - Empty)/Many},
      {c, (SC - Empty)/Many}},
     {add, {erl, (AERL - Empty)/Many},
      {c, (AC - Empty)/Many}}};
test(10) ->
    io:fwrite("square test\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    %A0 = 3,
    A = A0 rem ?q,
    S1 = decode(square(encode(A))),
    S1 = (A*A rem ?q),
    success;
test(11) ->
    io:fwrite("inverse test\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    A = A0 rem ?q,
    A = decode(inv(inv(encode(A)))),
    IA = decode(inv(encode(A))),
    1 = A * IA rem ?q,
    success;
test(12) ->
    io:fwrite("inverse speed test\n"),
    Many = 1000,
    R = range(0, Many),
    R2 = lists:map(
           fun(_) -> 
                   <<N0:256>> = 
                       crypto:strong_rand_bytes(
                         32),
                   N0 rem ?q
           end, R),
    R3 = lists:map(
           fun(X) -> encode(X) end, R2),
    T1 = erlang:timestamp(),
    lists:map(fun(I) -> inv(I) end, R3),
    T2 = erlang:timestamp(),
    lists:map(fun(I) ->
                        basics:inverse(I, ?q)
                end, R2),
    T3 = erlang:timestamp(),
    {{c, timer:now_diff(T2, T1)/Many},
     {erl, timer:now_diff(T3, T2)/Many}};
test(17) ->
    io:fwrite("test pow\n"),
    %<<A0:256>> = crypto:strong_rand_bytes(32),
    A0 = 1,
    A = A0 rem ?q,
    %<<B0:256>> = crypto:strong_rand_bytes(32),
    B0 = 1,
    B = B0 rem ?q,
    AE = encode(A),
    New = decode(pow(AE, <<B:256/little>>)),
    %New = decode(pow(AE, B)),
%                     reverse_bytes(<<B:256>>))),
                     %reverse_bytes(<<B:256>>))),
    Old = basics:rlpow(A, B, ?q),
    true = New == Old,
    success;
%success;
test(18) ->
    io:fwrite("test pow speed\n"),
    Many = 100,
    R = range(0, Many),
    R2 = lists:map(
           fun(_) ->
                   <<A0:256>> = crypto:strong_rand_bytes(32),
                   <<B0:256>> = crypto:strong_rand_bytes(32),
                   A = A0 rem ?q,
                   B = B0 rem ?q,
                   Ae = encode(A),
                   Be = reverse_bytes(<<B:256>>),
                   {A, B, Ae, Be}
           end, R),
    T1 = erlang:timestamp(),
    lists:foldl(fun({A, B, _, _}, _) ->
                        basics:rlpow(A, B, ?q)
                end, 0, R2),
    T2 = erlang:timestamp(),
    lists:foldl(fun({_, _, A, B}, _) ->
                        pow(A, B)
                end, 0, R2),
    T3 = erlang:timestamp(),
    {{erl, timer:now_diff(T2, T1)/Many},
     {c, timer:now_diff(T3, T2)/Many}};
test(19) ->
    io:fwrite("test short_pow\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    A = A0 rem ?q,
    <<B:16>> = crypto:strong_rand_bytes(2),
    C = decode(short_pow(encode(A), B)),
    D = basics:rlpow(A, B, ?q),
    C = D,
    %{A, B, C};
    success;
test(20) ->
    io:fwrite("test neg\n"),
    <<A0:256>> = crypto:strong_rand_bytes(32),
    A = A0 rem ?q,
    NA = ?q - A,
    NA = decode(neg(encode(A))),
    success;
test(21) ->
    io:fwrite("batch inverse\n"),
    A = encode([2,3,4,5,6]),
    AI = batch_inverse(A),
    [1,1,1,1,1] = 
        fr:decode(
          lists:zipwith(fun(X, Y) -> mul(X, Y) end,
                        A, AI)),
    success;
test(22) ->
    io:fwrite("test it doesn't overwrite existing data.\n"),
    S = [1, 101],
    [A, B] = encode(S),
    mul(A, B),
    add(A, B),
    neg(A),
    inv(A),
    square(A),
    pow(A, B),
    short_pow(A, B),
    decode(B),
    batch_inverse([A, B]),
    add_all([A, B]),
    S = decode([A, B]),
    success;
test(23) ->
    io:fwrite("fr on big numbers\n"),
    N = 2,
    Z = 1000000000000000000000000000000000000,
    B = 6557398279811269422222260660686945123758959220525701212948355841020816233267,
    [Ze, Be, Ne] = encode([Z, B, N]),
    [Z, B, N] = decode([Ze, Be, Ne]),

    true = ((Z + B) rem ?q) == decode(add(Ze, Be)),
    true = ((B - Z) rem ?q) == decode(sub(Be, Ze)),
    true = ((B * Z) rem ?q) == decode(mul(Be, Ze)),
    true = ((Z + 1) rem ?q) == decode(add(Ze, encode(1))),
    success.
    

    

                          

    


%A = encode(2),
%    B = reverse_bytes(<<3:256>>),
%    decode(pow(A, B)).



    

