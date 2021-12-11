-module(secp256k1).
-export([test/1, make/0, addition/3, 
         multiplication/3, gen_point/1,
         field_prime/1, order/1,
         on_curve/2,
         mod/2, 

         to_jacob/1, to_affine/1, to_affine_batch/1,
         jacob_mul/3, jacob_add/3, jacob_zero/0,
         jacob_equal/3, jacob_negate/2, jacob_sub/3,
         hash_point/1,

         multi_exponent/3, simplify_Zs_batch/1,

         compress/1, decompress/1
]).

-define(pow_2_128, 340282366920938463463374607431768211456).

-record(curve, {a, b, g, n, p, e}).

%for fast operations mod the expected prime.
%assumes the values are positive.
-define(prime, 115792089237316195423570985008687907853269984665640564039457584007908834671663).
-define(prime_over4, 28948022309329048855892746252171976963317496166410141009864396001977208667916).%(?prime + 1) div 4
-define(sub(A, B), ((A - B + ?prime) rem ?prime)).%assumes B less than ?prime
-define(neg(A), (?prime - A)).%assumes A less than ?prime
-define(add(A, B), ((A + B) rem ?prime)).
%-define(add(A, B), if ((A+B) > ?prime) -> A+B - ?prime; true -> A+B end ).
-define(mul(A, B), ((A * B) rem ?prime)).
-define(order, 115792089237316195423570985008687907852837564279074904382605163141518161494337).

-define(add_mod(C), %assumes C is positive and less than ?prime
        if (C>=?prime) -> C - ?prime;
           true -> C end).
-define(sub2(A, B), %assumes A and B are positive and less than ?prime
        (if(A>=B) -> (A - B); 
           true -> (A + ?prime - B) end)).
%-define(sub2(A, B), ?sub(A, B)).
                          
add2(A, B) ->
    D = A+B,
    C = D - ?prime,
    if
        (C < 0) -> D;
        true -> C
    end.
            
add(A, B) ->
    C = A+B,
    if
        (C > ?prime) ->
            C - ?prime;
        true -> C
    end.
empty(A, B) ->
    if
        (A > B) ->
            A;
        true -> B
    end.
    

%add2(A, B) -> ?add(A, B).
add3(A, B) ->
    C = A+B,
    D = C - ?prime,
    if
        (D == abs(D)) -> D;
        true -> C
    end.
            
    

                        
%-define(sub

field_prime(C) -> C#curve.p.
order(C) -> C#curve.n.

mod(X,Y)->(X rem Y + Y) rem Y.

on_curve({X, Y}, C) ->
    #curve{a = A, b = B, p = P
         } = C,
    on_curve(A, B, X, Y, P).
on_curve(A, B, X, Y, P) ->
    %check that the point is on the curve.
    %y^2 = x^3 + A*x + B
    0 == mod(mod(mod(X*X, P)*X, P) 
             + mod(A*X, P) 
             + B 
             - mod(Y*Y, P), 
             P).

make(A, B, X, Y, P, N, Endo) ->
    #curve{a = A, b = B, g = {X, Y}, 
           p = P, n = N, e = Endo}.

det_pow(0, _) -> 0;
det_pow(_, 0) -> 1;
det_pow(A, 1) -> A;
det_pow(A, N) when ((N rem 2) == 0) -> 
    det_pow(A*A, N div 2);
det_pow(A, N) -> 
    A*det_pow(A, N-1).

hash_point({X, Y}) ->
    <<Z:256>> = hash:doit(<<X:256, Y:256>>),
    Z;
hash_point(J = {_, _, _}) ->
    P = to_affine(J),
    hash_point(P).
    
    

make() ->
    %FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFE FFFFFC2F
%2256 - 232 - 29 - 28 - 27 - 26 - 24 - 1
    P=det_pow(2, 256) -
        det_pow(2, 32) - 
        det_pow(2, 9) -
        det_pow(2, 8) -
        det_pow(2, 7) -
        det_pow(2, 6) -
        det_pow(2, 4) -
        1,
    A = 0,
    B = 7,
    X = hex_to_int("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798"),
    Y = hex_to_int("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8"),
    N = hex_to_int("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141"),%group order.
    Endomorphism = hex_to_int("7AE96A2B657C07106E64479EAC3434E99CF0497512F58995C1396C28719501EE"),
    make(A, B, X, Y, P, N, Endomorphism).

to_jacob({X, Y}) ->
    {X, Y, 1}.
%to_affine({_, _, 0}) -> infinity;
to_affine({_, _, 0}) -> {0,0};
to_affine(P = {_, _, Z}) ->
    Z2 = ff:inverse(mod(Z, ?prime), ?prime),
    to_affine(P, Z2).
to_affine({X, Y, _}, Inverse) ->
    P2 = ?mul(Inverse, Inverse),
    P3 = ?mul(Inverse, P2),
    {?mul(X, P2),
%     ?mul(Y, P3)}.
     ff:mul(Y, P3, ?prime)}.%Y is sometimes negative.

zero_spots([], _) -> [];
zero_spots([0|T], N) -> 
    [N|zero_spots(T, N+1)];
zero_spots(T, N) -> 
    zero_spots(tl(T), N+1).
insert_zeros([], P, _) -> P;
insert_zeros([N|T], P, N) ->
    [{0,1}|insert_zeros(T, P, N+1)];
insert_zeros(Ns, [P|T], M) ->
    [P|insert_zeros(Ns, T, M+1)].

    
to_affine_batch(Ps) ->
    Zs = lists:map(fun({_, _, Z}) -> Z end, 
                   Ps),
    ZeroSpots = zero_spots(Zs, 0),
    Zs2 = lists:filter(fun(X) -> not(X == 0) end,
                       Zs),
    Ps2 = lists:filter(
            fun({_, _, Z}) -> not(Z == 0) end,
            Ps),
    %Is = invert_batch(Zs, Base),
    Is = ff:batch_inverse(Zs2, ?prime),
    Ps3 = lists:zipwith(
            fun(P, I) -> to_affine(P, I) end,
            Ps2, Is),
    insert_zeros(ZeroSpots, Ps3, 0).
simplify_Zs_batch(Ps) ->
    Ps2 = to_affine_batch(Ps),
    lists:map(fun(X) -> to_jacob(X) end, Ps2).
                      
compress({X, Y}) ->
    %2 means even, 3 means odd??
    if
        ((Y rem 2) == 0) -> <<2, X:256>>;
        true -> <<3, X:256>>
    end;
compress(L = [_|_]) ->
    L2 = to_affine_batch(L),
    lists:map(fun(X) -> compress(X) end, L2);
compress(J) ->
    compress(to_affine(J)).
decompress(<<S, X:256>>) ->
    %since the exponent and the modulus are the same every time, it seems like we should be able to precompute a lot of stuff.
    %Y*Y = X*X*X + 7
    YY = 7 + ?mul(X, ?mul(X, X)),
    Y = ff:pow(YY, (?prime + 1) div 4, ?prime),
    Y2 = if
             ((Y rem 2) == (S rem 2)) -> Y;
             true -> ?prime - Y
         end,
    to_jacob({X, Y2}).
jacob_negate({X, Y, Z}, _E) ->
    {X, ?neg(Y), Z}.
jacob_equal({X1, Y1, Z1}, {X2, Y2, Z2}, E) ->
    Base = field_prime(E),
    ZZ = ff:mul(Z1, Z1, Base),
    ZZZ = ff:mul(Z1, ZZ, Base),
    ZZ2 = ff:mul(Z2, Z2, Base),
    ZZZ2 = ff:mul(Z2, ZZ2, Base),
    Check1 = ff:mul(X1, ZZ2, Base) == 
        ff:mul(X2, ZZ, Base),
    Check2 = ff:mul(Y1, ZZZ2, Base) == 
        ff:mul(Y2, ZZZ, Base),
    Check1 and Check2.
jacob_sub(P1, P2, E) -> 
    jacob_add(P1, jacob_negate(P2, E), E).
jacob_add(P, {0, _, _}, _E) -> P;
jacob_add(P, {_, 0, _}, _E) -> P;
jacob_add({0, _, _}, P, _E) -> P;
jacob_add({_, 0, _}, P, _E) -> P;
jacob_add({X1, Y1, Z1}, {X2, Y2, Z2}, E) ->
    %http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-2007-bl 
    %Base = field_prime(E),
    Z1Z1 = ?mul(Z1, Z1),
    Z2Z2 = ?mul(Z2, Z2),
    U1 = ?mul(X1, Z2Z2),
    U2 = ?mul(X2, Z1Z1),
    S1 = ?mul(Y1, ?mul(Z2, Z2Z2)),
    S2 = ?mul(Y2, ?mul(Z1, Z1Z1)),
    H = ?sub2(U2, U1),
    HH = ?mul(H, H),
    I = 4*HH,
    J = ?mul(H, I),
    R = 2 * ?sub2(S2, S1),
    %R = ?mul(2, ?sub(S2, S1)),
    if
        (H == 0) and (R == 0) -> 
            %io:fwrite("same point\n"),
            jacob_double({X1, Y1, Z1}, E);
        (H == 0) ->
            jacob_zero();
        true ->
            V = ?mul(U1, I),
            RR = ?mul(R, R),
            V2 = 2*V,
            JV2 = ?add(J, V2),
            X3 = ?sub2(RR, JV2),
            RVX3 = ?mul(R, ?sub2(V, X3)),
            %S1J = ?mul(2, ?mul(S1, J)),
            S1J = ?mul(S1*2, J),
            Y3 = ?sub2(RVX3, S1J),
            Z1pZ2a = Z1 + Z2,
            Z1pZ2 = ?add_mod(Z1pZ2a),
            %Z1pZ2 = ?add(Z1, Z2),
            Z1Z1Z2Z2a = Z1Z1 + Z2Z2,
            Z1Z1Z2Z2 = ?add_mod(Z1Z1Z2Z2a),
            %Z1Z1Z2Z2 = ?add(Z1Z1, Z2Z2),
            ZZmul = ?mul(Z1pZ2, Z1pZ2),
            %Z3 = ?mul(H, ?sub(?mul(Z1pZ2, Z1pZ2),
            %                  ?add(Z1Z1, Z2Z2))),
            Z3 = ?mul(H, ?sub2(ZZmul, Z1Z1Z2Z2)),
            {X3, Y3, Z3}
    end.
jacob_double({X1, Y1, Z1}, _Curve) ->
    %http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
    %Base = field_prime(Curve),
    A = ?mul(X1, X1),
    B = ?mul(Y1, Y1),
    C = ?mul(B, B),
    X1B = X1 + B,
    D1 = ?add_mod(X1B),
    %D1 = ?add(X1, B),
    D2 = ?mul(D1, D1),
    AC = A + C,
    ACb = ?add_mod(AC),
    D3 = ?sub2(D2, ACb),
    %D3 = ?sub(D2, ?add(A, C)),
    D = 2 * D3,
    E = 3 * A,
    F = ?mul(E, E),
    %X3 = ?sub(F, ?mul(2, D)),
    X3 = ?sub(F, 2*D),
    C8 = 8*C,
    %C8 = ?mul(8, C),
    %Y3 = ?sub(?mul(E, ?sub(D, X3)),
    Y3 = ?sub(?mul(E, ?sub(D, X3)),
                C8),
                %C * 8),
    %Z3 = ?mul(2, ?mul(Y1, Z1)),
    Z3 = ?mul(Y1*2, Z1),
    {X3, Y3, Z3}.
    
%addition(infinity, P2, _) -> P2;
addition({0,0}, P2, _) -> P2;
%addition(P1, infinity, _) -> P1;
addition(P1, {0,0}, _) -> P1;
addition(P1, P2, E) ->
    {X1, Y1} = P1,
    {X2, Y2} = P2,
    #curve{
            a = A,
            p = N
         } = E,
    if
        (X1 == X2) and (not(Y1 == Y2)) ->
            %infinity;
            {0,0};
        true ->
            M = if
                    ((P1 == P2) 
                     and (not(Y1 == 0))) ->
                        %(A+(3*x1*x1))/(2*Y1)
                        ff:divide(
                          ?add(
                            A, 
                              3 *
                              ?mul(X1, X1)),
                          ?mul(2, Y1), N);
                    (not (X1 == X2)) ->
                        %(y2-y1)/(x2-x1)
                        ff:divide(
                          ?sub(Y2, Y1),
                          ?sub(X2, X1), N)
                end, 
            X3 = ?sub(?mul(M, M), ?add(X1, X2)),
            Y3 = ?sub(
                   ?mul(
                     M, ?sub(X1, X3)),
                   Y1),
            {X3, Y3}
    end.

jacob_zero() -> {0,1,0}.
jacob_mul(P, X, E) ->
    jacob_mul(jacob_zero(), P, X, E).
jacob_mul(_, _, 0, _E) -> 
    jacob_zero();
jacob_mul(_, {_, _, 0}, _, _E) -> 
    jacob_zero();
jacob_mul(A, P, X, E) when (X < 0) ->
    jacob_mul(A, jacob_negate(P, E), -X, E);
jacob_mul(A, P, 1, E) -> jacob_add(A, P, E);
jacob_mul(A, P, X, E) 
  when ((X rem 2) == 0) -> 
    jacob_mul(A, jacob_double(P, E),
              X div 2, E);
jacob_mul(A, P, X, E) -> 
    jacob_mul(jacob_add(P, A, E),
              P, X-1, E).

div_nearest(A, Base) ->
    (A + (Base div 2)) div Base.

split_scalar_endo(K, E) ->
    Base = field_prime(E),
    %A1 = hex_to_int("3086D221A7D46BCDE86C90E49284EB15"),
    %B1 = -hex_to_int("E4437ED6010E88286F547FA90ABFE4C3"),
    %A2 = hex_to_int("114CA50F7A8E2F3F657C1108D9D44CFD8"),
    A1 = 64502973549206556628585045361533709077,
    B1 = -303414439467246543595250775667605759171,
    A2 = 367917413016453100223835821029139468248,
    %io:fwrite({A1, B1, A2}),
    B2 = A1,
    C1 = div_nearest(ff:mul(B2, K, Base), Base),
    C2 = div_nearest(ff:neg(ff:mul(B1, K, Base), Base), Base),
    K1 = ff:sub(
           K, ff:add(
                ff:mul(C1, A1, Base),
                ff:mul(C2, A2, Base),
                Base
               ), Base),
    K2 = ff:sub(ff:neg(ff:mul(C1, B1, Base), Base),
                ff:mul(C2, B2, Base), Base),
    
    K1neg = (K1 > ?pow_2_128),
    K2neg = (K2 > ?pow_2_128),
    K1b = if
              K1neg -> Base - K1;
              true -> K1
          end,
    K2b = if
              K2neg -> Base - K2;
              true -> K2
          end,
    true = (K1b < ?pow_2_128),
    true = (K2b < ?pow_2_128),
    {K1neg, K1b, K2neg, K2b}.

endo_loop(_, 0, K1p, 0, K2p, _) -> 
    {K1p, K2p};
endo_loop(D, K1, K1p, K2, K2p, E) ->
    K1p2 = if
               ((K1 rem 2) == 1) ->
                   jacob_add(K1p, D, E);
               true -> K1p
           end,
    K2p2 = if
               ((K2 rem 2) == 1) ->
                   jacob_add(K2p, D, E);
               true -> K2p
           end,
    D2 = jacob_double(D, E),
    endo_loop(D2, K1 div 2, K1p2, 
                  K2 div 2, K2p2, E).

endo_mul(P, X, E) ->
    Base = field_prime(E),
    {K1neg, K1, K2neg, K2} = 
        split_scalar_endo(X, E),
    {K1b, K2b} = 
        endo_loop(P, K1, jacob_zero(), 
                     K2, jacob_zero(), E),
    K1c = if
              K1neg -> jacob_negate(K1b, E);
              true -> K1b
          end,
    {K2cA, K2cB, K2cC} = 
        if
            K2neg -> jacob_negate(K2b, E);
            true -> K2b
        end,
    K2d = {ff:mul(K2cA, E#curve.e, Base),
           K2cB, K2cC},
    jacob_add(K1c, K2d, E).

%multiplication(infinity, _, _) ->
%    infinity;
multiplication(_P1, 0, _E) ->
    %infinity;
    {0,0};
multiplication(P1, X, E) 
  when ((X rem 2) == 0) ->
    multiplication(
      addition(P1, P1, E),
      X div 2, E);
multiplication(P1, 1, _) -> 
    P1;
multiplication(P1, X, E) ->
    addition(
      P1,
      multiplication(P1, X-1, E),
      E).

hex_digit_to_int("A") -> 10;
hex_digit_to_int("B") -> 11;
hex_digit_to_int("C") -> 12;
hex_digit_to_int("D") -> 13;
hex_digit_to_int("E") -> 14;
hex_digit_to_int("F") -> 15;
hex_digit_to_int(X) -> 
    list_to_integer(X).

hex_to_int(L) ->
    hex_to_int2(L, 0).
hex_to_int2("", A) -> A;
hex_to_int2([H|T], A) -> 
    A2 = (A*16) + hex_digit_to_int([H]),
    hex_to_int2(T, A2).

gen_point(E) ->
    #curve{
           p = P
          } = E,
    <<X0:256>> = crypto:strong_rand_bytes(32),
    X = X0 rem P,
    G = gen_point(E, X),
    case G of
        error -> gen_point(E);
        _ -> G
    end.
            
gen_point(E, X) ->
    %based on the decrompression of bitcoin pubkeys algorithm.
    #curve{
           p = P,
           b = B,
           a = A
          } = E,
    Ysquare = mod(mod(X*mod(X*X, P), P) - (A*X) + B, P),
    Pident = (P+1) div 4,
    Y = basics:rlpow(Ysquare, Pident, P),
    Check = on_curve(A, B, X, Y, P),
    if
        Check -> {X, Y};
        true -> 
            %io:fwrite("failed\n"),
            error
    end.
add_times(_, _, _, 0) -> ok;
add_times(A, B, E, N) -> 
    add_times(A, addition(A, B, E), E, N-1).
jacob_add_times(_, _, _, 0) -> ok;
jacob_add_times(A, B, E, N) -> 
    jacob_add_times(A, jacob_add(A, B, E), E, N-1).
square_times(_, _, 0) -> ok;
square_times(A, E, N) -> 
    square_times(addition(A, A, E), E, N-1).
jacob_square_times(_, _, 0) -> ok;
jacob_square_times(A, E, N) -> 
    jacob_square_times(jacob_double(A, E), E, N-1).

many(_, 0) -> [];
many(X, N) when (N > 0) -> 
    [X|many(X, N-1)].

chunkify(_, _, 0) -> [];
chunkify(R, C, Many) -> 
    [(R rem C)|
     chunkify(R div C, C, Many-1)].

matrix_diagonal_flip([[]|_]) -> [];
matrix_diagonal_flip(M) ->
    Col = lists:map(fun(X) -> hd(X) end, M),
    Tls = lists:map(fun(X) -> tl(X) end, M),
    [Col|matrix_diagonal_flip(Tls)].

bucketify([], BucketsETS, [], E, 
          ManyBuckets) -> 
    %io:fwrite(Buckets),
    %T = tuple_to_list(Buckets),
    T = lists:map(
          fun(N) ->
                  X = ets:lookup(BucketsETS, N),
                  case X of
                      [] -> jacob_zero();
                      [{_, Y}] -> Y
                  end
          end, range(1, ManyBuckets)),
    T2 = lists:reverse(T),
    %io:fwrite("bucketify part 2 \n"),
    bucketify2(tl(T2), hd(T2), hd(T2), E);
bucketify([0|T], BucketsETS, [_|Gs], E, 
          ManyBuckets) ->
    bucketify(T, BucketsETS, Gs, E, 
              ManyBuckets);
bucketify([BucketNumber|T], BucketsETS, 
          [G|Gs], E, ManyBuckets) ->
    %to calculate each T_i.
    %6*G1 + 2*G2 + 5*G3 ... 6th, then 2nd, then 5th buckets.
    %(2^C)-1 buckets in total. 
    %Put a list of the Gs into each bucket.

    BucketETS0 = ets:lookup(BucketsETS, BucketNumber),
    Bucket = 
        case BucketETS0 of
            [] -> jacob_zero();
            [{_, X}] -> X
        end,
    Bucket2 = jacob_add(G, Bucket, E),%todo, instead of adding here, we should build up a list. so we can do efficient addition later with simplified format numbers. this can potentially make it twice as fast. This was tried, and it made it slower. but it still seems possible.
            
    ets:insert(BucketsETS, {BucketNumber, Bucket2}),
    bucketify(T, BucketsETS, Gs, E, 
              ManyBuckets).
bucketify2([], _L, T, _E) -> T;
bucketify2([S|R], L, T, E) -> 
    %for each bucket, sum up the points inside. [S1, S2, S3, ...
    %T_i = S1 + 2*S2 + 3*S3 ... (this is another multi-exponent. a simpler one this time.)
    %compute starting at the end. S7 + (S7 + S6) + (S7 + S6 + S5) ...
    %todo. maybe simplify, multiply, simplify and add? something like that should be faster if there are lots of buckets.
    L2 = jacob_add(S, L, E),
    T2 = jacob_add(L2, T, E),
    bucketify2(R, L2, T2, E).

remove_zero_terms([], [], A, B) ->
    {lists:reverse(A), lists:reverse(B)};
remove_zero_terms([0|R], [_|G], A, B) ->
    remove_zero_terms(R, G, A, B);
remove_zero_terms(R, G, A, B) ->
    remove_zero_terms(
      tl(R), tl(G), [hd(R)|A], [hd(G)|B]).

simple_exponent([], [], _, A) -> A;
simple_exponent([R|RT], [G|GT], E, Acc) -> 
    A2 = jacob_add(Acc, jacob_mul(G, R, E), E),
    simple_exponent(RT, GT, E, A2).
multi_exponent(Rs0, Gs0, E) ->
    %it looks more like multiplication for us, because that is a nice syntax for elliptic point arithmetic.
    %G is elliptic base points.
    %R are 256-bit integers.
    %Result = R1*G1 + R2*G2 + ...
    {Rs1, Gs} = 
        remove_zero_terms(Rs0, Gs0, [], []),
    if
        %length(Rs1) < 17 ->
        %length(Rs1) < 6 ->
        length(Rs1) < 2 ->
            simple_exponent(
              Rs1, Gs, E, jacob_zero());
        true ->
            multi_exponent2(Rs1, Gs, E)
    end.
multi_exponent2([], [], _E) ->
    jacob_zero();
multi_exponent2(Rs, Gs, E) ->
    C0 = floor(math:log(length(Rs))/math:log(2))-2,
    C1 = min(C0, 16),
    C = max(1, C1),
    F = det_pow(2, C),%this is how many buckets we have, and is the constant factor between elements in a bucket.
    %write each integer in R in binary. partition the binaries into chunks of C bits.
    B = 256,
    R_chunks = 
        lists:map(
          fun(R) -> L = chunkify(
                          R, F, 1+(B div C)),
                    lists:reverse(L)
          end, Rs),
    %Now the problem is broken into 256/C instances of multi-exponentiation.
    %each multi-exponentiation has length(Gs) parts. What is different is that instead of the Rs having 256 bits, they only have C bits. each multi-exponentiation makes [T1, T2, T3...]
    %Each T_i is a multi-exponent for a single base point G from Gs.
    Ts = matrix_diagonal_flip(R_chunks),
    %flip the matrix, so now each row has lots of different base points G, but
    %Each row is an instance of a multi-exponential problem, with C-bit exponents, and the same base value. We will bucketify each of these rows.
    Ss = lists:map(
           fun(X) -> 
                   BucketsETS = ets:new(buckets, [set]),%this ETS database has constant access time reading and editing. It is indexed by an integer, from 1 to F.
                   Result = bucketify(X, BucketsETS, Gs, E, F),
                   ets:delete(BucketsETS),
                   Result
           end, Ts),
    %to combine the Ss into the final sum, F is the factor seperating each S.
    % Ss are elliptic points, F is the integer 2^C.
    % S_0*F^0 + S_1*F^1 + S_2*F^2 + ...
    me3(Ss, jacob_zero(), F, E).
me3([H], A, _, E) -> 
    jacob_add(H, A, E);
me3([H|T], A, F, E) -> 
    %maybe do all the multiplications first, then simplify, then do additions. todo
    X = jacob_add(H, A, E),
    X2 = jacob_mul(X, F, E),
    me3(T, X2, F, E).

range(X, X) -> [X];
range(A, B) when A < B -> 
    [A|range(A+1, B)].

mul_test(_, _, 0) -> ok;
mul_test(A, B, N) -> 
    C = ?mul(A, B),
    mul_test(A, C, N-1).
mul_test2(_, _, 0) -> ok;
mul_test2(A, B, N) -> 
    C = 3*B,
    mul_test2(A, B, N-1).
add5_test(_, _, 0) -> ok;
add5_test(A, B, N) -> 
    C = A+B,
    D = ?add_mod(C),
    add5_test(A, D, N-1).
    
add4_test(_, _, 0) -> ok;
add4_test(A, B, N) -> 
    D = ?neg(B),
    C = ?sub2(A, D),
    %C = ?add2(A, B),
    add4_test(A, C, N-1).
add3_test(_, _, 0) -> ok;
add3_test(A, B, N) -> 
    C = add2(A, B),
    add3_test(A, C, N-1).
add2_test(_, _, 0) -> ok;
add2_test(A, B, N) -> 
    C = add(A, B),
    add2_test(A, C, N-1).
add_test(_, _, 0) -> ok;
add_test(A, B, N) -> 
    C = ?add(A, B),
    add_test(A, C, N-1).
sub4_test(_, _, 0) -> ok;
sub4_test(A, B, N) -> 
    C = ?sub2(B, A),
    sub4_test(A, C, N-1).
sub_test(_, _, 0) -> ok;
sub_test(A, B, N) -> 
    C = ?sub(B, A),
    sub_test(A, C, N-1).
empty_test(_, _, 0) ->  ok;
empty_test(A, B, N) -> 
    empty(A, B),
    empty_test(0, 0, N-1).


test(1) ->
    %testing to see if a random number can be used to make a generator of the group.
    E = make(),
    gen_point(E);
test(2) ->
    E = make(),
    G = gen_point(E),
    T1 = erlang:timestamp(),
    add_times(G, G, E, 500000),
    T2 = erlang:timestamp(),%23 seconds for 1/2 million.
    timer:now_diff(T2, T1);
test(3) ->
    E = make(),
    G = gen_point(E),
    T1 = erlang:timestamp(),
    square_times(G, E, 500000),
    T2 = erlang:timestamp(),%24 seconds for 1/2 million.
    timer:now_diff(T2, T1);
test(4) ->
    %testing the new addition formula.
    E = make(),
    G = gen_point(E),
    %G = {360, ff:sub(0, 360, Base)},
    Gj = to_jacob(G),
    G = to_affine(Gj),
    G2 = addition(G, G, E),
    G3 = addition(G2, G, E),
    Gj2 = jacob_double(Gj, E), 
    Gj3 = jacob_add(Gj2, Gj, E), 
    G2 = to_affine(Gj2),
    G3 = to_affine(Gj3),
    success;
test(5) ->
    E = make(),
    G = gen_point(E),
    Gj = to_jacob(G),
    T1 = erlang:timestamp(),
    jacob_square_times(Gj, E, 500000),
    T2 = erlang:timestamp(),%4 seconds for 1/2 million.
    %6x improvement
    timer:now_diff(T2, T1);
test(6) ->
    E = make(),
    G1 = to_jacob(gen_point(E)),
    G = to_jacob(gen_point(E)),
    T1 = erlang:timestamp(),
    jacob_add_times(G1, G, E, 500000),
    T2 = erlang:timestamp(),%6 seconds for 1/2 million.
    %4x improvement
    timer:now_diff(T2, T1);
test(7) ->
    E = make(),
    G = to_jacob(gen_point(E)),
    GN = jacob_negate(G, E),
    jacob_equal(
      G,
      jacob_add(
        G, jacob_add(G, GN, E), E),
      E);
test(8) ->
    E = make(),
    G2 = gen_point(E),
    G = to_jacob(G2),
    Z = jacob_add(G, jacob_negate(G, E), E),
    {
      Z,
      jacob_zero(),
      jacob_equal(Z, jacob_zero(), E),
      jacob_equal(G, G, E),
      jacob_equal(jacob_add(Z, G, E), G, E),
      to_affine(jacob_mul(G, 1000000000000, E)),
      to_affine(endo_mul(G, 1000000000000, E)),
      multiplication(G2, 1000000000000, E)};
test(9) ->
    E = make(),
    G2 = gen_point(E),
    G = to_jacob(G2),
    Base = field_prime(E),
    P = ff:inverse(ff:neg(1000000000000000, Base), Base),
    Many = many(0, 50),
    T1 = erlang:timestamp(),
    io:fwrite("normal multiplication \n"),
    lists:map(fun(_) ->
                      multiplication(G2, P, E)
              end, Many),
    T2 = erlang:timestamp(),
    io:fwrite("jacob multiplication \n"),
    lists:map(fun(_) ->
                      jacob_mul(G, P, E)
              end, Many),
    T3 = erlang:timestamp(),
    io:fwrite("endo multiplication \n"),
    lists:map(fun(_) ->
                      endo_mul(G, P, E)
              end, Many),
    T4 = erlang:timestamp(),
    D1 = timer:now_diff(T2, T1),
    D2 = timer:now_diff(T3, T2),
    D3 = timer:now_diff(T4, T3),
    {D1, D2, D3};
test(10) ->
    %multi exponent test
    E = make(),
    Base = field_prime(E),
    Rs = [ff:neg(1, Base),
         ff:neg(2, Base),
         ff:neg(3, Base),
         ff:neg(4, Base),
         ff:neg(5, Base),
         ff:neg(6, Base)],
    %Rs = [1, 0, 1, 2],
    Gs = lists:map(
      fun(_) ->
              to_jacob(gen_point(E))
      end, many(1, length(Rs))),
    Ps = lists:zipwith(
           fun(R, G) -> jacob_mul(G, R, E) end,
           Rs, Gs),
    true = jacob_equal(
             lists:foldl(
               fun(A, B) -> jacob_add(A, B, E) end,
               jacob_zero(), Ps),
             multi_exponent(Rs, Gs, E),
             E),
    success;
test(11) ->
    %tests multi-exponent
    E = make(),
    Base = field_prime(E),
    T_256 = det_pow(2, 256),
    Many = 100000,
    %Many = 50000,%10 is best
    %Many = 20000,%10 is best. 2 below estimate.
    %Many = 2000,%8 is best.
    Rs = lists:map(fun(_) ->
                           rand:uniform(T_256) rem Base
                   end, many(1, Many)),
    G0 = to_jacob(gen_point(E)),
    Gs = lists:map(
           fun(_) ->
                   G0
                   %to_jacob(gen_point(E))
           end, many(1, length(Rs))),
    
    
    T1 = erlang:timestamp(),
    %Ps0 = lists:zipwith(
    %       fun(R, G) -> jacob_mul(G, R, E) end,
    %       Rs, Gs),
    %Ps = simplify_Zs_batch(Ps0),
    %Result = 
    %    lists:foldl(
    %      fun(A, B) -> jacob_add(A, B, E) end,
    %      jacob_zero(), Ps),
    T2 = erlang:timestamp(),
    Result2 = multi_exponent(Rs, Gs, E),
    T3 = erlang:timestamp(),
    to_affine(Result2),
    T4 = erlang:timestamp(),
    %true = jacob_equal(Result, Result2, E),
    {{naive_version, timer:now_diff(T2, T1) div Many},
     {fast_version, timer:now_diff(T3, T2) div Many},
     {compress_result, timer:now_diff(T4, T3) div Many}};
test(12) ->
    %test invert_batch
    E = make(),
    Base = field_prime(E),
    V = [1,2,3,4,5,6],
    %IV = invert_batch(V, Base),
    %V = invert_batch(IV, Base),
    IV = ff:batch_inverse(V, Base),
    V = ff:batch_inverse(IV, Base),
    IV = lists:map(fun(X) -> basics:inverse(X, Base) end, V),
    success;
test(13) ->
    E = make(),
    J = to_jacob(gen_point(E)),
    C = compress(J),
    J = decompress(C),
    %success.
    {C, J};
test(14) ->
    %jacobian with z=1 speed comparison.
    E = make(),
    G = gen_point(E),
    G2 = gen_point(E),
    Many = 1000,
    Gs = many(G, Many),
    G2s = many(G2, Many),
    J = to_jacob(G),
    J2 = to_jacob(G2),
    %Gs = many(G, Many),
    Js = many(J, Many),
    J2s = many(J2, Many),
    K = jacob_add(J, J2, E),
    K2 = jacob_add(J, K, E),
    Ks = many(K, Many),
    K2s = many(K2, Many),

    T1 = erlang:timestamp(),
    %this version is like twice as fast.
    lists:zipwith(
      fun(A, B) -> jacob_add(A, B, E) end,
      Js, J2s),
    T2 = erlang:timestamp(),
    lists:zipwith(
      fun(A, B) -> jacob_add(A, B, E) end,
      Ks, K2s),
    T3 = erlang:timestamp(),
    lists:zipwith(
      fun(A, B) -> jacob_add(A, B, E) end,
      Js, K2s),
    T4 = erlang:timestamp(),
    lists:map(fun(A) -> jacob_double(A, E) end,
              Js),
    T5 = erlang:timestamp(),
    lists:map(fun(A) -> jacob_double(A, E) end,
              Ks),
    T6 = erlang:timestamp(),
    lists:map(fun(A) -> addition(A, A, E) end,
              Gs),
    T7 = erlang:timestamp(),
    lists:zipwith(fun(A, B) -> 
                          addition(A, B, E) end,
              Gs, G2s),
    T8 = erlang:timestamp(),
    
    {{affine_double, timer:now_diff(T7, T6)},
     {affine_add, timer:now_diff(T8, T7)},
      {add_simple, timer:now_diff(T2, T1)},%0.006
     {add_half, timer:now_diff(T4, T3)},%0.01
     {add_full, timer:now_diff(T3, T2)},%0.014
     {double_simple, timer:now_diff(T5, T4)},%0.005
     {double_full, timer:now_diff(T6, T5)}%0.005
    };
test(15) ->
    %finite field multiplication test
    <<X:256>> = crypto:strong_rand_bytes(32),
    %<<X:256>> = <<(-1):256>>,
    Many = 500000,
    T1 = erlang:timestamp(),
    %mul_test(X, X, Many),%0.51
    mul_test2(X, X, Many),%0.08
    %add_test(X, X, Many),%0.13
    %add2_test(X, X, Many),%0.11
    %add3_test(X, X, Many),%0.14
    %add4_test(X, X, Many),%0.12
    %add5_test(X, X, Many),%0.095
    %sub_test(X, X, Many),%0.16
    %sub2_test(X, X, Many),%0.12
    %sub3_test(X, X, Many),%0.12
    %sub4_test(X, X, Many),%0.075
    %empty_test(X, X, Many),%0.02
    T2 = erlang:timestamp(),
    timer:now_diff(T2, T1)/Many.
    

    
    

