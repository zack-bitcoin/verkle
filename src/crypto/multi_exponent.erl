-module(multi_exponent).
-export([doit/2, me3/3, simple_exponent/3,
         test/1]).

det_pow(0, _) -> 0;
det_pow(_, 0) -> 1;
det_pow(A, 1) -> A;
det_pow(A, N) when ((N rem 2) == 0) -> 
    det_pow(A*A, N div 2);
det_pow(A, N) when N > 1 -> 
    A*det_pow(A, N-1).

%break a 256-bit little endian number into Many chunks.
%chunkify(R, C, Many) ->
%    chunkify2(R, C, Many). 
chunkify(_, _, 0) -> [];
chunkify(R, C, Many) -> 
    [(R rem C)|
     chunkify(R div C, C, Many-1)].

matrix_diagonal_flip([[]|_]) -> [];
matrix_diagonal_flip(M) ->
    Col = lists:map(fun(X) -> hd(X) end, M),
    Tls = lists:map(fun(X) -> tl(X) end, M),
    [Col|matrix_diagonal_flip(Tls)].

remove_zero_terms([], [], A, B) ->
    {lists:reverse(A), lists:reverse(B)};
%remove_zero_terms([0|R], [_|G], A, B) ->
%    remove_zero_terms(R, G, A, B);
remove_zero_terms([<<0:256>>|R], [_|G], A, B) ->
    remove_zero_terms(R, G, A, B);
remove_zero_terms(R, G, A, B) ->
    remove_zero_terms(
      tl(R), tl(G), [hd(R)|A], [hd(G)|B]).
range(X, X) -> [X];
range(A, B) when A < B -> 
    [A|range(A+1, B)].

simple_exponent(A, B) -> 
    simple_exponent(A, B, ed:extended_zero()).
simple_exponent([], [], A) -> A;
simple_exponent(
  [R|RT], %256 bit montgomery encoded numbers
  [G|GT], %encoded eniels points
  Acc) -> %encoded point
    %e_add(extended, eniels)
    %e_mul_long(eniels, exponent)%exponent is a 256 bit little endian number in binary.
    A2 = ed:e_add(ed:e_mul2(G, R), Acc),
    %A2 = fq:e_add(fq:e_mul2(G, R), Acc),
    %A2 = fq:e_add(fq:e_mul_long(G, (R)), Acc2),
    simple_exponent(RT, GT, A2).

doit(
  Rs0, %256 bit mongomery encoded numbers
  Gs0 %extended point
 ) ->
    {Rs1, Gs} = 
        remove_zero_terms(Rs0, Gs0, [], []),
    if
        length(Rs1) < 2 ->
            simple_exponent(
              Rs1, Gs, ed:extended_zero());
        true ->
            multi_exponent2(Rs1, Gs)
    end.
bucketify([], BucketsETS, [], ManyBuckets) -> 
    %io:fwrite(Buckets),
    %T = tuple_to_list(Buckets),
    T = lists:map(
          fun(N) ->
                  X = ets:lookup(BucketsETS, N),
                  Z = case X of
                          [] -> ed:extended_zero();
                          [{_, Y}] -> Y
                      end,
                  false = (Z == error),
                  Z
          end, range(1, ManyBuckets)),
    T2 = lists:reverse(T),
    %T2 = T,
    %io:fwrite("bucketify part 2 \n"),
    %io:fwrite({size(hd(T2)), size(hd(tl(T2)))}),
    bucketify3(T2);
%bucketify2(tl(T2), hd(T2), hd(T2));
bucketify([0|T], BucketsETS, [_|Gs], 
          ManyBuckets) ->
    bucketify(T, BucketsETS, Gs, ManyBuckets);
bucketify([BucketNumber|T], BucketsETS, 
          [G|Gs], ManyBuckets) ->
    %to calculate each T_i.
    %6*G1 + 2*G2 + 5*G3 ... 6th, then 2nd, then 5th buckets.
    %(2^C)-1 buckets in total. 
    %Put a list of the Gs into each bucket.

    BucketETS0 = ets:lookup(
                   BucketsETS, BucketNumber),
    Bucket2 = 
        case BucketETS0 of
            [] ->  G;
%                case G of
%                    <<_:(256*5)>> -> G;
%                    _ ->
                        %fq:extended_niels2extended(G)
%                        fq:extended_niels2extended(G)
%                end;
            %[] -> G;
            %[{_, X}] -> fq:e_add(X, G)
            [{_, X}] -> 
                ed:e_add(X, G)
        end,

%todo, instead of adding here, we should build up a list. so we can do efficient addition later with simplified format numbers. this can potentially make it twice as fast. This was tried, and it made it slower. but it still seems possible.
            
    if
        (Bucket2 == error) ->
            {_, X2} = hd(BucketETS0),
            io:fwrite({size(X2), size(G),
                      X2, G});
        true -> ok
    end,
    ets:insert(BucketsETS, {BucketNumber, Bucket2}),
    bucketify(T, BucketsETS, Gs, ManyBuckets).
bucketify3(T) ->
    %T is a list of extended points.
    bucketify2(tl(T), hd(T), hd(T)).
bucketify2([], _L, T) -> T;
bucketify2([S|R], L, T) -> 
    %for each bucket, sum up the points inside. [S7, S6, S5, ...
    %T_i = S1 + 2*S2 + 3*S3 ... (this is another multi-exponent. a simpler one this time.)
    %compute starting at the end. S7 + (S7 + S6) + (S7 + S6 + S5) ...
    %todo. maybe simplify, multiply, simplify and add? something like that should be faster if there are lots of buckets.
    L2 = ed:e_add(L, S),
    T2 = ed:e_add(L2, T),
    bucketify2(R, L2, T2).



multi_exponent2([], []) ->
    %fq:e_zero();
    ed:extended_zero();
multi_exponent2(Rs0, Gs) 
  when is_binary(hd(Rs0)) ->
    Rs = lists:map(fun(X) -> fr:decode(X) end, 
                   Rs0),
    multi_exponent2(Rs, Gs);
multi_exponent2(Rs, Gs) ->
%    io:fwrite({Rs, Gs}),
    C0 = floor(math:log(length(Rs))/math:log(2))-2,
    C1 = min(C0, 16),
    C = max(1, C1),%how many bits per chunk
    %C = max(12, C1),%how many bits per chunk
    F = det_pow(2, C),%this is how many buckets we have, and is the constant factor between elements in a bucket.
    %write each integer in R in binary. partition the binaries into chunks of C bits.
    B = 256,
    R_chunks = 
        lists:map(
          fun(R) -> L = chunkify(
                          R, F, 1+(B div C)),
                    lists:reverse(L)
          end, Rs),
    Ts = matrix_diagonal_flip(R_chunks),
    %Now the problem has been broken into 256/C instances of multi-exponentiation.
    %each multi-exponentiation has length(Gs) parts. What is different is that instead of the exponents having 256 bits, they only have C bits. each multi-exponentiation makes [T1, T2, T3...]
    %Each row is an instance of a multi-exponential problem, with C-bit exponents. We will bucketify each of these rows.
    Ss = lists:map(
           fun(X) -> 
                   BucketsETS = 
                       ets:new(buckets, [set]),%this ETS database has constant access time reading and editing. It is indexed by an integer, from 1 to F.
                   Result = 
                       bucketify(X, BucketsETS, 
                                 Gs, F),
                   ets:delete(BucketsETS),
                   false = (error == Result),
                   Result
           end, Ts),
    %me3(Ss, fq:e_zero(), 
    %false = ed:e_eq(ed:extended_zero(), hd(lists:reverse(Ss))),
%    io:fwrite({length(Ss), 
    %true = ed:e_eq(hd(lists:reverse(Ss)), hd(Gs)),
    
    me3(Ss, ed:extended_zero(), 
        %fr:reverse_bytes(<<F:256>>)).
                 <<F:256/little>>).
    %true = ed:e_eq(hd(Gs), Result),
   
%fr:encode(F)).
me3([H], A, _) -> 
    %fq:e_add(H, A);
    %io:fwrite({ed:e_eq(A, ed:extended_zero())}),
    ed:e_add(H, A);
me3([H|T], A, F) -> 
    X = ed:e_add(A, H),
    X2 = ed:e_mul(X, F),
    if
        (X == error) -> io:fwrite({me3, one, A, H});
        (X2 == error) -> io:fwrite({me3, two, X, F});
        true -> ok
    end,
    me3(T, X2, F).


test(0) ->
    success = test(7),
    G = ed:affine2extended(ed:gen_point()),

    %normal multiplication first
    A = ed:e_add(G, G),
    A2 = ed:e_mul2(G, fr:encode(2)),
    true = ed:e_eq(A, A2),
    B = ed:e_add(A, G),
    B2 = ed:e_mul2(G, fr:encode(3)),
    true = ed:e_eq(B, B2),
    Z = 8589934592,
    B3 = ed:e_mul2(G, fr:encode(Z)),
    true = ed:e_eq(
             G, 
             multi_exponent2([fr:encode(1)], [G])),
    true = ed:e_eq(ed:extended_zero(), 
                   multi_exponent2([], [])),
    true = ed:e_eq(ed:extended_zero(), 
                   multi_exponent2([fr:encode(0)],
                                   [G])),
    true = ed:e_eq(
             G, 
             multi_exponent2([fr:encode(1)], [G])),
    true = ed:e_eq(G, 
                   multi_exponent2(
                     [fr:encode(1), fr:encode(0)], 
                     [G, G])),
    true = ed:e_eq(multi_exponent2(
                     [fr:encode(1), fr:encode(1)], 
                     [G, G]),
                   A),
    true = ed:e_eq(multi_exponent2([fr:encode(2)], 
                                   [G]),
                   A),
    true = ed:e_eq(multi_exponent2(
                     [fr:encode(1), fr:encode(1)], 
                     [G, G]), 
                   A),
    true = ed:e_eq(multi_exponent2(
                     [fr:encode(2)], 
                     [G]), 
                   A),
    true = ed:e_eq(multi_exponent2(
                     [fr:encode(4)], 
                     [G]), 
                   ed:e_mul2(G, fr:encode(4))),
    true = ed:e_eq(doit(
                     [fr:encode(1), fr:encode(4)], 
                     [G, G]), 
                   ed:e_mul2(G, fr:encode(5))),
    io:fwrite("32 bytes of zero\n"),
    %Z = basics:rlpow(10, 32, 9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999),
    Z = basics:rlpow(2, 33, 1000000000000000000000000000000000000000),
    Z = 8589934592,
    true = ed:e_eq(simple_exponent(fr:encode([Z, 1, 1]),
                        [G, G, G]),
                   simple_exponent(fr:encode([Z+1, 1]),
                        [G, G])),
    true = ed:e_eq(multi_exponent2(fr:encode([Z, 1, 1]),
                        [G, G, G]),
                   multi_exponent2(fr:encode([Z+1, 1]),
                        [G, G])),
    Big = 3705093086744360691065964547167704750793463218034549685405621849768160725598,
    true = ed:e_eq(
             simple_exponent(fr:encode([Big, 1, 1, 1]), 
                             [G, G, G, G]),
             simple_exponent(fr:encode([Big+3]),
                             [G])),
    true = ed:e_eq(
             multi_exponent2(fr:encode([Big, 1, 1, 1]), 
                             [G, G, G, G]),
             multi_exponent2(fr:encode([Big+3]),
                             [G])),
    success;
test(1) ->
    %testing bucketify3. (S7*7 + S6*6 + S5*5 + ...)
    Extended = ed:affine2extended(ed:gen_point()),
    Zero = ed:extended_zero(),
    true = ed:e_eq(bucketify3([Extended, Zero]),
                   ed:e_mul2(Extended, fr:encode(2))),
    success;
test(3) ->
    G = ed:affine2extended(ed:gen_point()),
    F = fr:encode(4),
    R = multi_exponent2([F], [G]),
    G2 = ed:e_add(G, G),
    G4 = ed:e_add(G2, G2),
    {
      G4,
      ed:e_mul2(G, F),
      R,
      ed:e_eq(R, ed:e_mul2(G, F))
    };
test(5) ->
    G = ed:gen_point(),
    true =ed:e_eq(multi_exponent2(
                    [fr:encode(4)], 
                    [G]), 
                  ed:e_mul2(G, fr:encode(4))),
    success;
test(6) ->
    G = ed:gen_point(),
    H = ed:gen_point(),
    B = [fr:encode(4), fr:encode(5)],
    true = ed:e_eq(multi_exponent2(B, [G, H]),
                   simple_exponent(
                     B, [G, H], 
                     ed:extended_zero())),
    success;
test(7) ->
    %test that using 32 bits of zeros doesn't break elliptic multiplication
    G = ed:gen_point(),

    
    io:fwrite("test 31\n"),
    Z0 = basics:rlpow(2, 31, 9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999),
    B0 = ed:e_mul2(G, fr:encode(Z0)),
    io:fwrite("next mul\n"),
    Bl10 = ed:e_mul2(G, fr:encode(Z0-1)),
    true = ed:e_eq(B0, ed:e_add(Bl10, G)),


    io:fwrite("test 32\n"),
    Z = basics:rlpow(2, 32, 9999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999999),
    B = ed:e_mul2(G, fr:encode(Z)),
    timer:sleep(50),
    io:fwrite("next mul\n"),
    Bl1 = ed:e_mul2(G, fr:encode(Z-1)),
    timer:sleep(50),
    true = ed:e_eq(B, ed:e_add(Bl1, G)),
    success;
test(8) ->
    %elliptic multiplication doesn't break on big numbers.
    G = ed:gen_point(),
    Eb = 328490237808490508376962983701062532245597166313109197768658377164801760055,
    Es = 200990237808490508376962983701062532245597166313109197768658377164801760055,
    %Es = 127990237808490508376962983701062532245597166313109197768658377164801760055,

    Gs = ed:e_mul2(G, fr:encode(Es)),
    Gb = ed:e_mul2(G, fr:encode(Eb)),
    Gd = ed:e_mul2(G, fr:encode(Eb - Es)),
    
    true = ed:e_eq(Gb, ed:e_add(Gs, Gd)),
    success.
    
    
    

    

