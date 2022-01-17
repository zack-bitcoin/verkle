-module(multi_exponent).
-export([doit/2]).

det_pow(0, _) -> 0;
det_pow(_, 0) -> 1;
det_pow(A, 1) -> A;
det_pow(A, N) when ((N rem 2) == 0) -> 
    det_pow(A*A, N div 2);
det_pow(A, N) when N > 1 -> 
    A*det_pow(A, N-1).

%break a 256-bit little endian number into Many chunks.
chunkify(R, C, Many) ->
    chunkify2(R, C, Many). 
chunkify2(_, _, 0) -> [];
chunkify2(R, C, Many) -> 
    [(R rem C)|
     chunkify2(R div C, C, Many-1)].

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

simple_exponent([], [], A) -> A;
simple_exponent(
  [R|RT], %256 bit numbers
  [G|GT], %encoded eniels points
  Acc) -> %encoded point
    %e_add(extended, eniels)
    %e_mul_long(eniels, exponent)%exponent is a 256 bit little endian number in binary.
    Acc2 = fq2:extended2extended_niels(Acc),
    A2 = fq2:e_add(fq2:e_mul_long(G, fq2:reverse_bytes(R)), Acc2),
    simple_exponent(RT, GT, A2).

doit(
  Rs0, %256 bit numbers
  Gs0 %encoded eniels points
 ) ->
    {Rs1, Gs} = 
        remove_zero_terms(Rs0, Gs0, [], []),
    if
        length(Rs1) < 2 ->
            simple_exponent(
              Rs1, Gs, fq2:e_zero());
        true ->
            multi_exponent2(Rs1, Gs)
    end.
bucketify([], BucketsETS, [], 
          ManyBuckets) -> 
    %io:fwrite(Buckets),
    %T = tuple_to_list(Buckets),
    T = lists:map(
          fun(N) ->
                  X = ets:lookup(BucketsETS, N),
                  case X of
                      [] -> fq2:e_zero();
                      [{_, Y}] -> Y
                  end
          end, range(1, ManyBuckets)),
    T2 = lists:reverse(T),
    %io:fwrite("bucketify part 2 \n"),
    %io:fwrite({size(hd(T2)), size(hd(tl(T2)))}),
    bucketify2(tl(T2), hd(T2), hd(T2));
bucketify([0|T], BucketsETS, [_|Gs], 
          ManyBuckets) ->
    bucketify(T, BucketsETS, Gs, ManyBuckets);
bucketify([BucketNumber|T], BucketsETS, 
          [G|Gs], ManyBuckets) ->
    %to calculate each T_i.
    %6*G1 + 2*G2 + 5*G3 ... 6th, then 2nd, then 5th buckets.
    %(2^C)-1 buckets in total. 
    %Put a list of the Gs into each bucket.

    BucketETS0 = ets:lookup(BucketsETS, BucketNumber),
    Bucket = 
        case BucketETS0 of
            [] -> fq2:e_zero();
            [{_, X}] -> X
        end,
    %Bucket2 = jacob_add(G, Bucket, E),
    Bucket2 = fq2:e_add(Bucket, G),
%todo, instead of adding here, we should build up a list. so we can do efficient addition later with simplified format numbers. this can potentially make it twice as fast. This was tried, and it made it slower. but it still seems possible.
            
    ets:insert(BucketsETS, {BucketNumber, Bucket2}),
    bucketify(T, BucketsETS, Gs, ManyBuckets).
bucketify2([], _L, T) -> T;
bucketify2([S|R], L, T) -> 
    %for each bucket, sum up the points inside. [S1, S2, S3, ...
    %T_i = S1 + 2*S2 + 3*S3 ... (this is another multi-exponent. a simpler one this time.)
    %compute starting at the end. S7 + (S7 + S6) + (S7 + S6 + S5) ...
    %todo. maybe simplify, multiply, simplify and add? something like that should be faster if there are lots of buckets.
    %L2 = jacob_add(S, L, E),
    L2 = fq2:e_add(L, fq2:extended2extended_niels(S)),
    %T2 = jacob_add(L2, T, E),
    T2 = fq2:e_add(L2, fq2:extended2extended_niels(T)),
    %io:fwrite({size(L2), size(T), L2, T, T2}),
    bucketify2(R, L2, T2).



multi_exponent2([], []) ->
    fq2:e_zero();
multi_exponent2(Rs, Gs) ->
    %io:fwrite({Rs}),
    C0 = floor(math:log(length(Rs))/math:log(2))-2,
    C1 = min(C0, 16),
    C = max(1, C1),%how many bits per chunk
    F = det_pow(2, C),%this is how many buckets we have, and is the constant factor between elements in a bucket.
    %write each integer in R in binary. partition the binaries into chunks of C bits.
    B = 256,
    R_chunks = 
        lists:map(
          fun(R) -> L = chunkify(
                          fr:decode(R), F, 1+(B div C)),
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
                   Result
           end, Ts),
    %io:fwrite({Ss}),
    me3(Ss, fq2:e_zero(), F).
me3([H], A, _) -> 
    fq2:e_add(H, fq2:extended2extended_niels(A));
me3([H|T], A, F) -> 
    X = fq2:e_add(A, fq2:extended2extended_niels(H)),
    X2 = fq2:e_mul(fq2:extended2extended_niels(X), F),
    me3(T, X2, F).
