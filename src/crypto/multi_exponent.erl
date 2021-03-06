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

simple_exponent([], [], A) -> A;
simple_exponent(
  [R|RT], %256 bit numbers
  [G|GT], %encoded eniels points
  Acc) -> %encoded point
    %e_add(extended, eniels)
    %e_mul_long(eniels, exponent)%exponent is a 256 bit little endian number in binary.
    A2 = fq:e_add(fq:e_mul2(G, R), Acc),
    %A2 = fq:e_add(fq:e_mul_long(G, (R)), Acc2),
    simple_exponent(RT, GT, A2).

doit(
  Rs0, %256 bit numbers
  Gs0 %encoded eniels points
 ) ->
    {Rs1, Gs} = 
        remove_zero_terms(Rs0, Gs0, [], []),
    if
        length(Rs1) < 2 ->
        %true ->
            simple_exponent(
              Rs1, Gs, fq:e_zero());
              %Rs0, Gs0, fq:e_zero());
        true ->
            multi_exponent2(Rs1, Gs)
    end.
bucketify([], BucketsETS, [], ManyBuckets) -> 
    %io:fwrite(Buckets),
    %T = tuple_to_list(Buckets),
    T = lists:map(
          fun(N) ->
                  X = ets:lookup(BucketsETS, N),
                  case X of
                      [] -> fq:e_zero();
                      [{_, Y}] -> Y
                  end
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
            [] -> 
                case G of
                    <<_:(256*5)>> -> G;
                    _ ->
                        fq:extended_niels2extended(G)
                end;
            %[] -> G;
            [{_, X}] -> fq:e_add(X, G)
        end,

%todo, instead of adding here, we should build up a list. so we can do efficient addition later with simplified format numbers. this can potentially make it twice as fast. This was tried, and it made it slower. but it still seems possible.
            
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
    %L2 = jacob_add(S, L, E),
    %B = fq:is_zero(S),
    %B2 = fq:is_zero(L),
    L2 = fq:e_add(L, S),
    T2 = fq:e_add(L2, T),
    bucketify2(R, L2, T2).



multi_exponent2([], []) ->
    fq:e_zero();
multi_exponent2(Rs0, Gs) 
  when is_binary(hd(Rs0)) ->
    Rs = lists:map(fun(X) -> fr:decode(X) end, 
                   Rs0),
    multi_exponent2(Rs, Gs);
multi_exponent2(Rs, Gs) ->
    %io:fwrite({Rs}),
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
                   Result
           end, Ts),
    me3(Ss, fq:e_zero(), 
        %fr:reverse_bytes(<<F:256>>)).
        fr:encode(F)).
me3([H], A, _) -> 
    fq:e_add(H, A);
me3([H|T], A, F) -> 
    X = fq:e_add(A, H),
    X2 = fq:e_mul2(X, F),
    me3(T, X2, F).


test(0) ->
    G = ipa2:gen_point(0),
    EG = fq:extended_niels2extended(G),
     A = fq:e_add(EG, G),
     A2 = fq:e_mul2(G, fr:encode(2)),
    B = fq:e_add(A, G),
     B2 = fq:e_mul2(G, fr:encode(3)),
    {
      fq:eq(EG, 
           multi_exponent2([fr:encode(1)], [G])),
      fq:eq(EG, 
           multi_exponent2(
             [fr:encode(1), fr:encode(0)], 
             [G, G])),
     fq:eq(multi_exponent2(
              [fr:encode(1), fr:encode(1)], 
              [G, G]),
            fq:e_mul2(G, fr:encode(2))),
     fq:eq(multi_exponent2([fr:encode(2)], 
                 [G]),
            fq:e_mul2(G, fr:encode(2))),
      fq:eq(multi_exponent2(
               [fr:encode(1), fr:encode(1)], 
               [G, G]), 
            fq:e_mul2(G, fr:encode(2))),
      fq:eq(multi_exponent2(
               [fr:encode(2)], 
               [G]), 
             fq:e_mul2(G, fr:encode(2))),
      fq:eq(multi_exponent2(
               [fr:encode(4)], 
               [G]), 
             fq:e_mul2(G, fr:encode(4))),
      fq:eq(doit(
               [fr:encode(1), fr:encode(4)], 
               [G, G]), 
             fq:e_mul2(G, fr:encode(5)))
     %doit([fr:encode(2)], [G]),
     %fq:e_mul1(G, fr:reverse_bytes(<<2:256>>)),
     %A2, B2
    % fq:eq(A, A2),
    % fq:eq(B, B2),
    % fq:eq(fq:e_double(B), 
    %        fq:e_mul2(G, fr:encode(6)))
     %doit([fr:encode(1), fr:encode(1)], [G, G])
    };
test(1) ->
    %testing bucketify3. (S7*7 + S6*6 + S5*5 + ...)
    ENiels = ipa2:gen_point(0),
    Extended = fq:extended_niels2extended(ENiels),
    Zero = fq:e_zero(),
    NielsZero = fq:extended2extended_niels(Zero),
    L = [Extended, Zero],%[S2, S1]
    fq:eq(bucketify3([Extended, Zero]),
           fq:e_mul2(ENiels, fr:encode(2))
          );
test(2) ->
    %testing addition orders
    ENiels1 = ipa2:gen_point(0),
    ENiels2 = ipa2:gen_point(0),
    ZeroNiels = fq:extended2extended_niels(fq:e_zero()),
    Extended1 = 
        fq:extended_niels2extended(ENiels1),
    Extended2 = 
        fq:extended_niels2extended(ENiels2),
    ZeroPlus = 
      fq:e_add(fq:e_zero(), 
                ZeroNiels),
    ZeroMul = 
        fq:e_mul2(ZeroNiels,
                   fr:encode(27)),
    
    {
      % a + b = b + a
      fq:eq(fq:e_add(Extended1, ENiels2),
            fq:e_add(Extended2, ENiels1)),
     % 0 + 0 = 0
     fq:eq(fq:e_zero(), 
            fq:e_add(fq:e_zero(), 
                      ZeroNiels)),
     % 0 * 27 = 0
     fq:eq(fq:e_zero(), 
            fq:e_mul2(ZeroNiels,
                       fr:encode(27))),
      %can niels encode the default version of zero.
      fq:eq(fq:e_zero(),
             fq:extended_niels2extended(fq:extended2extended_niels(fq:e_zero()))),
      %cannot niel encode other versions of zero.
      fq:is_zero(ZeroPlus),
      fq:is_zero(
             fq:extended_niels2extended(fq:extended2extended_niels(ZeroPlus)))
    };
test(3) ->
    G = ipa2:gen_point(0),
    EG = fq:extended_niels2extended(G),
    F = fr:encode(4),
    R = multi_exponent2([F], 
                        [G]),
    {
      fq:e_double(fq:e_double(EG)),
      fq:e_mul2(G, F),
      fq:e_mul2(fq:extended2extended_niels(EG), 
                 F),
      R,
      fq:eq(R,
             fq:e_mul2(G, F))
    };
test(4) ->
    N = ipa2:gen_point(0),
    E0 = fq:extended_niels2extended(N),
    Nb = fq:extended2extended_niels(E0),
    E0b = fq:extended_niels2extended(Nb),

    E = fq:e_mul2(N, fr:encode(2)),
    N2 = fq:extended2extended_niels(E),
    Eb = fq:extended_niels2extended(N2),
    N2b = fq:extended2extended_niels(Eb),

    E2 = fq:e_mul2(N2, fr:encode(2)),
    E4 = fq:e_mul2(N, fr:encode(4)),
    DD = fq:e_double(fq:e_double(E0)),



    {
      fq:eq(E0, E0b),%false.
      fq:eq(E, Eb),%false.
      fq:eq(E, fq:e_double(E0)),%true

      fq:eq(E2, E4),%false
      fq:eq(E2, DD),%false
      fq:eq(DD, E4)%true
    };
test(5) ->
    G = ipa2:gen_point(0),
    fq:eq(multi_exponent2(
             [fr:encode(4)], 
             [G]), 
           fq:e_mul2(G, fr:encode(4)));
test(6) ->
    G = ipa2:gen_point(0),
    H = ipa2:gen_point(0),
    B = [fr:encode(4), fr:encode(5)],
    fq:eq(multi_exponent2(B, [G, H]),
           simple_exponent(B, [G, H], 
                          fq:e_zero())).
    

