-module(precomputed_multi_exponent).
-export([
         parameters/2,
         doit/2
        ]).

range(X, X) -> [X];
range(X, Y) when (X < Y) -> 
    [X|range(X+1, Y)].
multi_exponent_parameters2(_, X, 0) -> [X];
multi_exponent_parameters2(Base, X, Times) ->
    N = ed:e_add(X, Base),
    [X|multi_exponent_parameters2(
         Base, 
         N,
         Times - 1)].
det_pow(0, _) -> 0;
det_pow(_, 0) -> 1;
det_pow(A, 1) -> A;
det_pow(A, N) when ((N rem 2) == 0) -> 
    det_pow(A*A, N div 2);
det_pow(A, N) -> 
    A*det_pow(A, N-1).
parameters(C, Gs) ->
    io:fwrite("calculating 256 multi exponent parameters\n"),
    F = det_pow(2, C),
    L = lists:zipwith(
          fun(G, R) ->
                  String = "ME # " ++ integer_to_list(R) ++ "\n",
                  X = multi_exponent_parameters2(
                        G, ed:extended_zero(), F),
                  X3 = ed:normalize(X),
                  list_to_tuple(X3)
          end, Gs, range(1, length(Gs))),
    io:fwrite("multi exponent parameters done\n"),
    list_to_tuple(L).
batch_chunkify(_Rs, _, 0) -> [];
batch_chunkify(Rs, F, Lim) -> 
    N = lists:map(fun(R) ->
                          R rem F
                  end, Rs),
    Rs2 = lists:map(fun(R) ->
                            R div F
                    end, Rs),
    [N|batch_chunkify(Rs2, F, Lim-1)].
    
get_domain([], [], [], D, R, M) ->
    {lists:reverse(D),
     lists:reverse(R),
     lists:reverse(M)};
get_domain([_D|DT], [0|RT], [_M|MT], Ds, Rs, Ms) ->
    get_domain(DT, RT, MT, Ds, Rs, Ms);
get_domain([_D|DT], [<<0:256>>|RT], [_M|MT], 
           Ds, Rs, Ms) ->
    get_domain(DT, RT, MT, Ds, Rs, Ms);
get_domain([D|DT], [R|RT], [M|MT], Ds, Rs, Ms) ->
    get_domain(DT, RT, MT, [D|Ds], [R|Rs], [M|Ms]).

doit(Rs0, MEP) ->
    %Rs0 is a list of fr encoded values.
    %we want to do part of the bucket algorithm, but since the generator points are all known ahead of time, we want to use precalculated values where possible.
    %n = 2, C = 10 -> 128*2/8 -> 32.
    Domain0 = parameters2:domain(),
    Mepl0 = tuple_to_list(MEP),
    {Domain, Rs, Mepl} = 
        get_domain(% 0.4%
          Domain0, Rs0, Mepl0, [], [], []),
    %io:fwrite(Rs),
    C = 8,
    F = det_pow(2, C),
    B = 256,
    %bitcoin has 19 leading zeros in hexidecimal format. around 80 bits per block.
    Lim = ceil(B / C),

    % 14% of storage
    Ts = batch_chunkify(
           fr:decode(Rs), F, Lim),
    %32 = length(Ts),
    %256 = length(Rs0),
    %256 = length(Rs),
    %true = (length(Domain) == length(Rs)),
    %256 = length(Mepl),
    %  4.5% of storage
    %EZero = fq:e_zero(),
    EZero = ed:extended_zero(),
    Ss = lists:map(
           fun(T) ->
                   if
                       (length(T) == length(Mepl)) ->
                           pme22(T, Mepl, EZero);
                       true ->
                           io:fwrite({T, Ts})
                   end
           end, Ts),

    % 3.5% of storage
    Result = multi_exponent:me3(
               lists:reverse(Ss), 
               EZero, 
               %fr:encode(F)),%  5%
               <<F:256/little>>),%  5%
    if
        (Result == error) ->
            io:fwrite({Ss, EZero, F});
        true -> ok
    end,
    Result.
                      
    %Now the problem has been broken into 256/C instances of multi-exponentiation.
    %each multi-exponentiation has length(Gs) parts. What is different is that instead of the exponents having 256 bits, they only have C bits. each multi-exponentiation makes [T1, T2, T3...]
    %Each row is an instance of a multi-exponential problem, with C-bit exponents. We will use the precalculated parameters for this.
%io:fwrite(Ts),

pme22([], [], Acc) -> Acc;
pme22([0|T], [_|D], Acc) -> 
    pme22(T, D, Acc);
pme22([Power|T], [H|MEP], Acc) -> 
    X = element(Power+1, H),
    %Acc2 = fq:e_add(X, Acc),
    Acc2 = ed:e_add(X, Acc),
    pme22(T, MEP, Acc2);
pme22(A, B, C) -> 
    io:fwrite("store2 pme22 failure\n"),
    io:fwrite({length(A), length(B), C}),
    io:fwrite("\n").
    
    

many(_, 0) -> [];
many(A, N) when N > 0 -> 
    [A|many(A, N-1)].

test(1) ->
    verkle_app:start(normal, []),
    R1 = ([1|many(0, 255)]),
    R2 = ([0,1|many(0, 254)]),
    R3 = ([2|many(0, 255)]),
    R4 = ([0,2|many(0, 254)]),
    %R5 = many(fr:prime()-1, 256),
    R5 = ([fr:prime()-1|many(0, 255)]),
    R = R5,
    {Gs, _, _} = parameters2:read(),
    Old = multi_exponent:doit(fr:encode(R), Gs),
    MEP = parameters2:multi_exp(),
    New = doit(
            fr:encode(R), MEP), 
    G = hd(Gs),
    Other = ed:e_mul2(G, fr:encode(fr:prime()-1)),
    %Saved0 = element(2, element(1, MEP)),
%    Saved0 = element(2, element(2, MEP)),
%    Saved = secp256k1:to_affine(secp256k1:jacob_add(Saved0, Saved0, ?p#p.e)),
    %Saved1 = element(2, element(2, MEP)),
    %io:fwrite({Old, New, Saved0}),
    %fq:eq(Old, New);
    true = ed:e_eq(Old, New),
    true = ed:e_eq(Old, Other),
    true = ed:e_eq(New, Other),
    success;
%    true = ed:e_eq(Old, New),
%    success;
test(2) ->
    io:fwrite("ftrace of precomputed multi exponent\n"),
    %multi exponent precompute speed comparison.
    %verkle_app:start(normal, []),
    Many = 20,
    Rs = lists:map(fun(_) ->
                           <<X:256>> = crypto:strong_rand_bytes(32),
                           fr:encode(X)
                   end, range(1, 256)),
    MEP = parameters2:multi_exp(),
    T1 = erlang:timestamp(),
    fprof:trace(start),
    lists:map(fun(_) ->
                      doit(
                        Rs, MEP)%72000
              end, range(1, Many)),
    fprof:trace(stop),
%fprof:analyse().
    T2 = erlang:timestamp(),
%    lists:map(fun(_) ->
%                      secp256k1:multi_exponent(
%                        Rs, Gs, E)%125000
%              end, range(1, Many)),
    T3 = erlang:timestamp(),
    {timer:now_diff(T2, T1)/Many,
     timer:now_diff(T3, T2)/Many},
    fprof:profile(file, "fprof.trace"),
    fprof:analyse().
    

    

    
