-module(multiproof2).
-export([prove/9, verify/4, test/1]).

-define(sanity_checks, false).

%G is the most important calculation of the multiproof.
    %sum i: r^i * (As_i(t)-Y_i)/(t-z_i)
%different parts of the multiproof will be computing this same formula, but from different perspectives. Sometimes using polynomials instead of integers, so that we can change the order that the computation is done in.
% As are the polynomials that have been committed to.
% Z are the locations we are proving in each of those polynomials.
% Y are the values stored in A at locations Z.

%One basic way G gets split up is into G1 and G2.
%G = G1 - G2
%G1 = sum i: r^i * (As_i(t))/(t-z_i)
%G2 = sum i: r^i * (Y_i)/(t-z_i)

%when G1 is expressed as a polynomial of t, we will denote that as polynomial H.


calc_G(R, As, Ys, Zs, Domain, DA) ->
    %polynomial g from dankrad's paper. computed by prover. https://dankradfeist.de/ethereum/2021/06/18/pcs-multiproofs.html
    %sum i: r^i * (As_i(t)-Y_i)/(t-z_i)
    % 1 * (?-3)/(3)
    %todo check
    L = length(Domain),
    DivEAll = case L of
                  256 -> 
                      parameters2:div_e();
                  _ -> poly2:all_div_e_parameters(
                         Domain, DA)
              end,
    DivEAll2 = 0,
    calc_Gb(fr:encode(1), R, As, Ys, Zs,
              Domain, DA, DivEAll, DivEAll2, []).
calc_Gb(_, _, [], [], [], _, _, _, _ ,
          Accumulator) -> Accumulator;
calc_Gb(RA, R, [A|AT], [Y|YT], [Z|ZT], Domain,
          DA, DivEAll, DivEAll2, Accumulator) ->
    X1 = lists:map(fun(C) -> fr:sub(C, Y) end, A),
    P = poly2:div_e(X1, Domain, DA, 
                    Z, DivEAll, DivEAll2),
    X = poly2:mul_scalar(RA, P),
    A2 = poly2:add(X, Accumulator), 
    calc_Gb(fr:mul(RA, R), R, AT, YT, ZT, Domain,
              DA, DivEAll, DivEAll2, A2).

mul_r_powers(_, _, []) -> [];
mul_r_powers(R, A, [C|T]) ->
    [fr:mul(C, A)|
     mul_r_powers(
       R, fr:mul(A, R), T)].

%sum_i:  r^i * y_i / (t - z_i)
%3*((1/3) + (1/3) + (1/3) + (1/3))
%4
calc_G2_2(R, T, Ys, Zs) ->
    %todo. check
    %the second half of calc_G.
    %io:fwrite({fr:decode([R, T, Ys, Zs])}),
    %[1, 5, [3,3,3,3], [2,2,2,2]]
    Divisors = 
        lists:map(fun(Z) -> fr:sub(T, Z) end, Zs),
    %[3,3,3,3]
    IDs = fr:batch_inverse(Divisors),
    RIDs = mul_r_powers(
             R, fr:encode(1), IDs),
    L1 = lists:zipwith(
          fun(Y, I) -> fr:mul(Y, I) end,
          Ys, RIDs),
    Result = fr:add_all(L1),
    %io:fwrite({fr:decode([Divisors, IDs, L1, Result])}),
    %[[3,3,3,3], [1/3, 1/3...], [1,1,1,1], 4]
    {RIDs, Result}.

%sum_i: As_i(X) * (r^i)/(t - z_i)
calc_H(R, T, As, Zs) ->
    %H is a polynomial such that if you plug T in to it, the result is G1.
    Divisors = 
        lists:map(fun(Z) -> fr:sub(T, Z) end, Zs),
    IDs = fr:batch_inverse(Divisors),
    RIDs = mul_r_powers(R, fr:encode(1), IDs),
    calc_H2(RIDs, As, []).
calc_H2([], [], Accumulator) -> Accumulator;
calc_H2([H|T], [A|AT], Acc) -> 
    X = poly2:mul_scalar(H, A),
    Acc2 = poly2:add(X, Acc),
    calc_H2(T, AT, Acc2).

calc_R([], [], [], B) -> 
    %deterministically generated random number. 
    <<R:256>> = hash:doit(B),
    fr:encode(R rem fr:prime());
calc_R([<<C1:256, C2:256>>|CT], 
       [<<Z:256>>|ZT], [<<Y:256>>|YT], B) -> 
    B2 = <<B/binary, 
           Z:256, 
           Y:256, 
           C1:256, 
           C2:256>>,
    calc_R(CT, ZT, YT, B2).

calc_T(<<C1:256, C2:256>>, <<R:256>>) ->
    %deterministically generated random number. 
    B = <<C1:256, C2:256, R:256>>,
    <<R2:256>> = hash:doit(B),
    fr:encode(R2 rem fr:prime()).

%-define(deco(X), secp256k1:decompress(X)).
%-define(comp(X), secp256k1:compress(X)).
%compress({C1, Csa, {AG, AB, Csb, AN, BN}}) ->
%    Cs0 = Csa ++ Csb,
%    [AG2, C2|Cs1] = ?comp([AG, C1|Cs0]),
%    {Csa2, Csb2} = lists:split(length(Csa), Cs1),
%    {C2, Csa2, {AG2, AB, Csb2, AN, BN}}.

%decompress({C2, Csa2, Cipa}) ->
%    Csa = lists:map(fun(X) -> ?deco(X) end, Csa2),
%    Ipa = ipa:decompress(Cipa),
%    {?deco(C2), Csa, Ipa}.
    
    
prove(As, %committed data
      Zs, %the slot in each commit we are reading from. A list as long as As. Made up of elements that are in the domain.
      Commits_e, Gs, Hs, Q, DA, PA, Domain) ->

    %todo. instead of accepting the entire list of As, we should receive a tree structure that allows us to stream the As. that way the memory requirement doesn't get so big.
    io:fwrite("multiprove Ys from As \n"),
    benchmark:now(),
    Ys0 = lists:zipwith(
           fun(F, Z) ->
                   %io:fwrite({size(Z), 
                   %           length(F), 
                   %           size(hd(Domain)), 
                   %           Z, F, hd(Domain)}),
                   poly2:eval_e(Z, F, Domain)
           end, As, Zs),%this should be streamed with calculating the As.
    %io:fwrite({fr:decode([Ys0, As, Zs])}),
    %Ys [3,3,3,3]
    %As [[4,3,2,1],...]
    %Zs [2,2,2,2]
    %io:fwrite(lists:map(fun(<<X:256>>) -> X end, Ys0)),
    %io:fwrite(fr:decode(Ys0)),
    %io:fwrite(Ys0),
    Ys =Ys0,
    io:fwrite("multiprove calc random R\n"),% 4%
    benchmark:now(),
    AffineCommits = 
        %fq:to_affine_batch(
        ed:extended2affine_batch(
          Commits_e),
    R = calc_R(AffineCommits, Zs, Ys, <<>>),
    %R = fr:encode(1),%todo!!
    %io:fwrite("multiprove 3\n"),
    %spends lots of time here.
    io:fwrite("multiprove calc G *slow* \n"),% 45%
    benchmark:now(),
    %the slow step.
    G = calc_G(R, As, Ys, Zs, Domain, DA),
    %G is a vector of fr encoded values.
    %io:fwrite("multiprove 4\n"),
    io:fwrite("multiprove commit to G\n"),
    benchmark:now(),
    %io:fwrite({length(G), length(Gs)}),
    CommitG_e = ipa2:commit(G, Gs),
    io:fwrite("multiprove calc random T\n"),
    benchmark:now(),
    %T = calc_T(fq:extended2affine(CommitG_e), R),
    T = calc_T(hd(ed:extended2affine_batch(
                    [CommitG_e])), R),
    %T = fr:encode(5),%todo!!!
    %io:fwrite("multiprove 6\n"),
    %spend very little time here.
    io:fwrite("multiprove calc polynomial h\n"), % 9%
    benchmark:now(),
    %a little slow.
    He = calc_H(R, T, As, Zs),%this is G1
    %io:fwrite("multiprove 7\n"),
    io:fwrite("multiprove calc commit to G-E\n"),
    benchmark:now(),
    NG2 = poly2:sub(G, He),
    io:fwrite("multiprove evaluate G-E outside the domain\n"),
    benchmark:now(),
    %io:fwrite({fr:decode([T, Domain, PA, DA])}),
    %[1, [1,2,3,4], poly, [poly, poly...]]
    EV = poly2:eval_outside_v(T, Domain, PA, DA),
    %io:fwrite("multiprove 9\n"),
    io:fwrite("multiprove create ipa opening to G-E\n"), % 2%
    benchmark:now(),
    %spend a little time here.
    IPA = ipa2:make_ipa(NG2, EV, 
                       Gs, Hs, Q),
    if
        ?sanity_checks ->
            {_RIDs, G2b} = 
                calc_G2_2(R, T, Ys, Zs),
            true = (fr:encode(0) 
                    == fr:add(G2b, element(
                                     2, IPA)));
        true -> ok
    end,
    io:fwrite("multiprove finished\n"),
    benchmark:now(),
    {CommitG_e, 
     IPA}.
verify({CommitG, Open_G_E}, Commits, Zs, Ys) ->
    {Gs, Hs, Q} = parameters2:read(),
    DA = parameters2:da(),
    PA = parameters2:a(),
    Domain = parameters2:domain(),

    io:fwrite("multiproof verify calc r\n"),
    benchmark:now(),
    T1 = erlang:timestamp(),
    [ACG|AffineCommits] = 
        %fq:to_affine_batch(
        ed:extended2affine_batch(
          [CommitG|Commits]),
    T2 = erlang:timestamp(),
%    io:fwrite({hd(AffineCommits), hd(Zs),
%               hd(Ys)}),
    R = calc_R(AffineCommits, Zs, 
               %fr:encode(Ys), <<>>),
               Ys, <<>>),
    io:fwrite("multiproof verify calc t\n"),
    benchmark:now(),
    T3 = erlang:timestamp(),
    T = calc_T(ACG, R),

    io:fwrite("multiproof verify eval outside v\n"),
    benchmark:now(),
    EV = poly2:eval_outside_v(
           T, Domain, PA, DA),
    T4 = erlang:timestamp(),

    io:fwrite("multiproof verify ipa\n"),
    benchmark:now(),
    %here.
    %io:fwrite({Open_G_E, EV}),
    true = ipa2:verify_ipa(
             Open_G_E, EV, Gs, Hs, Q),
    T5 = erlang:timestamp(),

    io:fwrite("multiproof verify g2\n"),
    benchmark:now(),
    %io:fwrite({R, T, Ys, Zs}),%bin, bin, [int..], [bin]
    {RIDs, G2} = 
        %calc_G2_2(R, T, fr:encode(Ys), Zs),
        calc_G2_2(R, T, Ys, Zs),
    %io:fwrite({G2, R, T, hd(Ys), hd(Zs)}),

    T6 = erlang:timestamp(),

    %sum_i  Ci*(R^i/(T-Zi))
    io:fwrite("multiproof verify commit neg *slow* e\n"),% 70% of the cost of verification is here.
    benchmark:now(),
    %the slow step.
    CommitE = 
        multi_exponent:doit(
          RIDs, Commits),%this is the slowest step.
    %CommitNegE = fq:e_neg(CommitE),
    CommitNegE = ed:e_neg(CommitE),
    %true = secp256k1:jacob_equal(CommitNegE, CommitNegE2, E),
    T7 = erlang:timestamp(),
    
    %CommitG_sub_E = ipa:add(CommitG, CommitNegE, E),
    io:fwrite("multiproof verify commit G-E\n"),
    benchmark:now(),
    CommitG_sub_E = 
        %fq:e_add(CommitG, CommitNegE),
        ed:e_add(CommitG, CommitNegE),
    T8 = erlang:timestamp(),
    io:fwrite("multiproof verify ipa eq\n"),
    benchmark:now(),
    true = ipa2:eq(CommitG_sub_E, 
                   element(1, Open_G_E)),
    T9 = erlang:timestamp(),
    NegE = timer:now_diff(T7, T6),
    io:fwrite("multiproof verify done\n"),
    benchmark:now(),
    %io:fwrite({G2, element(2, Open_G_E)}),
    true = (fr:encode(0) == 
                fr:add(G2, element(2, Open_G_E))),
    true.
    %io:fwrite(integer_to_list(timer:now_diff(T4, T3))),
    %io:fwrite("\n"),
    %io:fwrite("proofs per second: "),
    %io:fwrite(integer_to_list(round(length(Zs) * 1000000 / NegE))),
    %io:fwrite("\n"),
    %0 == add(G2, element(2, Open_G_E), Base).
%    fr:encode(0) == 
%        fr:add(G2, element(2, Open_G_E)).
   
         
range(X, X) -> [];
range(A, X) when A<X -> 
    [A|range(A+1, X)].

many(_, 0) -> [];
many(X, N) when N > 0 -> 
    [X|many(X, N-1)].
    
test(1) ->
    %calc_G
    %sum from i=0 to m-1 of r^i f_i(X)/(t-z_i)
    Domain = parameters2:domain(),
    Many = 2,
    %As are vectors that contain elements Y at locations Z.
    A = lists:map(fun(X) -> fr:neg(X) end,
                  lists:reverse(Domain)),
    As = lists:map(fun(_) -> A end,
                   range(0, Many)),
    Zs = many(hd(tl(Domain)), Many),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly2:eval_e(Z, F, Domain)
           end, As, Zs),

    DA = poly2:c2e(parameters2:da(), Domain),
    R = fr:encode(1),
    G2 = calc_G(R, As, Ys, Zs, Domain, DA),
    {G2};
test(2) ->
    %dth root of unity
    E = secp256k1:make(),
    Base = secp256k1:order(E),

    R1 = rand:uniform(Base),
    
    R2 = basics:lrpow(R1, Base-2, Base),
    R3 = basics:lrpow(R1, (Base-1) div 2, Base),

    
    
    {pedersen:fmul(R2, R2, E),
     pedersen:fmul(R3, R3, E),
     R3,
     (Base-1) rem 2,
     (Base-1) rem 3,
     Base-1
    },
    %prime factors of base-1:
    % 2^6, 3, 149, 631
    %basics:prime_factors(Base-1).
    %Root64 = primitive_nth_root(64, E),
    %Root = primitive_nth_root(2, E),
    ok;
%    {pedersen:fmul(Root, Root, E),
%     basics:lrpow(Root64, 64, Base)};
%     Root, 
%     Root64};
test(3) ->
    %test prove.
    {Gs0, Hs0, Q} = parameters2:read(),
    {Gs, _} = lists:split(4, Gs0),
    {Hs, _} = lists:split(4, Hs0),
    Domain = fr:encode([1,2,3,4]),
    Many = length(Domain),
    DA = poly2:c2e(poly2:calc_DA(Domain), Domain),
    PA = poly2:calc_A(Domain),
    A = lists:map(fun(X) -> 
                          fr:add(X, fr:encode(0)) 
                  end,
                  lists:reverse(Domain)),
    As = lists:map(fun(_) -> A end,
                   range(0, Many)),
    Zs = many(hd(tl(Domain)), Many),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly2:eval_e(Z, F, Domain)
           end, As, Zs),
    Commit1 = ipa2:commit(hd(As), Gs),
    Commits0 = lists:map(
      fun(A) ->
              Commit1
      end, As),
   % Commits = fq:e_simplify_batch(Commits0),
    Commits = ed:normalize(Commits0),
    %io:fwrite({fr:decode(A)}),
    io:fwrite("location 5 "),
    io:fwrite(integer_to_list(fr:decode(poly2:eval_outside(fr:encode(5), A, Domain, PA, DA)))),
    io:fwrite("\n"),
    Proof = prove(As, Zs, Commits, Gs, Hs, 
                  Q, DA, PA, Domain),
    success;
    
test(7) ->
    Many = 5,
    io:fwrite("many is "),
    io:fwrite(integer_to_list(Many)),
    io:fwrite("\n"),
    Domain = parameters2:domain(),
    A = lists:map(fun(X) -> fr:neg(X) end,
                  lists:reverse(Domain)),
    As = lists:map(fun(_) -> A end,
                   range(0, Many)),
    Zs = many(hd(tl(Domain)), Many),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly2:eval_e(Z, F, Domain)
           end, As, Zs),
    {Gs, Hs, Q} = parameters2:read(),
    Commit1 = ipa2:commit(hd(As), Gs),
    Commits0 = lists:map(fun(A) -> Commit1 end, 
                         As),
    Commits = ed:normalize(Commits0),
    io:fwrite("make proof\n"),
    T1 = erlang:timestamp(),
    {Gs, Hs, Q} = parameters2:read(),
    DA = parameters2:da(),
    PA = parameters2:a(),
    Domain = parameters2:domain(),
    Proof = prove(As, Zs, Commits, Gs, Hs, 
                  Q, DA, PA, Domain),
    T2 = erlang:timestamp(),
    io:fwrite("verify proof\n"),
    %true = verify(Proof2, Commits, Zs, Ys, P),
    Verified = verify(Proof, Commits, Zs, Ys),
    if
        Verified -> ok;
        true ->
            io:fwrite({Proof, hd(Zs), hd(Ys)}),
            io:fwrite("here\n"),
            ok
    end,
    T3 = erlang:timestamp(),
    {prove, timer:now_diff(T2, T1),
      verify, timer:now_diff(T3, T2)}.
    
                          
    

    
    


    
