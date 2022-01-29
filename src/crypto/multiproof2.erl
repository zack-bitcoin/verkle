-module(multiproof2).
-export([prove/3, verify/4, test/1]).


calc_G_e(R, As, Ys, Zs, Domain, DA) ->
    %polynomial h from dankrad's paper.
    DivEAll = parameters2:div_e(),
    DivEAll2 = 0,
    calc_G_e2(fr:encode(1), R, As, Ys, Zs,
              Domain, DA, DivEAll, DivEAll2, []).
calc_G_e2(_, _, [], [], [], _, _, _, _ ,
          Accumulator) -> Accumulator;
calc_G_e2(RA, R, [A|AT], [Y|YT], [Z|ZT], Domain,
          DA, DivEAll, DivEAll2, Accumulator) ->
    X1 = lists:map(fun(C) -> fr:sub(C, Y) end, A),
    P = poly2:div_e(X1, Domain, DA, 
                    Z, DivEAll, DivEAll2),
    X = poly2:mul_scalar(RA, P),
    A2 = poly2:add(X, Accumulator), 
    calc_G_e2(fr:mul(RA, R), R, AT, YT, ZT, Domain,
              DA, DivEAll, DivEAll2, A2).

mul_r_powers(_, _, []) -> [];
mul_r_powers(R, A, [C|T]) ->
    [fr:mul(C, A)|
     mul_r_powers(
       R, fr:mul(A, R), T)].

%sum_i:  r^i * y_i / (t - z_i)
calc_G2_2(R, T, Ys, Zs) ->
    Divisors = 
        lists:map(fun(Z) -> fr:sub(T, Z) end, Zs),
    IDs = fr:batch_inverse(Divisors),
    RIDs = mul_r_powers(
             R, fr:encode(1), IDs),
    L1 = lists:zipwith(
          fun(Y, I) -> fr:mul(Y, I) end,
          Ys, RIDs),
    Result = fr:add_all(L1),
    {RIDs, Result}.

%sum_i: polyA_i * (r^i)/(t - z_i)
calc_H(R, T, As, Zs) ->
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
      Commits_e) ->
    {Gs, Hs, Q} = parameters2:read(),
    DA = parameters2:da(),
    PA = parameters2:a(),
    Domain = parameters2:domain(),
    
    

    %todo. instead of accepting the entire list of As, we should receive a tree structure that allows us to stream the As. that way the memory requirement doesn't get so big.

    io:fwrite("multiprove Ys from As \n"),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   %io:fwrite({size(Z), 
                   %           length(F), 
                   %           size(hd(Domain)), 
                   %           Z, F, hd(Domain)}),
                   poly2:eval_e(Z, F, Domain)
           end, As, Zs),%this should be streamed with calculating the As.
    io:fwrite("multiprove calc random R\n"),
    AffineCommits = 
        fq2:to_affine_batch(
          Commits_e),
    R = calc_R(AffineCommits, Zs, Ys, <<>>),
    %io:fwrite("multiprove 3\n"),
    %spends lots of time here.
    io:fwrite("multiprove calc G\n"),
    %the slow step.
    G2 = calc_G_e(R, As, Ys, Zs, Domain, DA),
    %io:fwrite("multiprove 4\n"),
    io:fwrite("multiprove commit to G\n"),
    %io:fwrite({length(G2), length(Gs)}),
    CommitG_e = ipa2:commit(G2, Gs),
    io:fwrite("multiprove calc random T\n"),
    T = calc_T(fq2:extended2affine(CommitG_e), R),
    %io:fwrite("multiprove 6\n"),
    %spend very little time here.
    io:fwrite("multiprove calc polynomial h\n"),
    %a little slow.
    He = calc_H(R, T, As, Zs),
    %io:fwrite("multiprove 7\n"),
    io:fwrite("multiprove calc commit to G-E\n"),
    G_sub_E_e = poly2:sub(G2, He),
    io:fwrite("multiprove evaluate G-E outside the domain\n"),
    EV = poly2:eval_outside_v(T, Domain, PA, DA),
    %io:fwrite("multiprove 9\n"),
    io:fwrite("multiprove create ipa opening to G-E\n"),
    %spend a little time here.
    IPA = ipa2:make_ipa(G_sub_E_e, EV, 
                       Gs, Hs, Q),
    io:fwrite("multiprove finished\n"),
    {CommitG_e, 
     IPA}.
verify({CommitG, Open_G_E}, Commits, Zs, Ys) ->
    {Gs, Hs, Q} = parameters2:read(),
    DA = parameters2:da(),
    PA = parameters2:a(),
    Domain = parameters2:domain(),
    %io:fwrite({CommitG0, Commits0, Cs0}),
%    {[CommitG|Commits], Cs} = 
%        lists:split(length(Commits0)+1, 
%                    secp256k1:simplify_Zs_batch(
%                      [CommitG0|Commits0] ++ Cs0)),
   
%    Open_G_E = setelement(3, Open_G_E0, Cs),
    io:fwrite("multiproof verify calc r\n"),
    T1 = erlang:timestamp(),
    [ACG|AffineCommits] = 
        fq2:to_affine_batch(
          [CommitG|Commits]),
    T2 = erlang:timestamp(),
    R = calc_R(AffineCommits, Zs, Ys, <<>>),
    io:fwrite("multiproof verify calc t\n"),
    T3 = erlang:timestamp(),
    T = calc_T(ACG, R),
    io:fwrite("multiproof verify eval outside v\n"),
    EV = poly2:eval_outside_v(
           T, Domain, PA, DA),
    T4 = erlang:timestamp(),
    io:fwrite("multiproof verify ipa\n"),
    true = ipa2:verify_ipa(
             Open_G_E, EV, Gs, Hs, Q),
    T5 = erlang:timestamp(),
    io:fwrite("multiproof verify g2\n"),
    {RIDs, G2} = calc_G2_2(R, T, Ys, Zs),
    T6 = erlang:timestamp(),
    %sum_i  Ci*(R^i/(T-Zi))
    io:fwrite("multiproof verify commit neg e\n"),
    %the slow step.
    CommitE = multi_exponent:doit(RIDs, fq2:extended2extended_niels(Commits)), %this is the slowest step.
    CommitNegE = fq2:e_neg(CommitE),
    %true = secp256k1:jacob_equal(CommitNegE, CommitNegE2, E),
    T7 = erlang:timestamp(),
    
    %CommitG_sub_E = ipa:add(CommitG, CommitNegE, E),
    io:fwrite("multiproof verify commit G-E\n"),
    CommitG_sub_E = fq2:e_add(CommitG, fq2:extended2extended_niels(CommitNegE)),
    T8 = erlang:timestamp(),
    io:fwrite("multiproof verify ipa eq\n"),
    true = ipa2:eq(CommitG_sub_E, 
                   element(1, Open_G_E)),
    T9 = erlang:timestamp(),
    NegE = timer:now_diff(T7, T6),
    io:fwrite("multiproof verify done\n"),
    %io:fwrite(integer_to_list(timer:now_diff(T4, T3))),
    %io:fwrite("\n"),
    %io:fwrite("proofs per second: "),
    %io:fwrite(integer_to_list(round(length(Zs) * 1000000 / NegE))),
    %io:fwrite("\n"),
    %0 == add(G2, element(2, Open_G_E), Base).
    fr:encode(0) == 
        fr:add(G2, element(2, Open_G_E)).
   
         
range(X, X) -> [];
range(A, X) when A<X -> 
    [A|range(A+1, X)].

many(_, 0) -> [];
many(X, N) when N > 0 -> 
    [X|many(X, N-1)].
    
                          
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
test(7) ->
    Many = 5,
    io:fwrite("many is "),
    io:fwrite(integer_to_list(Many)),
    io:fwrite("\n"),
    %E = secp256k1:make(),
    %Base = secp256k1:order(E),
    %Root4 = primitive_nth_root(4, E),
    %Root4b = fr:mul(Root4, Root4),
    %Root4c = fr:mul(Root4b, Root4),
    %Domain = [1, Root4, Root4b, Root4c],
%    Domain = [fr:encode(1),
%              fr:encode(2),
%              fr:encode(3),
%              fr:encode(4)],
    
    %Domain = [5,6,7,8],
    %P = make_parameters_jacob(Domain, E),
    %A = [sub(0, 4, Base),
    %     sub(0, 3, Base),
    %     sub(0, 2, Base),
    %     sub(0, 1, Base)],
    %A = [?neg(4), ?neg(3), ?neg(2), ?neg(1)],
    Domain = parameters2:domain(),
    A = lists:map(fun(X) -> fr:neg(X) end,
                  lists:reverse(Domain)),
    As = lists:map(fun(_) -> A end,
                   range(0, Many)),
    %As = lists:map(fun(R) -> [sub(0, R, Base),
    %                          sub(0, R+3, Base),
    %                          sub(0, R+2, Base),
   %                           sub(0, R+1, Base)] end,
   %                range(0, Many)),
    %Zs = many(Root4, Many),
    Zs = many(hd(tl(Domain)), Many),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly2:eval_e(Z, F, Domain)
           end, As, Zs),
    {Gs, Hs, Q} = parameters2:read(),
    %Gs = P#p.g,
    Commit1 = ipa2:commit(hd(As), Gs),
    Commits0 = lists:map(
      fun(A) ->
              %ipa:commit(A, Gs, E)
              Commit1
      end, As),
    %Commits = secp256k1:simplify_Zs_batch(
    %            Commits0),
    Commits = fq2:e_simplify_batch(Commits0),
    io:fwrite("make proof\n"),
    T1 = erlang:timestamp(),
    Proof = prove(As, Zs, Commits),
    %{P1, Open = {_,_,Ps2,_,_}} = Proof,
    %[P1b|Ps2b] = secp256k1:simplify_Zs_batch(
    %               [P1|Ps2]),
    %Open2 = setelement(3, Open, Ps2b),
    %Proof2 = {P1b, Open2},
    T2 = erlang:timestamp(),
    io:fwrite("verify proof\n"),
    %true = verify(Proof2, Commits, Zs, Ys, P),
    true = verify(Proof, Commits, Zs, Ys),
    T3 = erlang:timestamp(),
    {prove, timer:now_diff(T2, T1),
      verify, timer:now_diff(T3, T2)}.
    
                          
    

    
    


    
