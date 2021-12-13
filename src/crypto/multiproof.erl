-module(multiproof).
-export([test/1, 
         compress/1, decompress/1,
         make_parameters_jacob/2, 
         primitive_nth_root/2,
         prove/4, verify/5,
         make_parameters_range/2
        ]).

%multiproofs for pedersen IPA.
%We are trying merge IPA.

%going through this paper: https://dankradfeist.de/ethereum/2021/06/18/pcs-multiproofs.html

-record(p, {e, b, g, h, q, domain, a, da, ls}).

-define(order, 115792089237316195423570985008687907852837564279074904382605163141518161494337).
-define(mul(A, B), ((A * B) rem ?order)).
-define(sub(A, B), ((A - B + ?order) rem ?order)).%assumes B less than ?order
-define(neg(A), ((?order - A))).%assumes A less than ?order
-define(add(A, B), ((A + B) rem ?order)).

-define(add_mod(C), %assumes C is positive and less than ?prime
        if (C>= ?order ) -> C - ?order;
           true -> C end).

-define(sub2(A, B), %assumes A and B are positive and less than ?prime
        (if(A>=B) -> (A - B); 
           true -> (A + ?order - B) end)).

make_parameters_range(Many, E) ->
    D = range(1, Many+1),
    make_parameters_jacob(D, E).
make_parameters_jacob(Domain, E) ->
    {Gs, Hs, Q} = ipa:basis(length(Domain), E),
    make_parameters2(Domain, E, Gs, Hs, Q).
make_parameters2(Domain, E, Gs, Hs, Q) ->
    Base = secp256k1:order(E),
    DAC = poly:calc_DA(Domain, E),%derivative of polynomial PA in coefficient format.
    DA = poly:c2e(DAC, Domain, Base),%now evaluation format.
    %Ls = poly:lagrange_polynomials(Domain, Base),
    PA = poly:calc_A(Domain, Base),
    #p{e = E, %the elliptic curve settings.
       b = Base, %group order of the elliptic curve.
       g = Gs, h = Hs, q = Q,%a bunch of elliptic curve points.
       domain = Domain, %the locations in the polynomial where we store information.
       a = PA, %all the base polynomials of the domain multiplied together.
       da = DA, %the finite derivative of PA. used along with PA to calculate values for the evaluation format polynomial outside of the domain.
       ls = 0}.
    

primitive_nth_root(N, E) ->
    Base = secp256k1:order(E),
    0 = N rem 2,
    X = random:uniform(Base),
    %true = (0 == ((Base - 1) rem N)),
    NI = basics:inverse(N, Base),
    G = basics:lrpow(
          X, ff:mul(Base - 1, NI, Base), Base),
    GP = basics:lrpow(G, N div 2, Base),
    if
        (GP == 1) ->
            primitive_nth_root(N, E);
        true -> G
    end.

calc_G_e(R, As, Ys, Zs, Domain, DA) ->

    %polynomial h from dankrad's paper.

    DivEAll = parameters:div_e(),
    %DivEAll = 0,
    %DivEAll2 = poly:all_div_e_parameters2(),
    DivEAll2 = 0,
    calc_G_e2(1, R, As, Ys, Zs,
              Domain, DA, DivEAll, DivEAll2, []).
calc_G_e2(_, _, [], [], [], _, _, _, _ ,
          Accumulator) -> Accumulator;
calc_G_e2(RA, R, [A|AT], [Y|YT], [Z|ZT], Domain,
          DA, DivEAll, DivEAll2, Accumulator) ->
    X1 = lists:map(fun(C) -> ?sub2(C, Y) end, A),
    P = poly:div_e(X1, Domain, DA, Z, DivEAll, DivEAll2),
    X = poly:mul_scalar(RA, P),
    A2 = poly:add(X, Accumulator), 
    calc_G_e2(?mul(RA, R), R, AT, YT, ZT, Domain,
              DA, DivEAll, DivEAll2, A2).

mul_r_powers(_, _, [], _) -> [];
mul_r_powers(R, A, [C|T], Base) ->
    [?mul(C, A)|
     mul_r_powers(
       R, ?mul(A, R), T, Base)].

%sum_i:  r^i * y_i / (t - z_i)
calc_G2_2(R, T, Ys, Zs, Base) ->
    Divisors = 
        %lists:map(fun(Z) -> sub(T, Z, Base) end, Zs),
        lists:map(fun(Z) -> ?sub2(T, Z) end, Zs),
    IDs = ff:batch_inverse(Divisors, Base),
    RIDs = mul_r_powers(R, 1, IDs, Base),

    L1 = lists:zipwith(
          fun(Y, I) -> ?mul(Y, I) end,
          Ys, RIDs),
    Result = ff:add_all(L1, Base),
    {RIDs, Result}.

%sum_i: polyA_i * (r^i)/(t - z_i)
calc_H(R, RA, T, As, Zs, Base) ->
    Divisors = 
        %lists:map(fun(Z) -> sub(T, Z, Base) end, Zs),
        lists:map(fun(Z) -> ?sub2(T, Z) end, Zs),
    IDs = ff:batch_inverse(Divisors, Base),
    RIDs = mul_r_powers(R, 1, IDs, Base),
    calc_H2(RIDs, As, Base, []).
calc_H2([], [], _, Accumulator) -> Accumulator;
calc_H2([H|T], [A|AT], Base, Acc) -> 
    X = poly:mul_scalar(H, A, Base),
    Acc2 = poly:add(X, Acc),
    calc_H2(T, AT, Base, Acc2).

calc_R([], [], [], B) -> 
    <<R:256>> = hash:doit(B),
    R;
calc_R([{C1, C2}|CT], [Z|ZT], [Y|YT], B) -> 
    %io:fwrite({C1, C2, Z, Y, B}),
    B2 = <<B/binary, 
           Z:256, 
           Y:256, 
           C1:256, 
           C2:256>>,
    calc_R(CT, ZT, YT, B2).
calc_T({C1, C2}, R) ->
    B = <<C1:256, C2:256, R:256>>,
    <<R2:256>> = hash:doit(B),
    R2.

-define(deco(X), secp256k1:decompress(X)).
-define(comp(X), secp256k1:compress(X)).
compress({C1, Csa, {AG, AB, Csb, AN, BN}}) ->
    Cs0 = Csa ++ Csb,
    [AG2, C2|Cs1] = ?comp([AG, C1|Cs0]),
    {Csa2, Csb2} = lists:split(length(Csa), Cs1),
    {C2, Csa2, {AG2, AB, Csb2, AN, BN}}.

decompress({C2, Csa2, Cipa}) ->
    Csa = lists:map(fun(X) -> ?deco(X) end, Csa2),
    Ipa = ipa:decompress(Cipa),
    {?deco(C2), Csa, Ipa}.
    
    

prove(As, %committed data
      Zs, %the slot in each commit we are reading from. A list as long as As. Made up of elements that are in the domain.
      Commits_e,
      #p{g = Gs, h = Hs, q = Q, e = E, da = DA,
        a = PA, domain = Domain}) ->

    %todo. instead of accepting the entire list of As, we should receive a tree structure that allows us to stream the As. that way the memory requirement doesn't get so big.

    io:fwrite("multiprove Ys from As \n"),
    Base = secp256k1:order(E),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, Domain, Base)
           end, As, Zs),%this should be streamed with calculating the As.
    io:fwrite("multiprove calc random R\n"),
    AffineCommits = 
        secp256k1:to_affine_batch(
          Commits_e),
    R = calc_R(AffineCommits, Zs, Ys, <<>>),
    %io:fwrite("multiprove 3\n"),
    %spends lots of time here.
    io:fwrite("multiprove calc G\n"),
    %the slow step.
    G2 = calc_G_e(R, As, Ys, Zs, Domain, DA),
    %io:fwrite("multiprove 4\n"),
    io:fwrite("multiprove commit to G\n"),
    CommitG_e = ipa:commit(G2, Gs, E),
    io:fwrite("multiprove calc random T\n"),
    T = calc_T(secp256k1:to_affine(CommitG_e), R),
    %io:fwrite("multiprove 6\n"),
    %spend very little time here.
    io:fwrite("multiprove calc polynomial h\n"),
    %a little slow.
    He = calc_H(R, 1, T, As, Zs, Base),
    %io:fwrite("multiprove 7\n"),
    io:fwrite("multiprove calc commit to G-E\n"),
    G_sub_E_e = poly:sub(G2, He, Base),
    io:fwrite("multiprove evaluate G-E outside the domain\n"),
    EV = poly:eval_outside_v(T, Domain, PA, DA, Base),
    %io:fwrite("multiprove 9\n"),
    io:fwrite("multiprove create ipa opening to G-E\n"),
    %spend a little time here.
    IPA = ipa:make_ipa(G_sub_E_e, EV, 
                       Gs, Hs, Q, E),
    io:fwrite("multiprove finished\n"),
    {CommitG_e, 
     IPA}.
verify({CommitG, Open_G_E}, Commits, Zs, Ys,
       #p{g = Gs, h = Hs, q = Q, e = E,
         domain = Domain, da = DA, a = PA}) ->
    %io:fwrite({CommitG0, Commits0, Cs0}),
%    {[CommitG|Commits], Cs} = 
%        lists:split(length(Commits0)+1, 
%                    secp256k1:simplify_Zs_batch(
%                      [CommitG0|Commits0] ++ Cs0)),
   
%    Open_G_E = setelement(3, Open_G_E0, Cs),
    io:fwrite("multiproof verify calc r\n"),
    T1 = erlang:timestamp(),
    Base = secp256k1:order(E),
    [ACG|AffineCommits] = 
        secp256k1:to_affine_batch(
          [CommitG|Commits]),
    T2 = erlang:timestamp(),
    R = calc_R(AffineCommits, Zs, Ys, <<>>),
    io:fwrite("multiproof verify calc t\n"),
    T3 = erlang:timestamp(),
    T = calc_T(ACG, R),
    io:fwrite("multiproof verify eval outside v\n"),
    EV = poly:eval_outside_v(
           T, Domain, PA, DA, Base),
    T4 = erlang:timestamp(),
    io:fwrite("multiproof verify ipa\n"),
    true = ipa:verify_ipa(
             Open_G_E, EV, Gs, Hs, Q, E),
    T5 = erlang:timestamp(),
    io:fwrite("multiproof verify g2\n"),
    {RIDs, G2} = calc_G2_2(R, T, Ys, Zs, Base),
    T6 = erlang:timestamp(),
    %sum_i  Ci*(R^i/(T-Zi))
    io:fwrite("multiproof verify commit neg e\n"),
    CommitE = secp256k1:multi_exponent(lists:map(fun(X) -> X end, RIDs), Commits, E), %this is the slowest step.
    CommitNegE = secp256k1:jacob_negate(CommitE, E),
    %true = secp256k1:jacob_equal(CommitNegE, CommitNegE2, E),
    T7 = erlang:timestamp(),
    
    %CommitG_sub_E = ipa:add(CommitG, CommitNegE, E),
    io:fwrite("multiproof verify commit G-E\n"),
    CommitG_sub_E = secp256k1:jacob_add(CommitG, CommitNegE, E),
    T8 = erlang:timestamp(),
    io:fwrite("multiproof verify ipa eq\n"),
    true = ipa:eq(CommitG_sub_E, element(1, Open_G_E), E),
    T9 = erlang:timestamp(),
    NegE = timer:now_diff(T7, T6),
    io:fwrite("multiproof verify done\n"),
    %io:fwrite(integer_to_list(timer:now_diff(T4, T3))),
    %io:fwrite("\n"),
    %io:fwrite("proofs per second: "),
    %io:fwrite(integer_to_list(round(length(Zs) * 1000000 / NegE))),
    %io:fwrite("\n"),
    %0 == add(G2, element(2, Open_G_E), Base).
    0 == ?add(G2, element(2, Open_G_E)).
   
         
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
    Root64 = primitive_nth_root(64, E),
    Root = primitive_nth_root(2, E),
    {pedersen:fmul(Root, Root, E),
     basics:lrpow(Root64, 64, Base),
     Root, 
     Root64};
test(7) ->
    Many = 5,
    io:fwrite("many is "),
    io:fwrite(integer_to_list(Many)),
    io:fwrite("\n"),
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    Root4 = primitive_nth_root(4, E),
    Root4b = ?mul(Root4, Root4),
    Root4c = ?mul(Root4b, Root4),
    Domain = [1, Root4, Root4b, Root4c],
    %Domain = [5,6,7,8],
    P = make_parameters_jacob(Domain, E),
    %A = [sub(0, 4, Base),
    %     sub(0, 3, Base),
    %     sub(0, 2, Base),
    %     sub(0, 1, Base)],
    A = [?neg(4), ?neg(3), ?neg(2), ?neg(1)],
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
                   poly:eval_e(Z, F, Domain, Base)
           end, As, Zs),
    Gs = P#p.g,
    Commit1 = ipa:commit(hd(As), Gs, E),
    Commits0 = lists:map(
      fun(A) ->
              %ipa:commit(A, Gs, E)
              Commit1
      end, As),
    T1 = erlang:timestamp(),
    Commits = secp256k1:simplify_Zs_batch(
                Commits0),
    io:fwrite("make proof\n"),
    Proof = prove(As, Zs, Commits, P),
    {P1, Open = {_,_,Ps2,_,_}} = Proof,
    [P1b|Ps2b] = secp256k1:simplify_Zs_batch(
                   [P1|Ps2]),
    Open2 = setelement(3, Open, Ps2b),
    Proof2 = {P1b, Open2},
    T2 = erlang:timestamp(),
    io:fwrite("verify proof\n"),
    true = verify(Proof2, Commits, Zs, Ys, P),
    T3 = erlang:timestamp(),
    true = verify(Proof, Commits, Zs, Ys, P),
    {prove, timer:now_diff(T2, T1),
      verify, timer:now_diff(T3, T2)}.
    
                          
    

    
    


    
