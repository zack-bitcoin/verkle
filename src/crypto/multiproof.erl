-module(multiproof).
-export([prove/9, fast_prove/9,
         verify/4, test/1]).

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
                      parameters:div_e();
                  _ -> poly:all_div_e_parameters(
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
    P = poly:div_e(X1, Domain, DA, 
                    Z, DivEAll, DivEAll2),
    X = poly:mul_scalar(RA, P),
    A2 = poly:add(X, Accumulator), 
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
    X = poly:mul_scalar(H, A),
    Acc2 = poly:add(X, Acc),
    calc_H2(T, AT, Acc2).

%calc_R and calc_T are using 
calc_R([], [], [], B) -> 
    %deterministically generated random number. 
    %io:fwrite(base64:encode(B)),
    %io:fwrite("\n"),
    <<R:256>> = hash:doit(B),
    fr:encode(R rem fr:prime());
calc_R([<<C1:256, C2:256>>|CT], 
       [<<Z:256>>|ZT], [<<Y:256>>|YT], B) -> 
    B2 = <<B/binary, 
           Z:256, 
           Y:256, 
           C1:256, 
           C2:256>>,
    calc_R(CT, ZT, YT, B2);
calc_R(A, B, C, D) -> 
    io:fwrite({A, B, C, D}).

calc_T(<<C1:256, C2:256>>, <<R:256>>) ->
    %deterministically generated random number. 
    B = <<C1:256, C2:256, R:256>>,
    <<R2:256>> = hash:doit(B),
    fr:encode(R2 rem fr:prime()).

dot(A, B) ->
    C = dot2(A,B),
    fr:add_all(C).

dot2([], []) -> [];
dot2([A|AT], [B|BT]) -> 
    [fr:mul(A, B)|dot2(AT, BT)].
   
fast_prove(As, Zs, Commits_e, Gs, DA, Domain) ->
    fast_prove(As, Zs, Commits_e, Gs, 0, 0, DA, 0, 
               Domain).
fast_prove(As, %[[256 fr encoded ints]...]
           Zs, %[element_in_domain...]
           Commits_e, %commits of vectors in A to Gs.
           Gs, _Hs, _Q, DA, _PA, Domain) -> 
    
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, Domain)
           end, As, Zs),%this should be streamed with calculating the As.
    AffineCommits = 
        ed:extended2affine_batch(
          Commits_e),
    R = calc_R(AffineCommits, Zs, Ys, <<>>),
    G = calc_G(R, As, Ys, Zs, Domain, DA),
    CommitG_e = ipa:commit(G, Gs),
    T = calc_T(hd(ed:extended2affine_batch(
                    [CommitG_e])), R),
    He = calc_H(R, T, As, Zs),%this is G1
    NG2 = poly:sub(G, He),%this is A in the bullet proof.
    {CommitG_e, NG2}.
fast_verify({CommitG, NG2}, Commits, Zs, Ys) ->
    {Gs, _Hs, _Q} = parameters:read(),
    DA = parameters:da(),
    PA = parameters:a(),
    Domain = parameters:domain(),
    [ACG|AffineCommits] = 
        ed:extended2affine_batch(
          [CommitG|Commits]),
    R = calc_R(AffineCommits, Zs, 
               Ys, <<>>),
    T = calc_T(ACG, R),
    EV = poly:eval_outside_v(
           T, Domain, PA, DA),

    AG = ipa:commit(NG2, Gs),

    {RIDs, G2} = 
        calc_G2_2(R, T, Ys, Zs),
    CommitE = 
        multi_exponent:doit(
          RIDs, Commits),%this is the slowest step.
    CommitNegE = ed:e_neg(CommitE),
    CommitG_sub_E = 
        ed:e_add(CommitG, CommitNegE),
    true = ed:e_eq(CommitG_sub_E, AG),
    AB = dot(NG2, EV),
    true = (fr:encode(0) == 
                fr:add(G2, AB)),
    true. 
    
prove(As, %committed data
      Zs, %the slot in each commit we are reading from. A list as long as As. Made up of elements that are in the domain.
      Commits_e, Gs, Hs, Q, DA, PA, Domain) ->

    io:fwrite("multiprove Ys from As \n"),
    benchmark:now(),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, Domain)
           end, As, Zs),%this should be streamed with calculating the As.
    %io:fwrite({fr:decode([Ys, As, Zs])}),
    %Ys [3,3,3,3]
    %As [[4,3,2,1],...]
    %Zs [2,2,2,2]
    io:fwrite("multiprove calc random R\n"),% 4%
    benchmark:now(),
    AffineCommits = 
        ed:extended2affine_batch(
          Commits_e),
    R = calc_R(AffineCommits, Zs, Ys, <<>>),
    io:fwrite("multiprove calc G *slow* \n"),% 45%
    benchmark:now(),
    %the slow step.
    G = calc_G(R, As, Ys, Zs, Domain, DA),
    %G is a vector of 256 fr encoded values.
    %io:fwrite("multiprove 4\n"),
    io:fwrite("multiprove commit to G\n"),
    benchmark:now(),
    CommitG_e = ipa:commit(G, Gs),
    io:fwrite("multiprove calc random T\n"),
    benchmark:now(),
    T = calc_T(hd(ed:extended2affine_batch(
                    [CommitG_e])), R),
    %spend very little time here.
    io:fwrite("multiprove calc polynomial h\n"), % 9%
    benchmark:now(),
    %a little slow.
    He = calc_H(R, T, As, Zs),%this is G1
    %io:fwrite("multiprove 7\n"),
    io:fwrite("multiprove calc commit to G-E\n"),
    benchmark:now(),
    NG2 = poly:sub(G, He),
    io:fwrite("multiprove evaluate G-E outside the domain\n"),
    benchmark:now(),
    %io:fwrite({fr:decode([T, Domain, PA, DA])}),
    %[1, [1,2,3,4], poly, [poly, poly...]]
    EV = poly:eval_outside_v(T, Domain, PA, DA),
    %io:fwrite("multiprove 9\n"),
    io:fwrite("multiprove create ipa opening to G-E\n"), % 2%
    benchmark:now(),
    %spend a little time here.
    IPA = ipa:make_ipa(NG2, EV, Gs, Hs, Q),
    if
        ?sanity_checks ->
            {RIDs, G2b} = 
                calc_G2_2(R, T, Ys, Zs),
            EVi = fr:decode(EV),
            <<EVB:256>> = hash:list_of_ints(EVi),
            io:fwrite(integer_to_list(length(EVi))),
            io:fwrite("\n"),
            io:fwrite(integer_to_list(hd(EVi))),
            io:fwrite("\n"),
            io:fwrite(integer_to_list(EVB)),
            %lists:map(fun(X) -> io:fwrite(integer_to_list(X)), io:fwrite("\n") end, EVi),
            io:fwrite("\n"),
            true = ipa:verify_ipa(
                     IPA, EV, 
                     Gs, Hs, Q),

            %checking that neg G2b is equal to NG2 dot EV
            Sanity = ipa:dot(NG2, EV),
            true = (Sanity == element(2, IPA)),
            true = (Sanity == fr:neg(G2b)),
            true = (fr:encode(0) 
                    == fr:add(G2b, element(
                                     2, IPA))),
            CommitE = 
                multi_exponent:doit(
                  RIDs, Commits_e),
            G_sub_E = 
                ed:e_add(
                  CommitG_e, ed:e_neg(CommitE)),
            Bool = ed:e_eq(G_sub_E,
                           element(1, IPA)),
            if
                Bool -> ok;
                true ->
                    io:fwrite("sanity failure"),
                    1=2
            end,
            ok;
        true -> ok
    end,
    io:fwrite("multiprove finished\n"),
    benchmark:now(),
    {CommitG_e, 
     IPA}.
verify({CommitG, Open_G_E}, Commits, Zs, Ys) 
  when ((is_list(Open_G_E)) 
        and (length(Open_G_E) == 256))->
    fast_verify({CommitG, Open_G_E}, Commits, Zs, Ys);
verify({CommitG, Open_G_E}, Commits, Zs, Ys) ->
    {Gs, Hs, Q} = parameters:read(),
    DA = parameters:da(),
    PA = parameters:a(),
    Domain = parameters:domain(),
    io:fwrite("multiproof verify calc r\n"),
    benchmark:now(),
    [ACG|AffineCommits] = 
        ed:extended2affine_batch(
          [CommitG|Commits]),
    R = calc_R(AffineCommits, Zs, 
               Ys, <<>>),
    io:fwrite("multiproof verify calc t\n"),
    benchmark:now(),
    T = calc_T(ACG, R),

    io:fwrite("multiproof verify eval outside v\n"),
    benchmark:now(),
    EV = poly:eval_outside_v(
           T, Domain, PA, DA),
    io:fwrite("multiproof verify ipa\n"),
    benchmark:now(),
    true = ipa:verify_ipa(
             Open_G_E, EV, Gs, Hs, Q),

    io:fwrite("multiproof verify g2\n"),
    benchmark:now(),
    %io:fwrite({R, T, Ys, Zs}),%bin, bin, [int..], [bin]
    {RIDs, G2} = 
        calc_G2_2(R, T, Ys, Zs),

    %sum_i  Ci*(R^i/(T-Zi))
    io:fwrite("multiproof verify commit neg *slow* e\n"),% 70% of the cost of verification is here.
    benchmark:now(),
    %the slow step.
    CommitE = 
        multi_exponent:doit(
          RIDs, Commits),%this is the slowest step.
    CommitNegE = ed:e_neg(CommitE),
    
    io:fwrite("multiproof verify commit G-E\n"),
    benchmark:now(),
    CommitG_sub_E = 
        ed:e_add(CommitG, CommitNegE),
    io:fwrite("multiproof verify eq\n"),
    benchmark:now(),
    AG = element(1, Open_G_E),
    true = ed:e_eq(CommitG_sub_E, AG),
    io:fwrite("multiproof verify done\n"),
    benchmark:now(),
    AB = element(2, Open_G_E),
    true = (fr:encode(0) == 
                fr:add(G2, AB)),
    true.
   
         
range(X, X) -> [];
range(A, X) when A<X -> 
    [A|range(A+1, X)].

many(_, 0) -> [];
many(X, N) when N > 0 -> 
    [X|many(X, N-1)].
    
test(1) ->
                                                %calc_G
                                                %sum from i=0 to m-1 of r^i f_i(X)/(t-z_i)
    Domain = parameters:domain(),
    Many = 2,
    %As are vectors that contain elements Y at locations Z.
    A = lists:map(fun(X) -> fr:neg(X) end,
                  lists:reverse(Domain)),
    As = lists:map(fun(_) -> A end,
                   range(0, Many)),
    Zs = many(hd(tl(Domain)), Many),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, Domain)
           end, As, Zs),

    DA = poly:c2e(parameters:da(), Domain),
    R = fr:encode(1),
    G2 = calc_G(R, As, Ys, Zs, Domain, DA),
    {G2};
test(3) ->
    %test prove.
    {Gs0, Hs0, Q} = parameters:read(),
    {Gs, _} = lists:split(4, Gs0),
    {Hs, _} = lists:split(4, Hs0),
    Domain = fr:encode([1,2,3,4]),
    Many = length(Domain),
    DA = poly:c2e(poly:calc_DA(Domain), Domain),
    PA = poly:calc_A(Domain),
    A = lists:map(fun(X) -> 
                          fr:add(X, fr:encode(0)) 
                  end,
                  lists:reverse(Domain)),
    As = lists:map(fun(_) -> A end,
                   range(0, Many)),
    Zs = many(hd(tl(Domain)), Many),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, Domain)
           end, As, Zs),
    Commit1 = ipa:commit(hd(As), Gs),
    Commits0 = lists:map(
      fun(A) ->
              Commit1
      end, As),
   % Commits = fq:e_simplify_batch(Commits0),
    Commits = ed:normalize(Commits0),
    %io:fwrite({fr:decode(A)}),
    io:fwrite("location 5 "),
    io:fwrite(integer_to_list(fr:decode(poly:eval_outside(fr:encode(5), A, Domain, PA, DA)))),
    io:fwrite("\n"),
    Proof = prove(As, Zs, Commits, Gs, Hs, 
                  Q, DA, PA, Domain),
    success;
    
test(7) ->
    Many = 3,
    io:fwrite("many is "),
    io:fwrite(integer_to_list(Many)),
    io:fwrite("\n"),
    Domain = parameters:domain(),
    A = lists:map(fun(X) -> fr:neg(X) end,
                  lists:reverse(Domain)),
    As = lists:map(fun(_) -> A end,
                   range(0, Many)),
    Zs = many(hd(tl(Domain)), Many),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, Domain)
           end, As, Zs),
    {Gs, Hs, Q} = parameters:read(),
    Commit1 = ipa:commit(hd(As), Gs),
    Commits0 = lists:map(fun(A) -> Commit1 end, 
                         As),
    Commits = ed:normalize(Commits0),
    io:fwrite("make proof\n"),
    T1 = erlang:timestamp(),
    {Gs, Hs, Q} = parameters:read(),
    DA = parameters:da(),
    PA = parameters:a(),
    Domain = parameters:domain(),
    %io:fwrite({length(hd(As)), length(As), length(Zs), length(Commits)}),
    %256,1,1,1
    Proof = prove(As, Zs, Commits, Gs, Hs, 
                  Q, DA, PA, Domain),
    FProof = fast_prove(As, Zs, Commits, Gs, Hs, 
                  Q, DA, PA, Domain),
    true = verify(Proof, Commits, Zs, Ys),
    true = verify(FProof, Commits, Zs, Ys),
    T2 = erlang:timestamp(),
    %io:fwrite("verify proof\n"),
    %io:fwrite({Ys}),
    {FProof, Commits};
    
test(8) ->
    Domain = parameters:domain(),
    {Gs, Hs, Q} = parameters:read(),
    DA = parameters:da(),
    PA = parameters:a(),

    Many = 3,
    As = lists:map(
          fun(Y) ->
                  lists:map(
                    fun(X) ->
                            fr:add(fr:mul(X, X),
                                   fr:encode(
                                     fr:prime()-
                                         (10000*Y)))
                    end, Domain)
          end, range(0, Many)),
    Zs = many(hd(tl(tl(Domain))), Many),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, Domain)
           end, As, Zs),
    Commits0 = lists:map(
                 fun(A) ->
                         ipa:commit(A, Gs)
                 end, As),
    Commits = ed:normalize(Commits0),

    
    Proof = prove(As, Zs, Commits, Gs, Hs, 
                  Q, DA, PA, Domain),
    true = verify(Proof, Commits, Zs, Ys),
    FastProof = fast_prove(As, Zs, Commits, Gs, Hs, 
                           Q, DA, PA, Domain),
    true = verify(FastProof, Commits, Zs, Ys),
    success;
test(9) ->
    Y = fr:encode(5),
    Z = fr:encode(6),
    P = ipa:gen_point(0),
    R = calc_R([P], [Z], [Y], <<>>),
    R.

%<<"ZH19WZA9dBN/b0UWEjP1Ogiz/UlHXjkIBWvHNeDnVQ8=">>

                          

    
                          
    

    
    


    
