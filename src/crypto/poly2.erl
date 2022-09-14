-module(poly2).

-export(
   [calc_DA/1, calc_A/1, 
    c2e/2, %lagrange_polynomials/2, 
    sub/2, div_e/6, mul_scalar/2, 
    add/2, 
    eval_e/3, eval_outside/5, eval_outside_v/4,
    all_div_e_parameters/2,
    test/1,
    symetric_view/2
   ]).

%library for dealing with polynomials over integers mod a prime.
%Built over the jubjub curve

%finite field operations
%-define(order, 115792089237316195423570985008687907852837564279074904382605163141518161494337).
%-define(sub(A, B), ((A - B + ?order) rem ?order)).%assumes B less than ?order
%-define(neg(A), ((?order - A) rem ?order)).%assumes A less than ?order
%-define(add(A, B), ((A + B) rem ?order)).
%-define(mul(A, B), ((A * B) rem ?order)).

-record(p, {b, 
            g, 
            h, 
            q, 
            domain, 
            a, 
            da, 
            ls}).

symetric_view([], _) -> [];
symetric_view([H|T], Y) ->
    [symetric_view(H, Y)|
     symetric_view(T, Y)];
symetric_view(X, Y) ->
    Y2 = Y div 2,
    if
        (X > Y2) -> X - Y;
        true -> X
    end.

%elliptic operations

%polynomial operations
add([], []) -> [];
%add([], X) -> X;
add(X, []) -> X;
add([A|AT], [B|BT]) ->
    [fr:add(A, B)|add(AT, BT)].
sub(A, B) ->
    %A and B are polynomials.
    add(A, neg(B)).
neg([]) -> [];
neg([H|T]) -> 
    %[ff:sub(0, H, Base)|
    [fr:neg(H)|
     neg(T)].
mul_scalar(_, []) -> [];
mul_scalar(S, [A|T]) ->
    %scalar * polynomial
    [fr:mul(S, A)|
     mul_scalar(S, T)].
add_all([P]) -> P;
add_all([A, B|T]) -> 
    add_all([fr:add(A, B)|T]).

poly_add_all([P]) -> P;
poly_add_all([A,B|T]) -> 
    poly_add_all([add(A, B)|T]).

%only used for generating parameters.
mul_c_all([X]) -> X;
mul_c_all([A, B|T]) ->
    if
        (hd(A) == error) ->
            io:fwrite({A, B, T});
        true -> ok
    end,
    mul_c_all([mul_c(A, B)|T]).

%coefficient form. multiplying 2 polynomials.
%only for generating parameters.
mul_c([], _B) -> [];
mul_c(_, []) -> [];
mul_c([A], B) ->
    mul_scalar(A, B);
mul_c([A|AT], B) ->
    X = mul_scalar(A, B),
    Y = mul_c(AT, [fr:encode(0)|B]),
    add_c(X, Y).
   
%coefficient format doesn't need to be same length 
%only for generating parameters.
add_c([], B) -> B;
add_c(B, []) -> B;
add_c([A|AT], [B|BT]) ->
    [fr:add(A, B)|
     add_c(AT, BT)].


range(N, N) -> [N];
range(A, B) when A < B -> 
    [A|range(A+1, B)].

all_div_e_parameters2(Domain, DA) ->
    1=2,
    io:fwrite("calculating the poly:div_e parameters\n"),
    %P = ok,%?p,
    D = Domain,
    %DA = P#p.da,
    First = hd(D),
    Last = hd(lists:reverse(D)),
    %R = range(First - Last, Last - First),
    R = range(1, Last - First),
    As = lists:map(
          fun(DM) ->
                  case DM of
                      0 -> 1;%unused case
                      X -> X
                  end
          end, R),
    Bs = lists:map(
           fun(DM) ->
                   case DM of
                          0 -> 1;%unused case
                          X -> fr:neg(X)
                   end
           end, R),
    io:fwrite({As, Bs, DA}),
    L = fr:batch_inverse(As ++ Bs ++ DA),
    {IAs, L2} = lists:split(length(As), L),
    {IBs, IDA} = lists:split(length(Bs), L2),
    {list_to_tuple(IAs), 
     list_to_tuple(IBs), 
     list_to_tuple(IDA)}.
    
              

all_div_e_parameters(Domain, DA) ->
    io:fwrite("calculating "),
    io:fwrite(integer_to_list(length(Domain))),
    io:fwrite(" div e parameters.\n"),
    io:fwrite(integer_to_list(fr:decode(hd(Domain)))),
    L = lists:map(
          fun(M) ->
                  io:fwrite("div e parameter "),
                  io:fwrite(integer_to_list(fr:decode(M))),
                  io:fwrite("\n"),
                  div_e_parameters(
                    Domain, DA, M)
          end, Domain),
    list_to_tuple(L).

%div_e_parameters(_, _, M) ->
%    parameters2:div_e(M);
div_e_parameters(Domain, DA, M) ->
    Dividends = 
        lists:map(
          fun(D) -> 
                  %X = ?sub2(D, M),
                  X = fr:sub(D, M),
                  case fr:decode(X) of
                      0 -> fr:encode(1);
                      _ -> X
                  end
          end, Domain),
    Dividends2 = 
        lists:zipwith3(
          fun(D, ID, A) ->
                  if
                      (D == M) -> fr:encode(1);
                      true ->
                          fr:mul(A, fr:sub(M, D))
                              %?mul(A, ?sub2(M, D))
                  end
          end, Domain, Dividends, DA),
    {IDs, IDs2} = 
        lists:split(
          length(Dividends),
          fr:batch_inverse(
            Dividends ++ Dividends2)),
    {lists:nth(fr:decode(M), DA),%this only works because the domain is the integers. there should be a way to generalize it. 
     IDs, IDs2}.

lookup_param([], _, _) -> [];
lookup_param([0|T], A, B) -> 
    [1|lookup_param(T, A, B)];
lookup_param([N|T], A, B) when N > 0 ->
    [element(N, A)|lookup_param(T, A, B)];
lookup_param([N|T], A, B) when N < 0 ->
    [element(-N, B)|lookup_param(T, A, B)].

   
%here is the special case where we are dividing the general polynomial A(x) by a polynomial with the form P(x) = x - I, for a constant I. If we evaluate this at 0, P(0) = 0, so the division seems impossible at that point. In this case, we need an alternative formula.
div_e(Ps, Domain, DA, M, DivEAll, DivEAll2) -> 
    %calculates the polynomial P(x) / (x - M).
    %M is a point in the domain of polynomial P.
        
    %DivEAll was generated by all_div_e_parameters(P)
    {DA_M, IDs, IDs2} = 
        if
            true -> element(fr:decode(M), DivEAll);
            true ->
                %to use this version, uncomment these parameters from calc_G_e.
                {IAs, IBs, IDAs} = DivEAll2,
                LookupsA = range(1-M, 256-M),
                LookupsB = 
                    lists:map(
                      fun(X) -> -X end, 
                      LookupsA),
                As = lookup_param(
                       LookupsA, IAs, IBs),
                Bs = lookup_param(
                       LookupsB, IAs, IBs),
                Cs = lists:zipwith(
                       fun(A, B) ->
                               fr:mul(A, B)
                       end, Bs, 
                       tuple_to_list(IDAs)),
                {As, Cs}
        end,
    {Poly1, Zeroth0} =
        div_e3(Ps, 1, IDs, IDs2, fr:decode(M), [], fr:encode(0)),
    %Zeroth = ?mul(Zeroth0, DA_M),
    Zeroth = fr:mul(Zeroth0, DA_M),
    {PolyA, PolyB} = lists:split(fr:decode(M)-1, 
                                 Poly1),
    Result = PolyA ++ [Zeroth] ++ (PolyB),
    Result.

div_e3([], _, [], [], _, Poly, Zero) -> 
    {lists:reverse(Poly), Zero};
div_e3([P|PT], D, [ID1|IDs1], [ID2|IDs2], 
       D, Poly, Zeroth) -> 
    div_e3(PT, D+1, IDs1, IDs2, D, Poly, Zeroth);
div_e3([P|PT], D, [ID1|IDs1], [ID2|IDs2], 
       M, Poly, Zeroth) -> 
    %NZ = ?mul(P, ID2),
    NZ = fr:mul(P, ID2),
    %NP = ?mul(P, ID1),
    NP = fr:mul(P, ID1),
    div_e3(PT, D+1, IDs1, IDs2, M, 
           [NP|Poly], fr:add(Zeroth, NZ)).

calc_A(Domain) -> 
    %in roots of unity case, it is (x^d - 1)
    %only used for generating parameters.
    io:fwrite("calculating the A polynomial\n"),
    L = lists:map(
          fun(D) -> base_polynomial_c(D) 
          end, Domain),
    mul_c_all(L).
calc_DA(Domain) -> 
    %this is the derivative of polynomial A. for some deterministic version of the derivative.
    %in the roots of unity case, A(root_i) is (vector size)*(root^(-i))
    %only used for generating parameters
    io:fwrite("calculating the DA polynomial. 256 elements.\n"),
    X = lists:map(
          fun(D) ->
                  %multiply together all the base polynomials, besides D.
                  io:fwrite(integer_to_list(fr:decode(D))),
                  io:fwrite("\n"),
                  Domain2 = remove_element(D, Domain),
                  Y = lists:map(
                        fun(D2) ->
                                base_polynomial_c(
                                  D2)
                        end, Domain2),
                  mul_c_all(Y)
          end, Domain),
    poly_add_all(X).
    
                          
              
    
%coefficient format
base_polynomial_c(Intercept) ->
    % x - intercept
    [fr:neg(Intercept), fr:encode(1)].
    %[?order - Intercept, 1].

%coefficient format
eval_c(X, P) -> 
    eval_poly2(X, fr:encode(1), P, 
               fr:encode(0)).
eval_poly2(_, _, [], Acc) -> Acc;
eval_poly2(X, XA, [H|T], Acc) ->
    %C = ?mul(H, XA) + Acc,
    C = fr:add(fr:mul(H, XA), Acc),
    eval_poly2(X, fr:mul(X, XA), T, C).


%evaluation format
%todo. maybe lists:nth would be faster.
eval_e(X, [P|_], [X|_]) -> P;
eval_e(X, [_|P], [_|D]) -> 
    eval_e(X, P, D).
eval_e_(N, F, _) ->
    lists:nth(fr:decode(N), F).

%evaluation format, looking up something outside the known domain.
%DA is also in evaluation format
eval_outside_v(Z, Domain, A, DA) ->
    %Z is a point not in domain.
    %A(Z)*sum(P_i/(A'(domain_i) * (z - domain_i)))
    Divisors = 
        lists:zipwith(
          fun(D, Dai) -> fr:mul(Dai, fr:sub(Z, D))
          end, Domain, DA),
    IDs = fr:batch_inverse(Divisors),
    AZ = eval_c(Z, A),
    lists:map(
      fun(D) ->
              %?mul(AZ, D)
              fr:mul(AZ, D)
      end, IDs).
    
eval_outside(Z, P, Domain, A, DA) ->
    %unused. maybe it doesn't work.

    %Z is a point not in domain.
    %A(Z)*sum(P_i/(A'(domain_i) * (z - domain_i)))
    EV = eval_outside_v(Z, Domain, A, DA),
    L = lists:zipwith(
          fun(PE, V) ->
                  %ff:mul(PE, V, Base)
                  %?mul(PE, V)
                  fr:mul(PE, V)
          end, P, EV),
    add_all(L).
    
remove_element(X, [X|T]) -> T;
remove_element(X, [A|T]) -> 
    [A|remove_element(X, T)].

c2e(P, Domain) ->
    %convert to evaluation format
    %cost is (length of polynomial)*(elements in the domain). 
    %currently: O(length(P)^2)
    %can be made faster with the DFT: P*log(P)/2 only if our domain is the roots of unity.
    lists:map(
      fun(X) -> eval_c(X, P) end,
      Domain).

decode_ele({X, L1, L2}) ->
    {fr:decode(X),
     fr:decode(L1),
     fr:decode(L2)}.

lagrange(Z, Domain, DA, DivEAll) ->
    lagrange2(Z, Domain, Domain, DA, DivEAll, fr:encode([1,1,1,1])).
lagrange2(_, [], _, _, _, A) -> A;
lagrange2(Z, [Z|D], Domain, DA, DivEAll, A) -> 
    lagrange2(Z, D, Domain, DA, DivEAll, A);
lagrange2(Z, [H|D], Domain, DA, DivEAll, A) -> 
    B = div_e(base_polynomial_c(H)++fr:encode([0,0]), Domain, DA, Z, DivEAll, 0),
    %io:fwrite({B, A}),
    A2 = lists:zipwith(fun(X, Y) -> fr:add(X, Y) end, A, B),
    %A2 = mul_scalar(A, B),
    %A *= (base_polynomial_c(H) / (Z - H)),
    lagrange2(Z, D, Domain, DA, DivEAll, A2).


test(1) ->    
    Ps = fr:encode([9,12,15,18]),
    Domain = fr:encode([1,2,3,4]),
    %io:fwrite({fr:decode(Domain)}),
    A = calc_A(Domain),
    DA = c2e(calc_DA(Domain), Domain),
    DivEAll = all_div_e_parameters(Domain, DA),

    %div_e should be
    % P(x) / (x - M)

    DM = 2,
    DZ = 5,
    Inv = fr:inv(fr:encode(DZ - DM)),
    %Inv = fr:encode(DZ - DM),

    M = fr:encode(DM),
    Ps2 = div_e(Ps, Domain, DA, M, DivEAll, 0),
    Ps3 = lists:zipwith(
            fun(A, B) ->
                    fr:mul(A, B)
            end, Ps2, c2e(base_polynomial_c(M), Domain)),
    %io:fwrite(fr:decode([Ps2, Ps3])),
    %fr:decode(Ps2).
    Z = fr:encode(DZ),
    EP = eval_outside(Z, Ps, Domain, A, DA),
    EP2 = eval_outside(Z, Ps2, Domain, A, DA),
    %EP3 = fr:mul(EP, Inv),
    EP3 = fr:mul(EP2, fr:encode(DZ - DM)),
    {symetric_view(fr:decode([EP, EP2, EP3]), fr:order())};
test(2) -> 
    Domain = fr:encode([1,2,3,4]),
    A = calc_A(Domain),
    DA = c2e(calc_DA(Domain), Domain),
    C = fr:encode([1,0,0,0]),
    E = c2e(C, Domain),
    %io:fwrite({fr:decode([E])}),
    Z = fr:encode(0),

    Result = eval_c(Z, C),
    Result2 = eval_outside(Z, E, Domain, A, DA),
    Result3 = eval_outside_v(Z, Domain, A, DA),

    %io:fwrite({symetric_view(fr:decode([ipa2:dot(Result3, E), Result, Result2, E]), fr:prime())}),
    success;
test(3) -> 
    %testing mul_c_all
    L = fr:encode(
          [[2,1,0,0],
           [1,1,0,0],
           [0,1,0,0]]),
    %(x+2)(x+1)x = x^3 + 3x^2 + 2x
    [0,2,3,1|_] = fr:decode(mul_c_all(L)),
    success;
test(4) -> 
    io:fwrite("calc_A\n"),
    Domain = [1,2,3,4],
    V1 = symetric_view(
           fr:decode(
             calc_A(
               fr:encode(Domain))), 
           fr:prime()),
    E = secp256k1:make(),
    V2 = symetric_view(
           poly:calc_A(Domain, 
                       secp256k1:order(E)), 
           secp256k1:order(E)),
    V1 = V2,
    success;
test(5) -> 
    io:fwrite("calc_DA\n"),
    Domain = [1,2,3,4],
    V1 = symetric_view(
           fr:decode(
             calc_DA(fr:encode(Domain))),
           fr:prime()),
    E = secp256k1:make(),
    V2 = symetric_view(
           poly:calc_DA(Domain, E), 
           secp256k1:order(E)),
    V1 = V2,
    success;
test(6) -> 
    io:fwrite("deriving eval_outside\n"),
    %f(z) = sum i: f_i * l_i(z)
    %l_i(X) = mul i, j (i != j): 
    %   (X - x_j) / (x_i - x_j)
    Domain = fr:encode([1,2,3,4]),
    DA = c2e(calc_DA(Domain), Domain),
    DivEAll = all_div_e_parameters(Domain, DA),
    fr:decode(lagrange(hd(tl(Domain)), Domain, DA, DivEAll)).
    
    
    
    
