-module(poly).
%-compile(export_all).

-export(
   [calc_DA/2, calc_A/2, 
    c2e/3, %lagrange_polynomials/2, 
    sub/3, div_e/6, mul_scalar/3, mul_scalar/2, 
    add/2, 
    evaluation_add/2,
    eval_e/4, eval_outside/6, eval_outside_v/5,
    all_div_e_parameters/1,
    all_div_e_parameters2/0,
    test/1
   ]).

%library for dealing with polynomials over integers mod a prime.

%finite field operations
%-define(order, 115792089237316195423570985008687907852837564279074904382605163141518161494337).
%-define(sub(A, B), ((A - B + ?order) rem ?order)).%assumes B less than ?order
%-define(neg(A), ((?order - A) rem ?order)).%assumes A less than ?order
%-define(add(A, B), ((A + B) rem ?order)).
%-define(mul(A, B), ((A * B) rem ?order)).
-include("../constants.hrl").

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
    C = A + B,
    [?add_mod(C)|
      add(AT, BT)].
evaluation_add([], []) -> [];
evaluation_add([A|AT], [B|BT]) ->
    C = A + B,
    [?add_mod(C)|
      evaluation_add(AT, BT)].
sub(A, B, Base) ->
    %A and B are polynomials.
    add(A, neg(B, Base)).
neg([], _Base) -> [];
neg([H|T], Base) -> 
    %[ff:sub(0, H, Base)|
    [?neg(H)|
     neg(T, Base)].
mul_scalar(S, A) ->
    mul_scalar(S, A, 0).
mul_scalar(_, [], _) -> [];
mul_scalar(S, [A|T], Base) 
  when is_integer(S) -> 
    %[ff:mul(S, A, Base)|
    [?mul(S, A)|
     mul_scalar(S, T, Base)].
add_all([P]) -> P;
add_all([A, B|T]) -> 
    %add_all([?add(A, B)|T]).
    C = A+B,
    add_all([?add_mod(C)|T]).
mul_c_all([X], _) -> X;
mul_c_all([A, B|T], Base) ->
    mul_c_all([mul_c(A, B, Base)|T], Base).
   
%coefficient format doesn't need to be same length 
add_c([], B, _) -> B;
add_c(B, [], _) -> B;
add_c([A|AT], [B|BT], Base) ->
    %[ff:add(A, B, Base)|
    %[?add(A, B)|
    C = A+B,
    [?add_mod(C)|
      add_c(AT, BT, Base)].

%coefficient form
mul_c([], _B, Base) -> [];
mul_c(_, [], Base) -> [];
mul_c([A], B, Base) ->
    mul_scalar(A, B, Base);
mul_c([A|AT], B, Base) ->
    add_c(mul_scalar(A, B, Base),
        mul_c(AT, [0|B], Base),
        Base).

%execution form
mul_e([], [], _) -> [];
mul_e([A|AT], [B|BT], Base) ->
    [ff:mul(A, B, Base)|
     mul_e(AT, BT, Base)].

range(N, N) -> [N];
range(A, B) when A < B -> 
    [A|range(A+1, B)].

all_div_e_parameters2() ->
    P = ?p,
    D = P#p.domain,
    DA = P#p.da,
    E = P#p.e,
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
                          X -> ?neg(X)
                   end
           end, R),
    L = ff:batch_inverse(As ++ Bs ++ DA, ?order),
    {IAs, L2} = lists:split(length(As), L),
    {IBs, IDA} = lists:split(length(Bs), L2),
    {list_to_tuple(IAs), 
     list_to_tuple(IBs), 
     list_to_tuple(IDA)}.
    
              

all_div_e_parameters(P) ->
    L = lists:map(
          fun(M) ->
                  %io:fwrite("generating parameter "),
                  %io:fwrite(integer_to_list(M)),
                  %io:fwrite("\n"),
                  div_e_parameters(
                    P#p.domain, P#p.da, M)
          end, P#p.domain),
    list_to_tuple(L).

%div_e_parameters(_, _, M) ->
%    parameters:div_e(M);
div_e_parameters(Domain, DA, M) ->
    Dividends = 
        lists:map(
          fun(D) -> 
                  X = ?sub2(D, M),
                  case X of
                      0 -> 1;
                      _ -> X
                  end
          end, Domain),
    Dividends2 = 
        lists:zipwith3(
          fun(D, ID, A) ->
                  if
                      (D == M) -> 1;
                      true ->
                          ?mul(A, ?sub2(M, D))
                  end
          end, Domain, Dividends, DA),
    {IDs, IDs2} = 
        lists:split(
          length(Dividends),
          ff:batch_inverse(
            Dividends ++ Dividends2,
            ?order)),
    {lists:nth(M, DA),%this only works because the domain is the integers. there should be a way to generalize it. 
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
            true -> element(M, DivEAll);
                %parameters:div_e(M);
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
                               ?mul(A, B)
                       end, Bs, 
                       tuple_to_list(IDAs)),
                {As, Cs}
        end,
    {Poly1, Zeroth0} =
        div_e3(Ps, 1, IDs, IDs2, M, [], 0),
    Zeroth = ?mul(Zeroth0, DA_M),
    {PolyA, PolyB} = lists:split(M-1, Poly1),
    Result = PolyA ++ [Zeroth] ++ PolyB,
    Result.

div_e3([], _, [], [], _, Poly, Zero) -> 
    {lists:reverse(Poly), Zero};
div_e3([P|PT], D, [ID1|IDs1], [ID2|IDs2], 
       D, Poly, Zeroth) -> 
    div_e3(PT, D+1, IDs1, IDs2, D, Poly, Zeroth);
div_e3([P|PT], D, [ID1|IDs1], [ID2|IDs2], 
       M, Poly, Zeroth) -> 
    NZ = ?mul(P, ID2),
    NP = ?mul(P, ID1),
    div_e3(PT, D+1, IDs1, IDs2, M, 
           [NP|Poly], Zeroth+NZ).
is_all_zeros([]) -> true;
is_all_zeros([0|T]) -> 
    is_all_zeros(T);
is_all_zeros(_) -> false.
many(_, 0) -> [];
many(X, N) when (N > 0) -> 
    [X|many(X, N-1)].
%coefficient form. 
% O(length(A)*length(B)).
div_c(A, [], _) -> A;%doesn't end a recursion. just a simple case.
div_c(A, B, Base) -> 
    %polynomial long division, doesn't handle remainders.
    D = length(A) - length(B),
    AllZeros = is_all_zeros(A),
    if
        AllZeros -> many(0, max(0, D+1));
        true ->
            if
                D < 0 ->
                    io:fwrite("impossible division\n"),
                    io:fwrite({A, B}),
                    ok;
                true -> ok
            end,
            %io:fwrite({A, B}),
            LA = hd(lists:reverse(A)),
            LB = hd(lists:reverse(B)),
            M = ff:divide(LA, LB, Base),
            BM = mul_scalar(M, B, Base),
            %BM2 = all_zeros(D) ++ BM,
            BM2 = many(0, D) ++ BM,
            A2 = sub(A, BM2, Base),
           %A3 = remove_trailing_zeros(A2),
            A3 = lists:reverse(tl(lists:reverse(A2))),
    %io:fwrite({A, B, M, A2, A3}),
    %io:fwrite({A, BM2, A2}),
            %io:fwrite({A3, B}),
            div_c(A3, B, Base) ++ [M]
    end.


calc_A(Domain, Base) -> 
    %in roots of unity case, it is (x^d - 1)
    L = lists:map(
          fun(D) -> base_polynomial_c(D, Base) 
          end, Domain),
    mul_c_all(L, Base).
calc_DA(Domain, E) -> 
    %this is the derivative of polynomial A. for some deterministic version of the derivative.
    %in the roots of unity case, A(root_i) is (vector size)*(root^(-i))
    Base = secp256k1:order(E),
    X = lists:map(
          fun(D) ->
                  %multiply together all the base polynomials, besides D.
                  Domain2 = remove_element(D, Domain),
                  Y = lists:map(
                        fun(D2) ->
                                base_polynomial_c(
                                  D2, Base)
                        end, Domain2),
                  mul_c_all(Y, Base)
          end, Domain),
    lists:foldl(fun(A, B) -> add_c(A, B, Base) end,
              hd(X), tl(X)).
%    add_all(X).
    
                          
              
    
%coefficient format
base_polynomial_c(Intercept, Base) ->
    % x - intercept
    %[ff:sub(0, Intercept, Base), 1].
    [?order - Intercept, 1].

%coefficient format
eval_c(X, P, Base) -> 
    eval_poly2(X, 1, P, Base, 0).
eval_poly2(_, _, [], _, Acc) -> Acc;
eval_poly2(X, XA, [H|T], Base, Acc) ->
    C = ?mul(H, XA) + Acc,
    eval_poly2(X, ?mul(X, XA), T, Base,
               ?add_mod(C)).


%evaluation format
eval_e(X, [P|_], [X|_], Base) -> P;
eval_e(X, [_|P], [_|D], Base) -> 
    eval_e(X, P, D, Base).

%evaluation format, looking up something outside the known domain.
%DA is also in evaluation format
eval_outside_v(Z, Domain, A, DA, Base) ->
    AZ = eval_c(Z, A, Base),
    Divisors = 
        lists:zipwith(
          fun(D, Dai) -> ?mul(Dai, ?sub2(Z, D))
          end, Domain, DA),
    IDs = ff:batch_inverse(Divisors, Base),
    lists:map(
      fun(D) ->
              ?mul(AZ, D)
      end, IDs).
    
eval_outside(Z, P, Domain, A, DA, Base) ->
    %Z is a point not in domain.
    %A(Z)*sum(P_i/(A'(domain_i) * (z - domain_i)))
    EV = eval_outside_v(Z, Domain, A, DA, Base),
    L = lists:zipwith(
          fun(PE, V) ->
                  %ff:mul(PE, V, Base)
                  ?mul(PE, V)
          end, P, EV),
    add_all(L).
    
remove_element(X, [X|T]) -> T;
remove_element(X, [A|T]) -> 
    [A|remove_element(X, T)].

c2e(P, Domain, Base) ->
    %coefficient format to evaluation format
    %cost is (length of polynomial)*(elements in the domain). 
    %currently: O(length(P)^2)
    %can be made faster with the DFT: P*log(P)/2 only if our domain is the roots of unity.
    lists:map(
      fun(X) -> eval_c(X, P, Base) end,
      Domain).

test(1) ->    
    %Ps = [12,24,36,48],
    Ps = [48,48,48,48],
    Domain = [1,2,3,4],
    A = calc_A(Domain, ?order),
    E = secp256k1:make(),
    DA = calc_DA(Domain, E),
%-record(p, {e, b, g, h, q, domain, a, da, ls}).
    P = {p, E,0,0,0,0,Domain, A, DA, 0},
    DivEAll = all_div_e_parameters(P),

    M = 2,
    Z = 5,
    %Inv = ff:inverse(Z-M, ?order),
   
    %Ps(X) / (X-3)
    Ps2 = div_e(Ps, Domain, DA, M, DivEAll, 0),
    %Ps3 = div_e(Ps2, Domain, DA, M, DivEAll, 0),
    Ps3 = lists:zipwith(
           fun(A, B) ->
                   ?mul(A, B)
           end, Ps2, c2e(base_polynomial_c(M, ?order), Domain, ?order)),
    io:fwrite({Ps2, c2e(base_polynomial_c(M, ?order), Domain, ?order), Ps3}),
    EP = eval_outside(Z, Ps, Domain, A, DA, ?order),
    EP2 = eval_outside(Z, Ps3, Domain, A, DA, ?order),%EP(X) / (X-M)
    EP3 = (EP2 * (Z-M)) rem ?order,
    [Ps, symetric_view(Ps2, ?order), 
     symetric_view(Ps3, ?order),
     ?order,
     ?order div 2,
    symetric_view(EP, ?order),
     symetric_view(EP2, ?order)];
test(2) -> 
    Domain = [1,2,3,4],
    Curve = secp256k1:make(),
    A = calc_A(Domain, ?order),
    DA = c2e(calc_DA(Domain, Curve), Domain, ?order),
    P = {p, Curve,0,0,0,0,Domain, A, DA, 0},
    C = [1,0,0,0],
    E = c2e(C, Domain, ?order),
    Z = 5,
    
    Result = eval_c(Z, C, ?order),
    Result2 = eval_outside(Z, E, Domain, A, DA, ?order),
    Result3 = eval_outside_v(Z, Domain, A, DA, ?order),
    io:fwrite({symetric_view([ipa:dot(E, Result3), Result, Result2, E], ?order)}),
    success;
test(3) -> 
    E = secp256k1:make(),
    Base = secp256k1:order(E),
    Domain = [1,2,3],
    P1 = base_polynomial_c(2, Base),
    P2 = base_polynomial_c(3, Base),
    P3 = mul_c(P1, P2, Base),
    
    P1 = div_c(P3, P2, Base),
    P2 = div_c(P3, P1, Base),

    P1b = c2e(P1, Domain, Base), 
    P2b = c2e(P2, Domain, Base), 
    P3b = c2e(P3, Domain, Base), 
    P3b = mul_e(P1b, P2b, Base),

    DAC = calc_DA(Domain, E),
    DA = c2e(DAC, Domain, Base),
    %P1b = div_e(P3b, Domain, DA, 3, Base),
    %P2b = div_e(P3b, Domain, DA, 2, Base),
    DivEAll = all_div_e_parameters(ok),
    P1b = div_e(P3b, Domain, DA, 3, DivEAll, 0),
    P2b = div_e(P3b, Domain, DA, 2, DivEAll, 0),

    PA = calc_A(Domain, Base),
    P5 = eval_outside(5, P3b, Domain, PA, DA, Base),
    P5 = eval_c(5, P3, Base),
    
    success.
    

