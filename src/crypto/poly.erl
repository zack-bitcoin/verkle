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
    all_div_e_parameters2/0
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
    %[?add(A, B)|
    C = A + B,
    [?add_mod(C)|
      add(AT, BT)].
evaluation_add([], []) -> [];
evaluation_add([A|AT], [B|BT]) ->
    %[?add(A, B)|
    C = A+B,
    [?add_mod(C)|
      evaluation_add(AT, BT)].
sub(A, B, Base) ->
    %add(A, ?neg(B), Base).
    %?add(A, ?neg(B)).
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
    add_all(X).
    
                          
              
    
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
    %cost is (length of polynomial)*(elements in the domain). 
    %currently: O(length(P)^2)
    %can be made faster with the DFT: P*log(P)/2 only if our domain is the roots of unity.
    lists:map(
      fun(X) -> eval_c(X, P, Base) end,
      Domain).

    
    
