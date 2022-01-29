-module(poly2).

-export(
   [calc_DA/1, calc_A/1, 
    c2e/3, %lagrange_polynomials/2, 
    sub/3, div_e/6, mul_scalar/2, 
    add/2, 
    eval_e/3, eval_outside/6, eval_outside_v/5,
    all_div_e_parameters/2
   ]).

%library for dealing with polynomials over integers mod a prime.
%Built over the jubjub curve

%finite field operations
%-define(order, 115792089237316195423570985008687907852837564279074904382605163141518161494337).
%-define(sub(A, B), ((A - B + ?order) rem ?order)).%assumes B less than ?order
%-define(neg(A), ((?order - A) rem ?order)).%assumes A less than ?order
%-define(add(A, B), ((A + B) rem ?order)).
%-define(mul(A, B), ((A * B) rem ?order)).
%-include("../constants.hrl").

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
sub(A, B, Base) ->
    %A and B are polynomials.
    add(A, neg(B, Base)).
neg([], _Base) -> [];
neg([H|T], Base) -> 
    %[ff:sub(0, H, Base)|
    [fr:neg(H)|
     neg(T, Base)].
mul_scalar(_, []) -> [];
mul_scalar(S, [A|T]) ->
    %scalar * polynomial
    [fr:mul(S, A)|
     mul_scalar(S, T)].
add_all([P]) -> P;
add_all([A, B|T]) -> 
    %add_all([?add(A, B)|T]).
    %C = A+B,
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

%coefficient form
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
    %[?add(A, B)|
%    C = A+B,
%    [?add_mod(C)|
%      add_c(AT, BT, Base)].


range(N, N) -> [N];
range(A, B) when A < B -> 
    [A|range(A+1, B)].

all_div_e_parameters2(Domain, DA) ->
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
%    parameters:div_e(M);
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
                               fr:mul(A, B)
                       end, Bs, 
                       tuple_to_list(IDAs)),
                {As, Cs}
        end,
    {Poly1, Zeroth0} =
        div_e3(Ps, 1, IDs, IDs2, M, [], 0),
    %Zeroth = ?mul(Zeroth0, DA_M),
    Zeroth = fr:mul(Zeroth0, DA_M),
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
eval_c(X, P, Base) -> 
    eval_poly2(X, fr:encode(1), P, 
               Base, fr:encode(0)).
eval_poly2(_, _, [], _, Acc) -> Acc;
eval_poly2(X, XA, [H|T], Base, Acc) ->
    %C = ?mul(H, XA) + Acc,
    C = fr:add(fr:mul(H, XA), Acc),
    eval_poly2(X, fr:mul(X, XA), T, Base, C).


%evaluation format
%todo. maybe lists:nth would be faster.
eval_e(X, [P|_], [X|_]) -> P;
eval_e(X, [_|P], [_|D]) -> 
    eval_e(X, P, D).

%evaluation format, looking up something outside the known domain.
%DA is also in evaluation format
eval_outside_v(Z, Domain, A, DA, Base) ->
    AZ = eval_c(Z, A, Base),
    Divisors = 
        lists:zipwith(
          %fun(D, Dai) -> ?mul(Dai, ?sub2(Z, D))
          fun(D, Dai) -> fr:mul(Dai, fr:sub(Z, D))
          end, Domain, DA),
    IDs = fr:batch_inverse(Divisors),
    lists:map(
      fun(D) ->
              %?mul(AZ, D)
              fr:mul(AZ, D)
      end, IDs).
    
eval_outside(Z, P, Domain, A, DA, Base) ->
    %Z is a point not in domain.
    %A(Z)*sum(P_i/(A'(domain_i) * (z - domain_i)))
    EV = eval_outside_v(Z, Domain, A, DA, Base),
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

c2e(P, Domain, Base) ->
    %cost is (length of polynomial)*(elements in the domain). 
    %currently: O(length(P)^2)
    %can be made faster with the DFT: P*log(P)/2 only if our domain is the roots of unity.
    lists:map(
      fun(X) -> eval_c(X, P, Base) end,
      Domain).

    
    
