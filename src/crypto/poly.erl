-module(poly).
%-compile(export_all).

-export(
   [calc_DA/2, calc_A/2, 
    c2e/3, %lagrange_polynomials/2, 
    sub/3, div_e/5, mul_scalar/3, add/2, 
    eval_e/4, eval_outside/6, eval_outside_v/5]).

%library for dealing with polynomials over integers mod a prime.

%finite field operations
-define(order, 115792089237316195423570985008687907852837564279074904382605163141518161494337).
-define(sub(A, B), ((A - B + ?order) rem ?order)).%assumes B less than ?order
-define(neg(A), ((?order - A) rem ?order)).%assumes A less than ?order
-define(add(A, B), ((A + B) rem ?order)).
-define(mul(A, B), ((A * B) rem ?order)).

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
add([], X) -> X;
add(X, []) -> X;
add([A|AT], [B|BT]) ->
    [?add(A, B)|
      add(AT, BT)].
sub(A, B, Base) ->
    %add(A, ?neg(B), Base).
    %?add(A, ?neg(B)).
    add(A, neg(B, Base)).
neg([], _Base) -> [];
neg([H|T], Base) -> 
    %[ff:sub(0, H, Base)|
    [?neg(H)|
     neg(T, Base)].
mul_scalar(_, [], _) -> [];
mul_scalar(S, [A|T], Base) 
  when is_integer(S) -> 
    %[ff:mul(S, A, Base)|
    [?mul(S, A)|
     mul_scalar(S, T, Base)].
add_all([P], _) -> P;
add_all([A, B|T], Base) -> 
    add_all([?add(A, B)|T], Base).
mul_c_all([X], _) -> X;
mul_c_all([A, B|T], Base) ->
    mul_c_all([mul_c(A, B, Base)|T], Base).
   
%coefficient format doesn't need to be same length 
add_c([], B, _) -> B;
add_c(B, [], _) -> B;
add_c([A|AT], [B|BT], Base) ->
    %[ff:add(A, B, Base)|
    [?add(A, B)|
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

%evaluation format
%assumes that the division is possible without a remainder.
%if B contains no zero, it is easy:
%unused_div_e([], [], _Base) -> [];
%unused_div_e([A|AT], [B|BT], Base) ->
%    [ff:divide(A, B, Base)|
%     unused_div_e(AT, BT, Base)].

%here is the special case where we are dividing the general polynomial A(x) by a polynomial with the form P(x) = x - I, for a constant I. If we evaluate this at 0, P(0) = 0, so the division seems impossible at that point. In this case, we need an alternative formula.
div_e(Ps, Domain, DA, M, Base) -> 
    %calculates the polynomial P(x) / (x - M).
    %M is a point in the domain of polynomial P.
    %io:fwrite({Ps, DA, M}),
    Dividends = 
        lists:map(
          fun(D) -> 
                  X = ?sub(D, M),
                  case X of
                      0 -> 1;
                      _ -> X
                  end
          end, Domain),
    IDs = ff:batch_inverse(Dividends, ?order),
    %todo. can't we pre-calculate these IDs??
          
    lists:zipwith3(
      fun(P, D, ID) -> 
              if
                  not(D == M) -> ?mul(P, ID);
                  true -> 
                      DA_M = grab_dam(
                               M, Domain, DA),
                      div_e2(Ps, Domain, M, 
                             DA, DA_M, Base)
              end
      end, Ps, Domain, IDs).
div_e2(Ps, Domain, M, DA, DA_M, Base) ->
    Divisors = 
        lists:zipwith(
          fun(D, A) ->
                  if
                      (D == M) -> 1;
                      true ->
                          ?mul(A, ?sub(M, D))
                  end
          end, Domain, DA),
    IDs = ff:batch_inverse(Divisors, Base),
    X = lists:zipwith3(
          fun(P, D, ID) ->
                  if
                      (D == M) -> 0;
                      true -> ?mul(P, ID)
                  end
          end, Ps, Domain, IDs),
    X2 = ff:add_all(X, Base),
    ?mul(X2, DA_M).

grab_dam(M, [M|_], [D|_]) -> D;
grab_dam(M, [_|T], [_|D]) -> 
    grab_dam(M, T, D).
   
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
    add_all(X, Base).
    
                          
              
    
%coefficient format
base_polynomial_c(Intercept, Base) ->
    % x - intercept
    %[ff:sub(0, Intercept, Base), 1].
    [?order - Intercept, 1].

%coefficient format
eval_c(X, P, Base) -> 
    eval_poly2(X, 1, P, Base).
eval_poly2(_, _, [], _) -> 0;
eval_poly2(X, XA, [H|T], Base) ->
    ?add(?mul(H, XA),
         eval_poly2(X, ?mul(X, XA), T, Base)).

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
          fun(D, Dai) -> ?mul(Dai, ?sub(Z, D))
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
    ff:add_all(L, Base).
    

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

    
    
