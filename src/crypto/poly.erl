-module(poly).
%-compile(export_all).

-export(
   [calc_DA/2, calc_A/2, 
    c2e/3, lagrange_polynomials/2, 
    sub/3, div_e/5, mul_scalar/3, add/3, 
    eval_e/4, eval_outside/6, eval_outside_v/5]).

%library for dealing with polynomials over integers mod a prime.

%finite field operations
-define(order, 115792089237316195423570985008687907852837564279074904382605163141518161494337).
-define(sub(A, B), ((A - B + ?order) rem ?order)).%assumes B less than ?order
-define(neg(A), ((?order - A) rem ?order)).%assumes A less than ?order
-define(add(A, B), ((A + B) rem ?order)).
-define(mul(A, B), ((A * B) rem ?order)).

mod(X,Y)->(X rem Y + Y) rem Y.
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
%fadd(A, B, N) ->
%    mod(A+B, N).
%fadd_all([A], _) -> A;
%fadd_all([A, B|T], Base) -> 
%    fadd_all([fadd(A, B, Base)|T], Base).
inverse(X, Base) ->
    basics:inverse(X, Base).

%elliptic operations
order(E) -> secp256k1:order(E).
eadd(A, B, E) ->
    secp256k1:addition(A, B, E).
emul(X, Y, E) when is_integer(Y) ->
    secp256k1:multiplication(X, Y, E).
eadd_all(V, E) ->
    lists:foldl(fun(A, B) -> 
                        eadd(A, B, E) end,
                %infinity, V).
                {0,0}, V).

%polynomial operations
add([], [], _) -> [];
add([A|AT], [B|BT], Base) ->
    [ff:add(A, B, Base)|
      add(AT, BT, Base)].
sub(A, B, Base) ->
    add(A, neg(B, Base), Base).
neg([], _Base) -> [];
neg([H|T], Base) -> 
    [ff:sub(0, H, Base)|
     neg(T, Base)].
mul_scalar(_, [], _) -> [];
mul_scalar(S, [A|T], Base) 
  when is_integer(S) -> 
    [ff:mul(S, A, Base)|
     mul_scalar(S, T, Base)].
add_all([P], _) -> P;
add_all([A, B|T], Base) -> 
    add_all([add(A, B, Base)|T], Base).
mul_c_all([X], _) -> X;
mul_c_all([A, B|T], Base) ->
    mul_c_all([mul_c(A, B, Base)|T], Base).
   
%coefficient format doesn't need to be same length 
add_c([], B, _) -> B;
add_c(B, [], _) -> B;
add_c([A|AT], [B|BT], Base) ->
    [ff:add(A, B, Base)|
      add_c(AT, BT, Base)].

%evaluation form
mul_e([], [], _) -> [];
mul_e([A|AT], [B|BT], Base) ->
    [ff:mul(A, B, Base)|
     mul_e(AT, BT, Base)].

%coefficient form
mul_c([], _B, Base) -> [];
mul_c(_, [], Base) -> [];
mul_c([A], B, Base) ->
    mul_scalar(A, B, Base);
mul_c([A|AT], B, Base) ->
    add_c(mul_scalar(A, B, Base),
        mul_c(AT, [0|B], Base),
        Base).

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

%evaluation format
%assumes that the division is possible without a remainder.
%if B contains no zero, it is easy:
%unused_div_e([], [], _Base) -> [];
%unused_div_e([A|AT], [B|BT], Base) ->
%    [ff:divide(A, B, Base)|
%     unused_div_e(AT, BT, Base)].

remove_from([X|T], X) -> T;
remove_from([A|T], X) -> 
    [A|remove_from(T, X)].

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
    ff:add(ff:mul(H, XA, Base),
         eval_poly2(
           X, ff:mul(X, XA, Base), T, Base),
         Base).

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
                  ff:mul(PE, V, Base)
          end, P, EV),
    ff:add_all(L, Base).
    

remove_element(X, [X|T]) -> T;
remove_element(X, [A|T]) -> 
    [A|remove_element(X, T)].
lagrange_polynomials(R, Base) 
  when is_list(R) ->
    lists:map(fun(X) -> 
                      lagrange_polynomial(
                        R, X, Base)
              end, R).
lagrange_polynomial(R, N, Base) ->
    R2 = remove_element(N, R),
    Ps = lists:map(
           fun(X) -> base_polynomial_c(X, Base) end, 
           R2),
    P = lists:foldl(
          fun(X, A) -> mul_c(X, A, Base) end, 
          [1], Ps),
    Ds = lists:map(
           fun(X) -> ff:sub(N, X, Base) end, 
           R2),
    D = lists:foldl(
          fun(X, A) -> ff:mul(X, A, Base) end, 
          1, Ds),
    %io:fwrite({D, P}),
    mul_scalar(inverse(D, Base), P,  Base).
%div_c(D, P, Base).

c2e(P, Domain, Base) ->
    %cost is (length of polynomial)*(elements in the domain). 
    %currently: O(length(P)^2)
    %can be made faster with the DFT: P*log(P)/2 only if our domain is the roots of unity.
    lists:map(
      fun(X) -> eval_c(X, P, Base) end,
      Domain).
%e2c(P, Domain, Base) ->
e2c(P, Ls, Base) ->
    %cost is (elements in polynomial)*(elements in the domain).
    %currently: O(length(P)^2)
    %can be made faster with the inverse DFT: P*log(P)/2 only if our domain is the roots of unity.
    %Ls = lagrange_polynomials(Domain, Base),
    Ps = lists:zipwith(
           fun(X, L) ->
                   mul_scalar(X, L, Base)
           end, P, Ls),
    add_all(Ps, Base).

powers(X, N, Base) ->
    powers2(X, 1, N, Base).
powers2(_, _, 0, _) -> [];
powers2(X, A, N, Base) ->
    [A|powers2(X, ff:mul(A, X, Base), N-1, Base)].

%coefficient format
commit_c(P, Gs, E) 
  when length(P) == length(Gs) ->
    pedersen:commit(P, Gs, E);
commit_c(P, Gs, E) 
  when length(P) < length(Gs) ->
    commit_c(P++[0], Gs, E).


%evaluation format
commit_e(P, Gs, Domain, E) ->
    Base = secp256k1:order(E),
    Ls = lagrange_polynomials(Domain, Base),
    Ls2 = lists:map(
            fun(L) -> commit_c(L, Gs, E) end,
            Ls),
    P2 = lists:zipwith(
           fun(X, L) -> emul(L, X, E) end,
           P, Ls2),
    eadd_all(P2, E).

    
test() ->                      
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
    P1b = div_e(P3b, Domain, DA, 3, Base),
    P2b = div_e(P3b, Domain, DA, 2, Base),

    PA = calc_A(Domain, Base),
    P5 = eval_outside(5, P3b, Domain, PA, DA, Base),
    P5 = eval_c(5, P3, Base),
    
    success.
    
    
