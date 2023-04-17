-module(basics).
-export([%gcd_euclid/2, gcd_binary/2,
         %to_bits_list/1,
         %eea/2, 
         lrpow/3, rlpow/3,
         inverse/2, %inverse_fermat/2,
         %inverse_euler/2,
         %is_prime/1,
         %prime_factors/1,
         %carmichael/1,
         %carmichael_number/1,
         test/0
        ]).

%Algorithms from the book "Partially Homomorphic Encryption", by Cetin Kaya Koc, Funda Ozdemir, and Zeynep Odemis Ozger.

divides(A, B) ->
    (B rem A) == 0.

gcd_euclid(A, B) when
      ((A < 0) or (B < 0)) ->
    undefined;
gcd_euclid(A, 0) -> A;
gcd_euclid(A, B) when A < B -> 
    gcd_euclid(B, A);
gcd_euclid(A, B) -> 
    gcd_euclid(B, A rem B).

gcd_binary(A, B) 
  when ((A < 0) or (B < 0)) ->
    undefined;
gcd_binary(A, 0) -> A;
gcd_binary(0, B) -> B;
gcd_binary(A, B) 
  when (((A rem 2) == 0) and
        ((B rem 2) == 0)) ->
    2 * gcd_binary(A div 2, B div 2);
gcd_binary(A, B)
  when ((A rem 2) == 0) ->
    gcd_binary(A div 2, B);
gcd_binary(A, B)
  when ((B rem 2) == 0) ->
    gcd_binary(A, B div 2);
gcd_binary(A, B) ->
    gcd_binary(
      abs(A - B),
      min(A, B)).

relatively_prime(A, B) ->
    (gcd_euclid(A, B)) == 1.

%bezout coefficients for A and B are S and T
%  such that (S*A) + (T*B) = gcd(A, B)
% Extended Euclidean Algorithm finds S and T.
eea(A, B)
  when ((A < 1) 
        or (B < 1)) ->
    undefined;
eea(A, B) ->
    eea_helper(A, 1, 0, B, 0, 1).
eea_helper(G, S, T, 0, _, _) ->
    {G, S, T};
eea_helper(G0, S0, T0, G1, S1, T1) ->
    Q = G0 div G1,
    eea_helper(G1, S1, T1, 
               G0 - (Q*G1),
               S0 - (Q*S1),
               T0 - (Q*T1)).

%modular exponentiation with the binary method.
%first left to right
to_bits_list(0) -> [];
to_bits_list(N) ->
    B = N rem 2,
    [(N rem 2)|to_bits_list(N div 2)].
lrpow(0, _, _) -> 0;
lrpow(_, 0, _) -> 1;
lrpow(B, E, N) ->
    % math:pow(B, E) rem N
    E2 = lists:reverse(
           to_bits_list(E)),
    A = case hd(E2) of
            1 -> B;
            0 -> 1
        end,
    lrpow2(A, B, tl(E2), N).
lrpow2(A, _, [], _) -> A;
lrpow2(A, B, [H|T], N) -> 
    %io:fwrite("square\n"),
    A2 = (A * A) rem N,
    A3 = if
             (H == 1) ->
                 %io:fwrite("mul\n"),
                 (A2 * B) rem N;
             true -> A2
         end,
    lrpow2(A3, B, T, N).

%now right to left
rlpow(0, _, _) -> 0;
rlpow(_, 0, _) -> 1;
rlpow(B, E, N) ->
    % math:pow(B, E) rem N
    E2 = to_bits_list(E),
    rlpow2(1, B, E2, N).
rlpow2(A, _, [0], _) -> A;
rlpow2(A, C, [1], N) -> 
    (A * C) rem N;
rlpow2(A, C, [1|T], N) -> 
    rlpow2((A*C) rem N,
           (C*C) rem N, 
           T, N);
rlpow2(A, C, [0|T], N) -> 
    rlpow2(A,
           (C*C) rem N, 
           T, N).
            
%multiplicative inverse using EEA
inverse(A, N) ->    
    EEA = eea(A, N),
    case EEA of
        undefined -> 
            io:fwrite("inverse does not exist "),
            io:fwrite(integer_to_list(A)),
            io:fwrite("\n"),
            1=2,
            does_not_exist;
        {G, S, T} ->
            case G of
                1 -> (S + N) rem N;
                _ -> 
                    io:fwrite("inverse does not exist"),
                    does_not_exist
            end
    end.

%multiplicative inverse using fermat
%requires that A is relatively prime to P, and that P is prime.
inverse_fermat(A, P) ->
    1 = gcd_euclid(A, P),%checking they are relatively prime.
    true = is_prime(P),%checking that P is prime
    lrpow(A, P-2, P).

prime_factors(N) ->
    prime_factors2([], 2, N).
prime_factors2(A, _, 1) -> lists:reverse(A);
prime_factors2([[C, E]|T], C, N) 
  when ((N rem C) == 0) -> 
    io:fwrite(integer_to_list(C)),
    io:fwrite("\n"),
    prime_factors2([[C, E+1]|T], C, N div C);
prime_factors2(T, C, N) 
  when ((N rem C) == 0) -> 
    io:fwrite(integer_to_list(C)),
    io:fwrite("\n"),
    prime_factors2([[C, 1]|T], C, N div C);
prime_factors2(T, C, N) ->
    prime_factors2(T, C+1, N).
    
eulers_phi(N) ->
    eulers_phi2(prime_factors(N), 1).
eulers_phi2([], Acc) -> Acc;
eulers_phi2([[P, E]|T], Acc) -> 
    Acc2 = Acc * 
        (P - 1) * 
        round(math:pow(P, E-1)),
    eulers_phi2(T, Acc2).

%multiplicative inverse using euler's phi.
inverse_euler(A, N) ->
    1 = gcd_binary(A, N),
    lrpow(A, eulers_phi(N)-1, N).
      
%checking primality by trial division.      
is_prime(N) when (N < 1) ->
    undefined;
is_prime(N) 
  when ((N rem 2) == 0) ->
    false;
is_prime(N) ->
    S = floor(math:sqrt(N)),
    is_prime2(3, S, N).
is_prime2(C, L, N) when (C > L) ->
    true;
is_prime2(C, L, N) 
  when ((N rem C) == 0) ->
    false;
is_prime2(C, L, N) ->
    is_prime2(C+2, L, N).

lcm(A, B) ->
    A * B div gcd_euclid(A, B).
lcm([X]) -> X;
lcm([A, B|T]) -> 
    lcm([lcm(A, B)|T]).

carmichael(N) ->
    F = fun([P, E]) ->
                Phi = eulers_phi2([[P, E]], 1),
                if
                    ((P == 2) 
                     and (E > 2)) -> Phi;
                    true -> Phi div 2
                end
        end,
    Cs = lists:map(F, prime_factors(N)),
    lcm(Cs).
carmichael_number(N) ->
    divides(carmichael(N), N-1).

%ord(A, N) ->
    %return E. E is the smallest positive integer where A^E == 1 in Z_N
%    ok.

%is_generator(A, N) ->
%    1 = gcd_binary(A, N),
%    ord(A, N) == eulers_phi(N).

%chinese remainder algorithm
cra(Rs, Ns) ->
    %remainders [r_1, r_2, ... , r_k]
    %moduli [n_1, n_2, ... , n_k]
    N = lists:foldl(fun(A, B) -> A * B end,
                    1, Ns),
    M = lists:map(fun(X) -> 
                          Y = N div X,
                          {Y, inverse(Y, X)}
                  end, Ns),
    cra2(Rs, M, N, 0).
cra2([], [], N, X) -> X rem N;
cra2([R|RT], [{M, C}|MT], N, X) ->
    cra2(RT, MT, N, (X + (R*M*C)) rem N).

eulers_criterion(A, P) ->
    %returns true if A is a quadratic residue.
    %returns true if A has a square root in mod P.
    true = is_prime(P),
    true = 1 == P rem 2,
    C = rlpow(A, (P-1) div 2, P),
    P2 = P-1,
    case C of
        1 -> true;
        P2 -> false
    end.

legendre_symbol(A, P) ->
    B = ((A rem P) == 0),
    if
        B -> 0;
        true ->
            B2 = eulers_criterion(A, P),
            if
                B2 -> 1;
                true -> -1
            end
    end.
                    
            
            


test() ->
    V = 3,
    Exp = 100,
    P = 101,
    true = (rlpow(V, Exp, P) == lrpow(V, Exp, P)),
    12 = inverse(23, 25),
    12 = inverse_euler(23, 25),
    4 = inverse_fermat(3, 11),
    true = carmichael_number(561),
    false = carmichael_number(560),
    false = carmichael_number(559),
    false = carmichael_number(123),
    10880 = cra([5, 12, 2], [15, 22, 49]),
    success.
    
