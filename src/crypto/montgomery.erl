-module(montgomery).
-export([prime_reverse/1, test/1, encode/1]).

%a clearer example of montgomery multiplication.

%2^256
-define(r, 115792089237316195423570985008687907853269984665640564039457584007913129639936).
-define(r_bits, 256).
-define(r_bits2, 512).

%for the finite field prime jubjub is defined under.
-define(jubjub_q, 52435875175126190479447740508185965837690552500527637822603658699938581184513).
-define(ed25519_q, 57896044618658097711785492504343953926634992332820282019728792003956564819949).

-define(simple_prime, 23).

%-define(n, ?jubjub_q).
-define(n, ?ed25519_q).

% in * n = -1 rem r
-define(in, 21330121701610878104342023554231983025602365596302209165163239159352418617883).
%27711634432943687283656245953990505159342029877880134060146103271536583507967).
        %15103315987476025490030998044611466241730867565083551831233597914075625605209).

%1/r rem n
-define(ir, 10665060850805439052171011777115991512801182798151104582581619579676209308938).
        %3).

%r rem n
-define(r1, 38).
%10920338887063814464675503992315976177888879664585288394250266608035967270910).
        %8).

%r*r rem n
-define(r2, 1444).
%3294906474794265442129797520630710739278575682199800681788903916070560242797).
        %18).

check_constants() -> 
    ?in = prime_reverse(?n),
    true = ?r > ?n,
    1 = (?n rem 2),
    true = power_of_2(?r),
    ?r1 = (?r rem ?n),
    ?r2 = ((?r * ?r) rem ?n),
    ?ir = ff:inverse(?r, ?n).
prime_reverse(N) ->
    %Used to calculate the IN input for redc.
    (?r - 1)*ff:inverse(N, ?r) rem ?r.
power_of_2(1) -> true;
power_of_2(N) when ((N rem 2) == 0) -> 
    power_of_2(N div 2);
power_of_2(_) -> false.



%montgomery reduction.
redc(T) -> redc(?r, ?n, ?in, T).
redc(R, N, IN, T) ->
     %R and N need to be coprime.
     %IN * N rem R needs to be -1.
     %IN is in [0, R)
     %T is in [0, RN)

     %returns S in [0, N] such that S = T/R rem N.
    <<Tb:?r_bits>> = <<T:?r_bits>>,
    <<M:?r_bits>> = <<(Tb*IN):?r_bits>>,
    %<<M:?r_bits>> = <<(T*IN):?r_bits>>,
    <<T2:?r_bits, _/binary>> = <<(T + (M*N)):?r_bits2>>,
    %M = ((T rem R)*IN) rem R,
    %T2 = (T + (M*N)) div R,
    if
        (T2 >= N) -> T2 - N;
        true -> T2
    end.

multiply(A, B) ->
    %X = (A * B * ?ir) rem ?n,
    redc(A*B).
    %X = Y.
    %Y.

encode(A) when ((A < ?n) and (A > -1)) ->
    %redc((a mod n)(r*r mod n))
    redc(?r2 * A).
decode(A) ->
    %redc((A*R) rem N).
    %redc((?r1 * A) rem ?n).
    %ok.
    multiply(A, 1).




  
many(_, 0) -> [];
many(X, N) when N > 0 -> 
    [X|many(X, N-1)].

range(N, N) -> [N];
range(A, B) when (A < B) -> 
    [A|range(A+1, B)].

test(1) ->
    check_constants(),
    A = 2,
    B = 3,
    C = 5,
    D = 22,
    {((A*B) rem ?n) == decode(multiply(encode(A), encode(B))),
     ((C*D) rem ?n) == decode(multiply(encode(C), encode(D))),
     C == decode(encode(C))};
test(2) ->
    %speed test
    {true, true, true} = test(1),
    Many = 100000,
    <<A0:256>> = crypto:strong_rand_bytes(32),
    <<B0:256>> = crypto:strong_rand_bytes(32),
    <<C0:256>> = crypto:strong_rand_bytes(32),
    A = A0 rem ?n,
    B = B0 rem ?n,
    C = C0 rem ?n,
    AM = encode(A),
    BM = encode(B),
    T1 = erlang:timestamp(),
    lists:map(fun(X) ->
                      ((A+X)*(B+X)) rem ?n
              end, range(0, Many)),
    T2 = erlang:timestamp(),
    lists:map(fun(X) ->
                      multiply((AM+X), (BM+X))
                      %redc((AM+X)*(BM+X))
              end, range(0, Many)),
    T3 = erlang:timestamp(),
    lists:map(fun(X) ->
                      (A+X)*(B+X)
              end, range(0, Many)),
    T4 = erlang:timestamp(),
    true = ((A*B) rem ?n) == decode(multiply(AM, BM)),
    Normal = timer:now_diff(T2, T1)/Many,
    Montgomery = timer:now_diff(T3, T2)/Many,
    Empty = timer:now_diff(T4, T3)/Many,
    {{normal, Normal-Empty},
     {montgomery, Montgomery-Empty},
     {empty, Empty},
     {frac, (Montgomery-Empty)/(Normal-Empty)}}.

