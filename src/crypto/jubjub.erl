-module(jubjub).
-export([test/1,
         sqrt/1,
         wiki_sqrt/1,
         gen_point/0,
         gen_point/1,
         multiply/2,
         double/1,
         affine2extended/1,
         affine_niels2extended_niels/1,
         affine2affine_niels/1,
         eq/2,
         add/2,
         extended2affine/1,
         extended2extended_niels/1,
         extended_niels2extended/1,
         decompress_points/1,
         is_on_curve/1
        ]).

%this jubjub module is based on this: https://github.com/zkcrypto/jubjub/blob/main/src/lib.rs
%I am not storing numbers in montgomery format currently.

%modulus for building jubjub. this is the modulus for the scalar group on top of BLS12-381.
%q = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
-define(q, 52435875175126190479447740508185965837690552500527637822603658699938581184513).

-define(i2, 26217937587563095239723870254092982918845276250263818911301829349969290592257).


%the modulus for the scalar group on top of jubjub.
-define(r, 6554484396890773809930967563523245729705921265872317281365359162392183254199).

%GENERATOR = 6 (multiplicative generator of r-1 order, that is also quadratic nonresidue)
%720b1b19d49ea8f1bf4aa36101f13a585fa8cc968193ccbb0e70cbdc7dccf3ac hex2decimal 
-define(Generator, 51583287099746435272984346388532994015543111600007926519509846435385525990316).

-define(S, 1).

%aa9f02ab1d6124deb3524a64661129327342261215ac260b04d6b87b1da259e2
%for r.
-define(root_of_unity, 
        77174131359192641987342156634882896635436473315550340693359511651124777212386).

%/// INV = -(r^{-1} mod 2^64) mod 2^64
%1ba3a358ef788ef9
-define(INV, 
        1991615062597996281).


%2^256 mod ?r
-define(R,  %4365854490173040654744536428792730448269323145811170256246478247246014318553).
        10920338887063814464675503992315976177888879664585288394250266608035967270910).

-define(IR, 12549076656233958353659347336803947287922716146853412054870763148006372261952).
        

%1/(2^256) mod ?q

%R^2 mod ?r
-define(R2, %2244478849891746936202736009816130624903096691796347063256129649283183245105).
        3294906474794265442129797520630710739278575682199800681788903916070560242797).

%R^3 mod ?r
-define(R3, %2500637408964451122979126917521009379857064207447470548189037276238799111492).
        %45206882162899404125528140160728975319198890590864298389525709841616422531380).
        49829253988540319354550742249276084460127446355315915089527227471280320770991).

%edwards d = -(10240/10241) mod ?q
-define(D,  
        19257038036680949359750312669786877991949435402254120286184196891950884077233).
        %4613292015700488001365336802839132430399402449409985642425691713946182686872).
            %463575388861791286679386052962409037024404189887549159224978478986358827848
%01065fd6d6343eb1292d7f6d37579d26f5fd9207e6bd7fd42a9318e74bfa2b48

    %01065fd6d6343eb1
    %292d7f6d37579d26
    %f5fd9207e6bd7fd4
    %2a9318e74bfa2b48

    %2a9318e74bfa2b48f5fd9207e6bd7fd4292d7f6d37579d2601065fd6d6343eb1


%2 * d mod ?q
-define(D2, 
        38514076073361898719500625339573755983898870804508240572368393783901768154466).
        %2672099634510202192799706042155019131092883632947654003486024265500182119545).

-define(zero, 0).
%-define(rone, ?R).
%-define(one, 10920338887063814464675503992315976177888879664585288394250266608035967270910).%2^256 mod ?q. montgomery form of 1.
-define(one, 1).%2^256 mod ?q. montgomery form of 1.

-define(neg(A), (?q - A)).
-define(mul(A, B), ((A * B) rem ?q)).
-define(add_mod(C),
        if (C>=?q) -> C - ?q;
           true -> C end).
-define(sub(A, B),
        (if(A>=B) -> (A - B);
           true -> (A + ?q - B) end)).
montgomery_mul(A, B) ->
    %multiplication in montgomery form.
    AB = ?mul(A, B),
    ?mul(?IR, AB).
fadd(A, B) ->
    C = A + B,
    ?add_mod(C).
finverse(F) ->
    basics:inverse(F, ?q).
finverse_batch(L) ->
    ff:batch_inverse(L, ?q).
fpow(A, B) ->
    basics:rlpow(A, B, ?q).
sqrt_C() ->
    io:fwrite("sqrt_C \n"),
    <<C0:32>> = crypto:strong_rand_bytes(4),
    C = C0 + 2,
    %S = 32
    %S2 = fpow(2, S-1),
    S2 = 2147483648,
    C2 = fpow(C, S2),
    if
        (C2 == 1) -> sqrt_C();
        true -> C
    end.
factors_of_two(0) -> 1=2;
factors_of_two(X) when ((X rem 2) == 0) ->
    1 + factors_of_two(X div 2);
factors_of_two(_) -> 0.

wiki_sqrt(N) ->
    %https://en.wikipedia.org/wiki/Tonelli%E2%80%93Shanks_algorithm
    S = 32,
    Q = 12208678567578594777604504606729831043093128246378069236549469339647,
    Z = 5,
    %true = (?q - 1) == ?mul(Q, fpow(2, S)),
    %true = (?q - 1) == fpow(Z, (?q-1) div 2),
    %Z = 5,
    case wiki_sqrt2(S, fpow(Z, Q), fpow(N, Q), 
                    fpow(N, (Q+1) div 2)) of
        error -> error;
        R1 ->
            {?sub(0, R1), R1}
    end.
wiki_sqrt2(_M, _C, 0, R) -> 0;
wiki_sqrt2(_M, _C, 1, R) -> R;
wiki_sqrt2(M, C, T, R) ->
    %find smallest I such that 0<i<M and t^(2^i) == 1
    case get_I(0, M, T) of
        error -> error;
        I ->
            B = fpow(C, fpow(2, M - I - 1)),
            BB = ?mul(B, B),
            wiki_sqrt2(
              I, BB, ?mul(BB, T), ?mul(R, B))
    end.
get_I(X, X, _) -> error; 
get_I(N, M, 1) -> N;
get_I(N, M, T) -> 
    get_I(N+1, M, fpow(T, 2)).

    

    
sqrt(A) ->    
    %sqrt(a) mod P
    %fpow(A, (?q + 1) div 4).%this strategy doesn't work, because ?q+1 is not divisible by 4.
    %using tonelli-shanks. page 12 algorithm 5. https://eprint.iacr.org/2012/685.pdf
    %?q - 1 has 2^32 as a factor.
    %?q - 1 = t*2^S.
    S = 32,
    T = 12208678567578594777604504606729831043093128246378069236549469339647,
    %S = factors_of_two(?q - 1),
    %T = (?q - 1) div basics:rlpow(2, S, ?q),
    true = (?q-1) == T * fpow(2, S),
    W = fpow(A, (T-1) div 2),
    WW = ?mul(W, W),
    WWA = ?mul(WW, A),
    Bool = (fpow(WWA, fpow(2, S-1)) == (?q - 1)),
    if
        Bool ->
            %io:fwrite("that number has no square root.\n"),
            no_sqrt;
        true ->
            C = sqrt_C(),
            Z = fpow(C, T),
            %true = (?q - 1) == fpow(5, (?q-1) div 2), %checks that Z is a quadratic non-residue.
            true = (?q - 1) == fpow(Z, (?q-1) div 2), %checks that Z is a quadratic non-residue.
            X = ?mul(A, W),
            B = ?mul(X, W),
            sqrt2(A, S, X, B, W, Z)
    end.
sqrt2(A, V, X, B, W, Z) ->
    io:fwrite("sqrt2 "),
    io:fwrite(integer_to_list(V)),
    io:fwrite("\n"),
    %find smallest positive K where b^(2^k) == 1.
    K = sqrt_k(B, 0),
    %VK = ?sub(V, K),
    %VK1 = ?sub(VK, 1),
    %VK1 = (((V - K - 1) rem P) + P) rem P,
    VK1 = V - K - 1,
    if
        (VK1 < 0) -> 
            io:fwrite({V, K, Z}),
            sqrt(A);
        true ->
            %true = (VK1 > -1),
            W2 = fpow(Z, fpow(2, VK1)),
            Z2 = ?mul(W2, W2),
            B2 = ?mul(B, Z2),
            X2 = ?mul(X, W2),
            V2 = K,
            case B2 of
                1 -> X2;
                _ -> sqrt2(A, V2, X2, B2, W2, Z2)
            end
    end.
            
sqrt_k(B, K) ->
    C = fpow(B, fpow(2, K)),
    case C of
        1 -> K;
        _ -> sqrt_k(B, K+1)
    end.
            
    
    
    
-define(FR_MODULUS, 82852703072269600661578441035401213255493911489986464879664064758351744236814).
-define(FR_MODULUS_BYTES, 
        [183, 44, 247, 214, 94, 14, 151, 208, 
         130, 16, 200, 204, 147, 32, 104, 166, 
         0, 59, 52, 1, 1, 59, 103, 6, 
         169, 175, 51, 101, 234, 180, 125, 14]).

%a jubjub point.
-record(affine_point, {
          u = ?zero, % u can possibly be negative??
          v = ?one}).

generator() ->
    %62edcbb8bf3787c88b0f03ddd60a8187caf55d1b29bf81afe4b3d35df1a7adfe
    %62edcbb8bf3787c8
    %8b0f03ddd60a8187
    %caf55d1b29bf81af
    %e4b3d35df1a7adfe

    %e4b3d35df1a7adfecaf55d1b29bf81af8b0f03ddd60a818762edcbb8bf3787c8
    %"4e3b3dd51f7adaefac5fd5b192fb18fab8f030dd6da0187826debc8bfb73788c"
    %"26debc8bfb73788cb8f030dd6da01878ac5fd5b192fb18fa4e3b3dd51f7adaef"

    A = #affine_point{
           v = 11,
           u = % 17581429596771594620009844481038993443214979027141390825343533838268221807343
               %35385072918627718043713148493801197528901743097221144573611547205535651821708 
               %103445053902783521905114435114685718156801333628409219107608055170232558782408
               44746807950788659978687200207992930935149218647843500701850233404325651525118
               %115194287181224516511265984065352866302384695513220181839485073082323925986658,
               %4258727773875940690362607550498304598101071202821725296872974770776423442226
     },
    true = A#affine_point.u < ?q,
    A.


%default values are for encoding affine point {0, ?one}
-record(extended_point, {
          u = ?zero, 
          v = ?one, 
          z = ?one, %can't be zero.
          t1 = ?zero, 
          t2 = ?zero}).
%correspoinds to the affine point {u/z, v/z}
%t1*t2 = u*v/z is always true.

%default values are for encoding affine point {0, ?one}
-record(affine_niels_point, {
          v_plus_u = ?one, 
          v_minus_u = ?one, 
          t2d = ?zero}).%u*v*2d

-record(extended_niels_point, {
          v_plus_u = ?one,
          v_minus_u = ?one,
          t2d = ?zero,
          z = ?one}).



affine2extended(#affine_point{u = U, v = V}) ->
    #extended_point{u = U, v = V, z = ?one, t1 = U,
                    t2 = V}.
extended2affine(
  E = #extended_point{z = Z}) ->
    extended2affine(E, finverse(Z)).
extended2affine(
  #extended_point{u = U, v = V}, IZ) ->
    #affine_point{u = ?mul(U, IZ),
                  v = ?mul(V, IZ)}.
affine2affine_niels(#affine_point{u = U, v = V}) ->
    UV = ?mul(U, V),
    T = ?mul(UV, ?D2),
    #affine_niels_point{
                     v_plus_u = fadd(V, U),
                     v_minus_u = ?sub(V, U),
                     t2d = T
                    }.
extended2extended_niels(
  #extended_point{u = U, v = V, z = Z, t1 = T1, 
                  t2 = T2}) ->
    %UV = ?mul(U, V),
    T3 = ?mul(T1, T2),
    #extended_niels_point{
               v_plus_u = fadd(V, U),
               v_minus_u = ?sub(V, U),
               z = Z,
               t2d = ?mul(T3, ?D2)
                      }.
extended_niels2extended(
  #extended_niels_point{
     v_plus_u = VPU,
     v_minus_u = VSU,
     z = Z,
     t2d = T}) -> 
    V2 = fadd(VPU, VSU),
    U2 = ?sub(VPU, VSU),
    IZ = finverse(Z),
    V = ?mul(IZ, ?mul(V2, ?i2)),%divide by 2.
    U = ?mul(IZ, ?mul(U2, ?i2)),
    A = #affine_point{u = U, v = V},
    affine2extended(A).
    
     
affine_niels2extended_niels(
    #affine_niels_point{
                    v_plus_u = VPU2,
                    v_minus_u = VMU2,
                    t2d = TD2}) ->
    #extended_niels_point{v_plus_u = VPU2,
                          v_minus_u = VMU2,
                          t2d = TD2,
                          z = ?one}.

batch_extended2affine(Es) ->
    Zs = lists:map(fun(#extended_point{z = Z}) ->
                           Z end, Es),
    Is = ff:batch_inverse(Zs, ?q),
    lists:zipwith(
      fun(P, I) -> extended2affine(P, I) end,
      Es, Is).
                   

neg(A = #affine_point{u = U}) ->
    A#affine_point{u = ?neg(U)};
neg(A = #extended_point{u = U, t1 = T}) ->
    A#extended_point{u = ?neg(U), t1 = ?neg(T)}.

eq(#affine_point{u = U, v = V},
   #affine_point{u = U, v = V}) ->
    true;
eq(#affine_point{},
   #affine_point{}) ->
    false;
eq(#extended_point{u = U1, v = V1, z = Z1},
   #extended_point{u = U2, v = V2, z = Z2}) ->
    (?mul(U1, Z2) == ?mul(U2, Z1)) and
        (?mul(V1, Z2) == ?mul(V2, Z1)).

identity(#extended_point{u = U, v = V, z = Z}) ->
    (U == ?zero) and (V == Z).

small_order(E = #extended_point{}) ->
    E2 = double(double(E)),
    E2#extended_point.u == ?zero.

is_torsion_free(E = #extended_point{}) ->
    S = ?r,
    E2 = multiply(S, E),
    identity(E2).

%prime order means that ?r is the smallest scalar that you can multiply by this point to produce the identity.
is_prime_order(E = #extended_point{}) ->
    is_torsion_free(E) and not(identity(E)).

is_on_curve(#affine_point{u = U, v = V}) ->
    %only for testing.
    U2 = ?mul(U, U),
    V2 = ?mul(V, V),
    UV2 = ?mul(U2, V2),
    (?sub(V2, U2)) == fadd(?one, ?mul(?D, UV2)).
%v*v - u*u = one + d*u*u*v*v
%vv - duuvv = one + uu
%vv(1 - duu) = one + uu
%vv = (one + uu)/(1 - duu)

-define(tries, 20).

test_gen_point(_, _, 0) -> ok;
test_gen_point(G, X, Times) 
  when (Times > 0) ->
    io:fwrite(integer_to_list(Times)),
    io:fwrite("\n"),
    G = gen_point(X),
    test_gen_point(G, X, Times-1).

gen_point() ->
    <<X0:256>> = crypto:strong_rand_bytes(32),
    X = X0 rem ?q,
    G = gen_point(X, 2, 2),
    true = is_on_curve(G),
    G.
decompress_points(L) when is_list(L) ->
    gen_point(L, ?tries, ?tries).

gen_point(X) ->
    gen_point(X, ?tries, ?tries).
gen_point(U, 0, StartTries) ->
    gen_point(U+1, StartTries, StartTries);
gen_point(Us, _Tries, _StartTries) 
  when is_list(Us) ->
    UUs = lists:map(fun(X) -> ?mul(X, X) end, Us),
    DUUs = lists:map(fun(X) -> ?sub(1, ?mul(?D, X))
                     end, UUs),
    Bs = finverse_batch(DUUs),
    VVs = lists:zipwith(
            fun(B, UU) -> 
                    ?mul(fadd(?one, UU), B)
            end, Bs, UUs),
    lists:zipwith(
      fun(U, VV) ->
              gen_point(U, 20, 20, VV)
      end, Us, VVs);
gen_point(U, Tries, StartTries) ->
    UU = ?mul(U, U),
    DUU = ?mul(?D, UU),
    B = finverse(?sub(1, DUU)),
    T = fadd(?one, UU),
    VV = ?mul(T, B),
    gen_point(U, Tries, StartTries, VV).
           
gen_point(U, _, StartTries, VV) ->
    case wiki_sqrt(VV) of
        error ->
            gen_point(U+1, StartTries, StartTries);
        {V1, V2} ->
            A = #affine_point{u = U, v = V1},
            G = affine2extended(A),
            Prime = is_prime_order(G),
            if
                Prime -> A;
                true -> #affine_point{u = U, v = V2}
            end
    end.
                            
old_gen_point(U, Tries, StartTries, VV) ->
    V = sqrt(VV),
    case V of
        no_sqrt -> 
            %io:fwrite("no sqrt\n"),
            gen_point(U+1, StartTries, StartTries);
        _ ->
            A = #affine_point{u = U, v = V},
            G = affine2extended(A),
            %when decompressing, there are 2 possible values of V. only one of them passes the prime order test.
            Prime = is_prime_order(G),
            if
                Prime -> A;
                true -> gen_point(U, Tries-1, 
                                  StartTries, VV)
            end
    end.
    

-record(completed_point, {u, v, z, t}).

completed_to_extended(
  #completed_point{
    u = U, v = V, z = Z, t = T}) ->
    #extended_point{
                     u = ?mul(U, T),
                     v = ?mul(V, Z),
                     z = ?mul(Z, T),
                     t1 = U,
                     t2 = V
                   }.

double(#extended_point{
          u = U, v = V, z = Z, t1 = _T1, 
          t2 = _T2}) ->
    UU = ?mul(U, U),
    VV = ?mul(V, V),
    ZZ2 = ?mul(Z*2, Z),
    UV1 = fadd(U, V),
    UV2 = ?mul(UV1, UV1),
    VV_plus_UU = fadd(VV, UU),
    VV_minus_UU = ?sub(VV, UU),
    CP = #completed_point{
      u = ?sub(UV2, VV_plus_UU),
      v = VV_plus_UU,
      z = VV_minus_UU,
      t = ?sub(ZZ2, VV_minus_UU)},
    completed_to_extended(CP).

print32(N) ->
    <<A:64, B:64, C:64, D:64>> = <<N:256>>,
    io:fwrite("erl "),
    io:fwrite(integer_to_list(A)),
    io:fwrite(" "),
    io:fwrite(integer_to_list(B)),
    io:fwrite(" "),
    io:fwrite(integer_to_list(C)),
    io:fwrite(" "),
    io:fwrite(integer_to_list(D)),
    io:fwrite("\n").
    

add(#extended_point{
       u = U,
       v = V,
       z = Z1,
       t1 = T1,
       t2 = T2
      },
    #extended_niels_point{
                    v_plus_u = VPU2,
                    v_minus_u = VMU2,
                    t2d = TD2,
                    z = Z2}) ->
    VMU1 = ?sub(V, U),
    A = ?mul(VMU1, VMU2),
    VPU1 = fadd(V, U),
    B = ?mul(VPU1, VPU2),
    TD1 = ?mul(T1, T2),
    C = ?mul(TD1, TD2),
    D = ?mul(2*Z1, Z2),
    CP = #completed_point{
      u = ?sub(B, A),
      v = fadd(B, A),
      z = fadd(D, C),
      t = ?sub(D, C)},
    completed_to_extended(CP);
add(E = #extended_point{},
    A = #affine_niels_point{}) ->
    A2 = affine_niels2extended_niels(A),
    add(E, A2).


sub(#extended_point{
       u = U,
       v = V,
       z = Z1,
       t1 = T1,
       t2 = T2
      },
    #extended_niels_point{
                    v_plus_u = VPU2,
                    v_minus_u = VMU2,
                    t2d = TD2,
                    z = Z2}) ->
    VMU1 = ?sub(V, U),
    VPU1 = fadd(V, U),
    A = ?mul(VMU1, VPU2),
    B = ?mul(VPU1, VMU2),
    TD1 = ?mul(T1, T2),
    C = ?mul(TD1, TD2),
    D = ?mul(2*Z1, Z2),
    CP = #completed_point{
      u = ?sub(B, A),
      v = fadd(B, A),
      t = ?sub(D, C),
      z = fadd(D, C)
     },
    completed_to_extended(CP);
sub(E = #extended_point{},
    A = #affine_niels_point{}) ->
    A2 = affine_niels2extended_niels(A),
    sub(E, A2).


multiply(N, Base = #extended_point{}) ->
    multiply(N, extended2extended_niels(Base));
multiply(1, Base = #affine_niels_point{}) -> 
    multiply(1, affine_niels2extended_niels(Base));
multiply(1, Base = #extended_niels_point{}) ->
    extended_niels2extended(Base);
multiply(1, Base = #affine_point{}) ->
    multiply(1, affine2affine_niels(Base));
multiply(1, _) ->
    io:fwrite("can only multiply points.\n"),
    ok;
multiply(S, Base) %base is some kind of niels point
  when ((S rem 2) == 0) -> 
    X = multiply(S div 2, Base),
    double(X);
multiply(S, Base) -> 
    X = multiply(S-1, Base),
    add(X, Base).

%from_raw(N) ->    
%    ?mul(N, ?R2).

many(_, 0) -> [];
many(A, N) when N > 0 -> 
    [A|many(A, N-1)].


check_rs() ->
    %R = ?R,
    R = basics:rlpow(2, 256, ?q),
    R2 = (R*R) rem ?q,
    R3 = (R2*R) rem ?q,
    %QR = basics:rlpow(2, 256, ?q),
    %io:fwrite({QR}),
    {{?R, ?R2, ?R3, ?one},
     {R, R2, R3, 1}}.

test(1) ->
    {X, X} = check_rs(),
    D = ?neg(?mul(10240, finverse(10241))),
    D2 = ?mul(2, D),
    %io:fwrite({D, D2}),
    {?D == (?neg(?mul(10240, finverse(10241)))),
    ?D2 == ?mul(2, ?D)};
test(2) ->
    %A = generator(),
    G = gen_point(),
    G2 = extended2affine(affine2extended(G)),
    if
        not(G == G2) ->
            io:fwrite({G, G2});
        true -> ok
    end,
    E = affine2affine_niels(G),
    G = extended2affine(multiply(1, E)),
    {
      %A,
      is_on_curve(G),
      is_on_curve(extended2affine(multiply(2000000, E)))
    };
test(3) ->
    %multiply speed test.
    M = 100,
    Many = many(0, M),
    <<P:256>> = crypto:strong_rand_bytes(32),
    T1 = erlang:timestamp(),
    G = gen_point(),
    E = affine2affine_niels(G),
    lists:map(fun(_) ->
                      multiply(P, E)
              end, Many),
    T2 = erlang:timestamp(),
    D1 = timer:now_diff(T2, T1),
    {mul, D1 / M};
test(4) ->
    %cofactor tests
    A = gen_point(),
    G = multiply(1, A),
    {is_torsion_free(G),
     not(identity(G)),
     is_prime_order(G),
     A};
test(5) ->
    io:fwrite("deterministic gen point test\n"),
    Times = 100,
    X = 500000,
    G = gen_point(X),
    test_gen_point(G, X, Times);
test(6) ->
    io:fwrite("decompress point speed test\n"),
    ok;
test(7) ->
    io:fwrite("square root test\n"),
    R = wiki_sqrt(?R2),
    R = ?R,
    %R = sqrt(?R2),
    S = factors_of_two(?q - 1),
    S = 32,
    T = (?q - 1) div basics:rlpow(2, S, ?q),
    T = 12208678567578594777604504606729831043093128246378069236549469339647,
    C = sqrt_C(),
    Z = basics:rlpow(C, T, ?q),
    {
      {c, C},
      {z, Z}
    }.

    



