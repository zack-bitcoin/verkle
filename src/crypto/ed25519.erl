-module(ed25519).

%this version is in erlang for testing and documentation purposes.

-export([
         %using integers in a finite field mod q.
         fsqrt/1, fadd/2, fsub/2, fmul/2, finv/1,
         fneg/1,
         fgen_point/0,
         fencode_point/1,%to32 byte format
         fdecode_point/1,
         faffine2extended/1,
         fextended2affine_batch/1,
         fextended_mul/2,
         fextended_double/1,
         fextended_add/2,
         fnormalize/1,
         feq/2,
         fhash_point/1,
         fis_on_curve/1,

         %montgomery encoded version
         encode/1,
         decode/1,
         mmul/2,
         msub/2,
         madd/2,
         mpow/2,
         mneg/1,
         msqrt/1,
         mdecode_point/1,
         maffine2extended/1,
         mextended2affine_batch/1,
         mextended_double/1,
         mextended_add/2,
         mextended_mul/2,
         meq/2,
         mencode_point/1,
         mdecode_point/1,
         mgen_point/0,

         fbase_point/0,

         test/1
        ]).

%twisted edwards curve with this equation.
%−x^2 + y^2 = 1 − (121665/121666) * x^2 * y^2

%-on_load(init/0).

init() ->
    ok = erlang:load_nif("./ebin/fq", 0),
    setup(0),
    ok.
setup(_) ->
    %defined in C.
    ok.

%finite field the curve is defined over
%2^255 - 19
-define(q, 
        57896044618658097711785492504343953926634992332820282019728792003956564819949
       ).

% 2^252 + 27742317777372353535851937790883648493
%this is how many points exist on the curve.
-define(order, 
        7237005577332262213973186563042994240857116359379907606001950938285454250989
       ).

% -(121665/121666)
-define(D, 37095705934669439343138083508754565189542113879843219016388785533085940283555).
%montgomery encoded version of D.
-define(mD, 
20131754669644349956395353228418582963360511446355554149282842162308175096314
).
%<<250,233,71,223,254,139,237,128,115,41,198,175,
%  119,135,161,16,144,134,24,188,7,146,147,229,38,
%  197,159,114,90,43,130,44>>).

%generator point.
-define(basex, 15112221349535400772501151409588531511454012693041857206046113283949847762202).
-define(mbasex, 53200009714422349948974321025268612095537551340208035652193176754485131584135).
-define(basey, 46316835694926478169428394003475163141307993866256225615783033603165251855960).
-define(mbasey, 23158417847463239084714197001737581570653996933128112807891516801582625928010).
%basex  * basey mod q
-define(basex_basey, 46827403850823179245072216630277197565144205554125654976674165829533817101731).
-define(mbasex_basey, 42560007771537879959179456820214889676430041072166428521754541403588105267308).

-define(max256, 115792089237316195423570985008687907853269984665640564039457584007913129639936).

% 2^255
%-define(max255 57896044618658097711785492504343953926634992332820282019728792003956564819968).

-define(max255, 1).
%57896044618658097711785492504343953926634992332820282019728792003956564819968).

%montgomery encoded 1
-define(m_one, 38).
-define(m_two, 76).

%sqrt -1
-define(sqrt_neg1, 19681161376707505956807079304988542015446066515923890162744021073123829784752).
% other root: 38214883241950591754978413199355411911188925816896391856984770930832735035197}

-record(extended, {x, y, z, t}).
-record(affine, {x, y}).

-define(fbase_point, 
        #extended{x = ?basex, y = ?basey,
                  z = 1, 
                  t = ?basex_basey}).
fbase_point() ->
    ?fbase_point.

-define(mbase_point,
        #extended{x = ?mbasex, y = ?mbasey,
                  z = ?m_one, t = ?mbasex_basey}).

-define(fzero_point,
        #extended{x = 0, y = 1, z = 1, t = 0}).
-define(mzero_point,
        #extended{x = 0, y = ?m_one, 
                  z = ?m_one, t = 0}).

-define(faffine_zero, #affine{x = 0, y = 1}).


-define(maffine_zero, #affine{x = 0, y = ?m_one}).

fadd(X, Y) ->
    ff:add(X, Y, ?q).
fsub(X, Y) ->
    ff:sub(X, Y, ?q).
fmul(X, Y) ->
    ff:mul(X, Y, ?q).
finv(X) ->
    ff:inverse(X, ?q).



faffine2extended(P = #affine{x = X, y = Y}) ->
    %io:fwrite("f affine 2 extended\n"),
    %B = feq(P, ?faffine_zero),
    %B = fis_affine_zero(P),
    %if
    %    B -> ?fzero_point;
    %    true ->
            #extended{x = X, y = Y, z = 1, 
                      t = fmul(X, Y)};
    %end;
faffine2extended(L) when is_list(L) ->
    lists:map(fun(X) ->
                      faffine2extended(X)
              end, L).

fextended2affine_batch(L) ->
    Zs = lists:map(fun(#extended{z = Z}) ->
                           Z end, L),
    Is = ff:batch_inverse(Zs, ?q),
    lists:zipwith(
      fun(P, I) -> fextended2affine(P, I) end,
      L, Is).
fextended2affine(
  #extended{x = X, y = Y}, I) ->
    #affine{x = fmul(X, I), y = fmul(Y, I)}.

fnormalize(L) ->
    faffine2extended(fextended2affine_batch(L)).

fis_affine_zero(#affine{x = 0, y = 1}) -> true;
fis_affine_zero(A = #affine{}) -> 
    %io:fwrite("f is affine zero\n"),
    E = faffine2extended(A),
    fis_extended_zero(E).
    
fis_extended_zero(E3) -> 
    %io:fwrite("f is extended zero\n"),
    ZT = fextended_double(
           fextended_double(
             fextended_double(E3))),
    feq2(ZT, ?fzero_point).
feq(A1 = #affine{}, A2) -> 
    feq(faffine2extended(A1),
        faffine2extended(A2));
feq(E1 = #extended{}, E2 = #extended{}) ->
    E3 = fextended_sub(E1, E2),
    fis_extended_zero(E3).
feq2(#extended{x = X1, y = Y1, z = Z1}, 
    #extended{x = X2, y = Y2, z = Z2}) -> 
    %io:fwrite("f eq 2\n"),
    (fmul(X1, Z2) == fmul(X2, Z1)) 
        and (fmul(Y1, Z2) == fmul(Y2, Z1)).
    
%feq(#affine{x = X, y = Y},
%           #affine{x = X, y = Y}) ->
%    true;
%feq(#affine{}, #affine{}) ->
%    false.

fneg(E = #extended{x = X, t = T}) ->
    E#extended{x = fneg(X), t = fneg(T)};
fneg(A = #affine{x = X}) ->
    A#affine{x = fneg(X)};
fneg(0) -> 0;
fneg(X) when is_integer(X) -> ?q - X.


fextended_double(
  #extended{x = X1, y = Y1, z = Z1}) ->
    %http://hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html#doubling-dbl-2008-hwcd 
    A = fmul(X1, X1),
    B = fmul(Y1, Y1),
    C = fmul(2, fmul(Z1, Z1)),
    D = fneg(A),%a = -1 for this curve.
    XY = fadd(X1, Y1),
    E = fsub(fmul(XY, XY), fadd(A, B)),
    G = fadd(D, B),
    F = fsub(G, C),
    H = fsub(D, B),
    #extended{x = fmul(E, F), y = fmul(G, H),
              t = fmul(E, H), z = fmul(F, G)}.

fextended_add(
  P1 = #extended{x = X1, y = Y1, z = Z1, t = T1},
  #extended{x = X2, y = Y2, z = Z2, t = T2}) ->
    A = fmul(fsub(Y1, X1), fadd(Y2, X2)),
    B = fmul(fadd(Y1, X1), fsub(Y2, X2)),
    F = fsub(B, A),
    if 
        (F == 0) ->
            fextended_double(P1); %same point.
        true ->
            C = fmul(Z1, fmul(2, T2)),
            D = fmul(T1, fmul(2, Z2)),
            E = fadd(D, C),
            G = fadd(B, A),
            H = fsub(D, C),
            X3 = fmul(E, F),
            Y3 = fmul(G, H),
            T3 = fmul(E, H),
            Z3 = fmul(F, G),
            #extended{x = fmul(E, F),
                      y = fmul(G, H),
                      t = fmul(E, H),
                      z = fmul(F, G)}
    end.

fextended_sub(P1, P2) ->
    fextended_add(P1, fneg(P2)).

fextended_mul(P = #extended{}, N) ->
    [P2] = fnormalize([P]),
    fextended_mul2(?fzero_point, P2, N, 256).
fextended_mul2(A, _, _, 0) -> A;
fextended_mul2(A, B, N, C) 
  when ((N band 1) == 0) ->
    fextended_mul2(A, fextended_double(B), 
                   N div 2, C-1);
fextended_mul2(A, B, N, C) ->
    A2 = fextended_add(A, B),
    fextended_mul2(A2, fextended_double(B), 
                   N div 2, C-1).

fsqrt(A) ->
    V = ff:pow((2*A), (?q - 5) div 8, ?q),
    AV = ff:mul(A, V, ?q),
    I = ff:mul(2*AV, V, ?q),
    R = ff:mul(AV, I-1, ?q),
    {ff:neg(R, ?q), R}.

fis_on_curve(#affine{x = X, y = Y}) ->
    XX = fmul(X, X),
    YY = fmul(Y, Y),
    XY = fmul(XX, YY),
    fsub(YY, XX) == fadd(1, fmul(?D, XY)).

fgen_point() ->
    <<X0:256>> = crypto:strong_rand_bytes(32),
    case fdecode_point(<<X0:256>>) of
        error -> fgen_point();
        P -> P
    end.
fdecode_point(<<S:1, P0:255>>) ->
    P = decode(P0),
    true = P < ?q,
    UU = fmul(P, P),
    DUU = fmul(?D, UU),
    B = finv(fsub(1, DUU)),
    T = fadd(1, UU),
    VV = fmul(T, B),
    case fsqrt(VV) of
        error ->
            %invalid point.
            %io:fwrite("invalid, no square root\n"),
            error;
        {V1, V2} ->
            S2 = fis_positive(V1),
                
            V = if
                    (S == S2) -> V1;
                    true -> V2
                end,
%            V = case S of
%                    0 -> V1;
%                    1 -> V2
%                end,
            Point = #affine{x = P, y = V},
            Bool = fis_on_curve(Point),
            if
                Bool -> Point;
                true -> 
                    %invalid point
                    %io:fwrite("invalid, not on curve\n"),
                    error
            end
    end.
mis_positive(Y) ->
    %returns true if Y is even.
    (Y band ?max255) == 0.
fis_positive(Y) ->
    Y2 = encode(Y),
    mis_positive(Y2).
fencode_point(#affine{x = X, y = Y}) ->
    S = case not(fis_positive(Y)) of
            true -> 1;
            false -> 0
        end,
    X2 = encode(X),
    <<S:1, X2:255>>.
mencode_point(#affine{x = X, y = Y}) ->
    S = case not(mis_positive(Y)) of
            true -> 1;
            false -> 0
        end,
    <<S:1, X:255>>.
  
fhash_point(P = #extended{}) ->
    P2 = fextended_mul(P, 8),
    [P3] = fextended2affine_batch([P2]),
    <<E:256>> = fencode_point(P3),
    R = E rem fr:prime(),
    %io:fwrite({P3, E, R}),
    R.
 

%2^256
-define(r, 115792089237316195423570985008687907853269984665640564039457584007913129639936).
-define(r_bits, 256).
-define(r_bits2, 512).

-define(n, ?q).
% in * ?q = -1 in base r
-define(in, 21330121701610878104342023554231983025602365596302209165163239159352418617883).

%1/r rem n
-define(ir, 10665060850805439052171011777115991512801182798151104582581619579676209308938).

%r*r rem n
-define(r2, 1444).

redc(T) -> redc(?r, ?q, ?in, T).
redc(R, N, IN, T) ->
    <<Tb:?r_bits>> = <<T:?r_bits>>,
    <<M:?r_bits>> = <<(Tb*IN):?r_bits>>,
    <<T2:?r_bits, _/binary>> = 
        <<(T + (M*N)):?r_bits2>>,
    if
        (T2 >= N) -> T2 - N;
        true -> T2
    end.
encode(A) when ((A < ?q) and (A > -1)) ->
    redc(?r2 * A).
decode(A) ->
    mmul(A, 1).
mmul(A, B) ->
    redc(A*B).
mneg(A) -> fneg(A).
msub(A, B) -> fsub(A, B).
madd(A, B) -> fadd(A, B).
minv(A) -> encode(ff:inverse(decode(A), ?q)).

%A is montgomery encoded. B is not.
mpow(A, 0) -> 0;
mpow(A, 1) -> A;
mpow(A, N) when (N rem 2) == 0 -> 
    mpow(mmul(A, A), N div 2);
mpow(A, N) -> 
    mmul(A, mpow(A, N-1)).

msqrt(A) ->
    T = encode(2),
    V = mpow(mmul(T, A), (?q - 5) div 8),
    AV = mmul(A, V),
    I = mmul(AV, mmul(V, T)),
    R = mmul(AV, msub(I, encode(1))),
    {mneg(R), R}.

meq(#extended{x = X1, y = Y1, z = Z1}, 
    #extended{x = X2, y = Y2, z = Z2}) -> 
    (mmul(X1, Z2) == mmul(X2, Z1)) 
        and (mmul(Y1, Z2) == mmul(Y2, Z1));
meq(#affine{x = X, y = Y},
    #affine{x = X, y = Y}) -> true;
meq(#affine{}, #affine{}) -> false.

mpis([], _) -> [];
mpis([H|T], A) -> 
    X = mmul(H, A),
    [X|mpis(T, X)].
mbatch_inverse(Vs) ->
    [All|V2] = lists:reverse(mpis(Vs, encode(1))),%[v16, v15, v14, v13, v12, v1]
    AllI = minv(All),
    VI = lists:map(
           fun(V) -> mmul(AllI, V) end,
           V2), %[i6, i56, i46, i36, i26]
    V3 = lists:reverse(mpis(lists:reverse(Vs), encode(1))),%[v16, v26, v36, v46, v56, v6]
    V4 = tl(V3)++[encode(1)],%[v26, v36, v46, v56, v6, 1]
    VI2 = [AllI|lists:reverse(VI)],%[i16, i26, i36, i46, i56, i6]
    lists:zipwith(fun(A, B) ->
                          mmul(A, B)
                  end, V4, VI2).
    
maffine2extended(P = #affine{x = X, y = Y}) ->
    B = meq(P, ?maffine_zero),
    if
        B -> ?mzero_point;
        true ->
            #extended{x = X, y = Y, z = ?m_one,
                      t = mmul(X, Y)}
    end;
maffine2extended(L) when is_list(L) ->
    lists:map(fun(X) ->
                      maffine2extended(X)
              end, L).
mextended2affine_batch(L) ->
    Zs = lists:map(fun(#extended{z = Z}) ->
                           Z end, L),
    Is = mbatch_inverse(Zs),
    lists:zipwith(
      fun(P, I) -> mextended2affine(P, I) end,
      L, Is).
mextended2affine(
  #extended{x = X, y = Y}, I) ->
    #affine{x = mmul(X, I), y = mmul(Y, I)}.

mnormalize(L) ->
    maffine2extended(mextended2affine_batch(L)).

mextended_double(              
  #extended{x = X1, y = Y1, z = Z1}) ->
    %http://hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html#doubling-dbl-2008-hwcd 
    A = mmul(X1, X1),
    B = mmul(Y1, Y1),
    C = mmul(?m_two, mmul(Z1, Z1)),
    D = mneg(A),%a = -1 for this curve.
    XY = madd(X1, Y1),
    E = msub(mmul(XY, XY), madd(A, B)),
    G = madd(D, B),
    F = msub(G, C),
    H = msub(D, B),
    #extended{x = mmul(E, F), y = mmul(G, H),
              t = mmul(E, H), z = mmul(F, G)}.

mextended_add(
  P1 = #extended{x = X1, y = Y1, z = Z1, t = T1},
  #extended{x = X2, y = Y2, z = Z2, t = T2}) ->
    A = mmul(msub(Y1, X1), madd(Y2, X2)),
    B = mmul(madd(Y1, X1), msub(Y2, X2)),
    F = msub(B, A),
    if 
        (F == 0) ->
            mextended_double(P1); %same point.
        true ->
            C = mmul(Z1, mmul(?m_two, T2)),
            D = mmul(T1, mmul(?m_two, Z2)),
            E = madd(D, C),
            G = madd(B, A),
            H = msub(D, C),
            X3 = mmul(E, F),
            Y3 = mmul(G, H),
            T3 = mmul(E, H),
            Z3 = mmul(F, G),
            #extended{x = mmul(E, F),
                      y = mmul(G, H),
                      t = mmul(E, H),
                      z = mmul(F, G)}
    end.
    
mextended_sub(P1, P2) ->
    mextended_add(P1, mneg(P2)).
    
mextended_mul(P = #extended{}, N) ->
    %N is NOT montgomery encoded.
    [P2] = mnormalize([P]),
    mextended_mul2(?mzero_point, P2, N, 256).
mextended_mul2(A, _, _, 0) -> A;
mextended_mul2(A, B, N, C) 
  when ((N band 1) == 0) ->
    mextended_mul2(A, mextended_double(B), 
                   N div 2, C-1);
mextended_mul2(A, B, N, C) ->
    A2 = mextended_add(A, B),
    mextended_mul2(A2, mextended_double(B), 
                   N div 2, C-1).

mis_on_curve(#affine{x = X, y = Y}) ->
    XX = mmul(X, X),
    YY = mmul(Y, Y),
    XY = mmul(XX, YY),
    msub(YY, XX) == 
        madd(encode(1), mmul(?mD, XY)).

mgen_point() ->
    <<X0:256>> = crypto:strong_rand_bytes(32),
    case mdecode_point(<<X0:256>>) of
        error -> mgen_point();
        P -> P
    end.
mdecode_point(<<S:1, P:255>>) ->
    %P is a montgomery encoded integer.
    UU = mmul(P, P),
    DUU = mmul(?mD, UU),
    B = minv(msub(?m_one, DUU)),
    T = madd(?m_one, UU),
    VV = mmul(T, B),
    case msqrt(VV) of
        error ->
            %invalid point.
            io:fwrite("invalid, no square root\n"),
            error;
        {V1, V2} ->
            SB = (S == 0),
            S2 = mis_positive(V1),
            V = if
                    (SB == S2) -> V1;
                    true -> V2
                end,
            if
                not(SB == ((V rem 2) == 0)) -> error;
                true ->
                    %SB = ((V rem 2) == 0),
            %s==1 means it should be even.
%            io:fwrite({{s, S}, {v_should_be_even, SB}, 
%                       {v1_even, S2, 0 == (V1 rem 2)},
%                       {v1_same_as_v, V1 == V}}),
            Point = #affine{x = P, y = V},
            Bool = mis_on_curve(Point),
            if
                Bool -> Point;
                true -> 
                    %invalid point
                    %io:fwrite("invalid, not on curve\n"),
                    error
            end
            end
    end.
    
            
    


    
            
            
        
    




% 2 * D
%16295367250680780974490674513165176452449235426866156013048779062215315747161
-define(D2, 
<<244,211,143,190,253,23,219,1,231,82,140,95,239,
  14,67,33,32,13,49,120,15,36,39,203,77,138,63,
  229,180,86,4,89>>).

m2f(#affine{x = X, y = Y}) ->
    X2 = decode(X),
    Y2 = decode(Y),
    #affine{x = X2, y = Y2};
m2f(#extended{x = X, y = Y, z = Z, t = T}) ->
    X2 = decode(X),
    Y2 = decode(Y),
    Z2 = decode(Z),
    T2 = decode(T),
    #extended{x = X2, y = Y2, z = Z2, t = T2}.
f2m(#affine{x = X, y = Y}) ->
    X2 = encode(X),
    Y2 = encode(Y),
    #affine{x = X2, y = Y2};
f2m(#extended{x = X, y = Y, z = Z, t = T}) ->
    X2 = encode(X),
    Y2 = encode(Y),
    Z2 = encode(Z),
    T2 = encode(T),
    #extended{x = X2, y = Y2, z = Z2, t = T2}.
    
    


test(1) ->
   %batch inverse
    L = [5, 7, 9, 33],
    L2 = mbatch_inverse(L),
    L = mbatch_inverse(L2),
    success;
test(2) ->
    Pf = fgen_point(),

    %to montgomery and back
    Pm = f2m(Pf),
    Pf = m2f(Pm),

    % to extended and back
    Pme = maffine2extended(Pm),
    Pfe = faffine2extended(Pf),

    Pf = hd(fextended2affine_batch([Pfe])),
    Pm = hd(mextended2affine_batch(
              [Pme])),

    %zero point is same

    true = hd(mextended2affine_batch(
                [?mzero_point])) ==
        f2m(hd(fextended2affine_batch(
                 [?fzero_point]))),

    %mul neg add sub

    N = 27,
    M = 16,
    Nm = encode(N),
    Mm = encode(M),
    
    NM = fmul(N, M),
    NM = decode(mmul(Nm, Mm)),

    N2 = fneg(N),
    N2b = decode(mneg(Nm)),

    NM2 = fadd(N, M),
    NM2 = decode(madd(Nm, Mm)),

    NM3 = fsub(N, M),
    NM3 = decode(fsub(Nm, Mm)),

    %double zero is zero

    true = feq(fextended_double(?fzero_point),
               ?fzero_point),
    %io:fwrite({mextended2affine_batch([mextended_double(?mzero_point), ?mzero_point]), [mextended_double(?mzero_point), ?mzero_point]}),
    true = meq(mextended_double(?mzero_point),
               ?mzero_point),

    %doubling

    Pfd = fextended_double(Pfe),
    Pmd = mextended_double(Pme),
    Pfd2 = m2f(Pmd),
    true = feq(Pfd2, Pfd),

    %adding

    Pft = fextended_add(Pfe, Pfd),
    Pmt = mextended_add(Pme, Pmd),
    Pft2 = m2f(Pmt),
    true = feq(Pft2, Pft),

    %adding same
    Pfdb = fextended_add(Pfe, Pfe),
    Pmdb = mextended_add(Pme, Pme),
    Pfd2b = m2f(Pmdb),
    true = feq(Pfd2b, Pfdb),

    %adding zero should change nothing.

    Pfe2 = fextended_add(Pfe, ?fzero_point),
    true = feq(Pfe, Pfe2),
    Pme2 = mextended_add(Pme, ?mzero_point),
    true = feq(Pme, Pme2),

    %multiplication

    F = 3,
    
    Pf2 = hd(fextended2affine_batch(
               [fextended_mul(Pfe, F)])),
    Pm2 = hd(mextended2affine_batch(
               [mextended_mul(Pme, F)])),
    Pf2b = m2f(Pm2),
    {Pf, Pf2, Pf2b},
    success;
test(3) ->
    %point encoding.

    %io:fwrite(mgen_point()),

    io:fwrite("before gen point\n"),
    Pf = fgen_point(),

    E = fencode_point(Pf),
    Pf = fdecode_point(E),
    io:fwrite("before affine 2 extended\n"),
    EPf = faffine2extended(Pf),
    io:fwrite("before extended double\n"),
    Pf2 = fextended_double(fextended_double(EPf)),
    io:fwrite("before mdecode\n"),
    Pm = mdecode_point(E),
    E = mencode_point(Pm),
    io:fwrite("before second extended double\n"),
    EPm = maffine2extended(Pm),
    Pm2 = mextended_double(mextended_double(EPm)),
    io:fwrite("before m2f\n"),
    Pf22 = m2f(Pm2),
    io:fwrite("before feq\n"),
   
    true = feq(m2f(mdecode_point(E)), fdecode_point(E)),
 
    Pf1 = m2f(Pm),
    true = feq(Pf1, Pf),
    SameBool = feq(Pf2, Pf22),
    if
        SameBool -> ok;
        true -> io:fwrite({fextended2affine_batch([Pf2, Pf22])})
    end,
    io:fwrite("after feq\n"),
    %io:fwrite({E, Pm, Pf}),
    E = mencode_point(Pm),

    #affine{x = Xm, y = Ym} = Pm,
    Xf = decode(Xm),
    Yf = decode(Ym),
    Pf = #affine{x = Xf, y = Yf},

    success;
test(4) ->
    %check group operations hold
%P * 5 * 7 = P * 7 * 5.
%P*5 + P*7 = P*3 + P*9.

    %first with normal integers.
    F = faffine2extended(fgen_point()),
    F5 = fextended_mul(F, 5),
    F7 = fextended_mul(F, 7),
    F35a = fextended_mul(F5, 7),
    F35b = fextended_mul(F7, 5),
    [F35, F35] = 
        fextended2affine_batch([F35a, F35b]),

    F3 = fextended_mul(F, 3),
    F9 = fextended_mul(F, 9),

    F12a = fextended_add(F5, F7),
    F12b = fextended_add(F3, F9),
    [F12, F12] = 
        fextended2affine_batch([F12a, F12b]),
    true = fis_on_curve(F35),
    true = fis_on_curve(F12),

    %now montgomery version
    M = maffine2extended(mgen_point()),
    M5 = mextended_mul(M, 5),
    M7 = mextended_mul(M, 7),
    M35a = mextended_mul(M5, 7),
    M35b = mextended_mul(M7, 5),
    [M35, M35] = 
        mextended2affine_batch([M35a, M35b]),

    M3 = mextended_mul(M, 3),
    M9 = mextended_mul(M, 9),

    M12a = mextended_add(M5, M7),
    M12b = mextended_add(M3, M9),
    [M12, M12] = 
        mextended2affine_batch([M12a, M12b]),
    true = mis_on_curve(M35),
    true = mis_on_curve(M12),

    success.

    
    

