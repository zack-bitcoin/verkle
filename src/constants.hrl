

-include("parameters256.hrl").

-define(order, 115792089237316195423570985008687907852837564279074904382605163141518161494337).
-define(sub(A, B), ((A - B + ?order) rem ?order)).%assumes B less than ?order
-define(neg(A), (?order - A)).%assumes A less than ?order
-define(add(A, B), ((A + B) rem ?order)).
-define(mul(A, B), ((A * B) rem ?order)).
-define(add_mod(C), %assumes C is positive and less than ?order
        if (C>= ?order ) -> C - ?order;
           true -> C end).
-define(sub2(A, B), %assumes A and B are positive and less than ?order
        (if(A>=B) -> (A - B); 
           true -> (A + ?order - B) end)).


-record(leaf, { key
	      , value
	      , meta = 0 %meta is data we want to remember that doesn't get hashed into the merkle tree.
	      }).
-record(stem, { root
                , types
                , pointers
                , hashes
	      }).

%for the 4 child version
%-define(nwidth, 4).%children per node
%-define(nindex, 2).%should be log2(width)

-define(nwidth, 256).
-define(nindex, 8).


%-define(root8, 36188356813700178691818544968121959758909550161426798528723736001201041182661).
%-define(root64, 82197185704688442490006447828692191331519280365147330290079205072302121668882).

-define(root, ?root8).

%created in multiproof:make_parameters_jacob/2
-record(p, {e, b, g, h, q, domain, a, da, ls}).

%secp256k1
-define(e, {curve,0,7,
          {55066263022277343669578718895168534326250603453777594175500187360389116729240,
           32670510020758816978083085130507043184471273380659243275938904335757337482424},
          115792089237316195423570985008687907852837564279074904382605163141518161494337,
          115792089237316195423570985008687907853269984665640564039457584007908834671663,
          55594575648329892869085402983802832744385952214688224221778511981742606582254}).


-define(p4, {p, {curve,0,7, 
          {55066263022277343669578718895168534326250603453777594175500187360389116729240,
           32670510020758816978083085130507043184471273380659243275938904335757337482424},
          115792089237316195423570985008687907852837564279074904382605163141518161494337,
          115792089237316195423570985008687907853269984665640564039457584007908834671663,
          55594575648329892869085402983802832744385952214688224221778511981742606582254},
   115792089237316195423570985008687907852837564279074904382605163141518161494337,
   [{11675176786353927734622706391726801482622125499398844182359490766726699263791,
     8116300455602240784546625446432954784250422425461734147796767903380455091569,
     1},
    {66796502670527101909135907971201150643668921160151367298475353259525851301800,
     72372164602202388963607355878567202847525426993081178677395888564978788579302,
     1},
    {111051608952101679800644565444872899803793118452783700354374916456528012771434,
     114034285791653420985405069212161273553205110180325789505887032593493345808472,
     1},
    {71388795820698609561621340575592122718955539708278481626373994932185932999800,
     63939110951459593556301547654968436301424418789939277188490332579054021556339,
     1}],
   [{59085803608703082976662287509796960704228616939691772093782614840272168206907,
     92807739758540477557883417658190424508003563570897447018530236711982590886873,
     1},
    {31298151912749332702819629361708499871474354016162447166655001816551138370167,
     66604130600780005238797582173213060541078779846612087768237861965325574466438,
     1},
    {1053077440918803267170911436643439258195318759315119228710269153598483483116,
     56822260288843474080328647260416055554411074298666494323912230165735974288100,
     1},
    {104520091087991653389560210761089191619445972582670963835951003212326852782690,
     115297599966785973888292541997458356093928549069151513931782057479210049524414,
     1}],
   {11388759732513641896953701617917643802966047219792231977581243629033020747200,
    52564875025467440847446443735112047513952575625786861669318569561021185672300,
    1},
   [1,2,3,4],
   [24,
    115792089237316195423570985008687907852837564279074904382605163141518161494287,
    35,
    115792089237316195423570985008687907852837564279074904382605163141518161494327,
    1],
   [115792089237316195423570985008687907852837564279074904382605163141518161494331,
    2,
    115792089237316195423570985008687907852837564279074904382605163141518161494335,
    6],
   0}).
