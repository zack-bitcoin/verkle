(function(){
    //order of the finite field used to define ed25519.
    //2^255 - 19.
    var Order = fq.order();
    var EllipticGroupOrder = 7237005577332262213973186563042994240857116359379907606001950938285454250989n;//order of the elliptic curve group ed25519, div 8.
    var Extended = nobleEd25519.ExtendedPoint;
    var Point = nobleEd25519.Point;


    function first_three_test() {
        //testing that point addition and doubling are the same as in the erlang version.
        var Base = Extended.fromAffine(Point.BASE);
        var Base2 = Base.add(Base);
        var Base3 = Base2.add(Base);
        var P = ([Base, Base2, Base3]).map(
            function(x) { return(x.toAffine())});
        //console.log([P[2].x, P[2].y]);
        return((46896733464454938657123544595386787789046198280132665686241321779790909858396n == P[2].x) &&
               (8324843778533443976490377120369201138301417226297555316741202210403726505172n == P[2].y));

    }
    console.log(first_three_test());

    var compressed_base_64 =
        "dZ4jcH5gd9CYeZNrreS1t5ylmFYjluSJ4sq8VT+dooc=";
    function decompress_base_test(){
        var r = points.compressed2affine(compressed_base_64);
        console.log(r);
        return(r);
    };
    function test_eq(){
        //testing that addition and doubling calculate the same things, and that the equals function works.
        var base = Extended.fromAffine(Point.BASE);
        var base4 = base.double().double();
        var base4b = base.add(base).add(base).add(base);
        if(!(points.eq(base4, base4b))){
            return(["error", "unequal"]);
        };
        return("success");
    };
    function test_hash(){
        var base = Extended.fromAffine(Point.BASE);
        var h = points.hash(base);
        return(h == 1776483211286933621438884453533311676776004902530881175740560331936951997513n);
    };
    function test_multi_exponent(){
        var base = Extended.fromAffine(Point.BASE);
        var base4 = base.double().double();
        var base4b = multi_exponent.doit(
            [2n, 1n, 1n], [base, base, base]);
        console.log([base4, base4b]);
        if(!(points.eq(base4, base4b))){
            return(["error", "unequal"]);
        };
        return("success");
    };
    console.log(test_eq());
    console.log(test_hash());
    console.log(test_multi_exponent());

})();
