var points = (function(){
    //order of the finite field used to define ed25519.
    //2^255 - 19.
    var Order = fq.order();
    var EllipticGroupOrder = 7237005577332262213973186563042994240857116359379907606001950938285454250989n;//order of the elliptic curve group ed25519, div 8.
    var Extended = nobleEd25519.ExtendedPoint;
    var Point = nobleEd25519.Point;

    // -(121665/121666)
    // a constant in the definition of the ed25519 elliptic curve.
    var D = 37095705934669439343138083508754565189542113879843219016388785533085940283555n;

    function compressed2affine(X0){
        //base64 encoded to affine.
        var X = string_to_array(atob(X0));
        return(compressed2affine2(X));
    };
    function compressed2affine2(X){
        // array encoded to affine.
        var B1 = X[0];
        var P = JSON.parse(JSON.stringify(X));
        var S;
        if (B1 > 128) {
            P[0] = P[0] - 128;
            S = 1n;
        } else {
            S = 0n;
        };
        var U0 = array_to_int(P);
        var U = fq.decode(U0);
        var UU = fq.mul(U, U);
        var DUU = fq.sub(1n, fq.mul(D, UU));
        var T = fq.add(1n, UU);
        var B = fq.inv(DUU);
        return(decompress_point2(U, S, T, B));
    };
    function is_on_curve(P){
        var X = P.x;
        var Y = P.y;
        var XX = fq.mul(X, X);
        var YY = fq.mul(Y, Y);
        var XY = fq.mul(XX, YY);
        return((fq.sub(YY, XX) ==
                fq.add(1n, fq.mul(D, XY))));
    };
    function decompress_point2(U, S, T, B){
        var VV = fq.mul(T, B);
        var SqrtVV = fq.sqrt(VV);
        if(SqrtVV == "error"){
            return(["error", "sqrt failure 1"]);
        } else if (SqrtVV == [0, 0]){
            return(["error", "sqrt failure 2"]);
        } else {
            var [V1, V2] = SqrtVV;
            var SB = (S == 0);
            var S2 = fq.is_positive(V1);
            var V;
            if(SB == S2){ V = V1; }
            else { V = V2; }
            console.log([U, V]);
            console.log(Point.BASE);
            var P = new Point(U, V);
            var OnCurve = is_on_curve(P);
            if(OnCurve){return(P);}
            else{return(["error", "not on curve"])};
        };
    };
    function affine2compressed(p) {
        if(!(p instanceof Point)){
            return(["error", "wrong type into affine2compressed"]);
        };
        var x = p.x;
        var y = p.y;
        var x2 = fq.encode(x);
        var arr = integer_to_array(x2, 32);
        if(!(fq.is_positive(y))){
            arr[0] = arr[0] + 128;
        };
        var result = array_to_string(arr);
        return(btoa(result));
    };
    function clear_torsion(p) {
        console.log(p);
        var p2 = p.double().double().double();
        return(p2);
    };
    function point_hash(p){
        if(p instanceof Extended){
            var p2 = clear_torsion(p);
            var p3 = p2.toAffine();
            var p4 = affine2compressed(p3);//in base64
            var bin = atob(p4);
            var n = array_to_int(string_to_array(bin).reverse());
            var result = (n % EllipticGroupOrder);
            return(result);
        } else {
            console.log(p);
            return(["error", "hash of this is not implemented"]);
        };
    };
    function eq(a, b){
        var c = a.subtract(b);
        return(is_extended_zero(c));
    };
    function is_extended_zero(e0){
        var e = clear_torsion(e0);
        return((e.x == 0) && (e.y == e.z));
    };
    function extended_zero(){
        return(Extended.ZERO);
    };
    function mul(a, r){
        if(!(a instanceof Extended)){
            return(["error", "error, can only  mupltiply extended points, a"]);
        };
           return(a.multiplyUnsafe(r));
    };
    function add(a, b){
        if(!(a instanceof Extended)){
            return(["error", "error, can only add extended points, a"]);
        };
        if(!(b instanceof Extended)){
            return(["error", "error, can only add extended points, b"]);
        };
        return(a.add(b));
    };
    function normalize(l){
        return(Extended.normalizeZ(l));
    };
    function gen_point(x) {
        //there are 513 generator points. so x is an integer from 0 to 512.
        var a = integer_to_array(x, 32);
        var h = hash(a);
        console.log(a);
        console.log(h);
        return gen_point2(h);
    };
    function gen_point2(x){
        //x is 32 bytes. lets see if it decodes into an elliptic point. otherwise, try adding 1 to it, and testing the next to see if it is a valid point.
        //returns is a point in affine format.
        var b = compressed2affine2(x);
        if(b[0] === "error"){
            console.log("gen point next");
            var n = array_to_int(x);
            var n2 = n+1n;
            var x2 = integer_to_array(n2, 32).reverse();
            console.log(x);
            console.log(x2);
            return(gen_point2(x2));
        } else {
            return(b);
        };
    };
    function basis(s) {
        var g = [];
        var h = [];
        for(var i = 0; i < s; i++){
            g.push(gen_point(i));
            h.push(gen_point(s + i));
        };
        var q = gen_point(s * 2);
        return([g, h, q]);
    };
    function test_0(){
        //testing that we generate the 0th generator point correctly.
        var should_be = "Zmh6rfhivXdsj8GLjp+OIAiXFIVu4jOzkCpZHQ1fKSU=";
        var affine1 = compressed2affine(should_be);
        var affine2 = gen_point(0n);
        console.log(affine1);
        console.log(affine2);
        var e1 = Extended.fromAffine(affine1);
        var e2 = Extended.fromAffine(affine2);
        return(eq(e2, e1));
    };
    function test_1(){
        //testing that we generate the 1st generator point correctly.
        var should_be = "AdD6vSUfy74rk7S5J7Jq0qGpkHcVLkXe0eZ4r6RdvsY=";
        var affine1 = compressed2affine(should_be);
        var affine2 = gen_point(1n);
        console.log(affine1);
        console.log(affine2);
        var e1 = Extended.fromAffine(affine1);
        var e2 = Extended.fromAffine(affine2);
        return(eq(e2, e1));
    };

    return({
        affine2compressed: affine2compressed,
        compressed2affine: compressed2affine,
        is_on_curve: is_on_curve,
        hash: point_hash,
        extended_zero: extended_zero,
        eq: eq,
        mul: mul,
        add: add,
        normalize: normalize,
        gen_point: gen_point,
        test_0: test_0,
        test_1: test_1
    });
})();
