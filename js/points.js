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
    function compressed2affine_batch(l){
        var q = l.map(function(x){
            var y = string_to_array(atob(x));
            var b1 = y[0];
            var p = JSON.parse(JSON.stringify(y));
            var s;
            if(b1 > 128){
                p[0] = p[0] - 128;
                s = 1n;
            } else {
                s = 0n;
            };
            var u = fq.decode(array_to_int(p));
            var uu = fq.mul(u, u);
            var duu = fq.sub(1n, fq.mul(D, uu));
            var t = fq.add(1n, uu);
            return([u, s, t, duu]);
        });
        var duus = q.map(function(x){
            return(x[3]);
        });
        var bs = fq.batch_inverse(duus);
        var r = [];
        for(var i = 0; i<bs.length; i++){
            var x = q[i];
            var new_point = decompress_point2(
                x[0], x[1], x[2], bs[i]);
            r.push(new_point);
        };
        return(r);
    };
    function is_on_curve(P){
        var X = P.x;
        var Y = P.y;
        var XX = fq.mul(X, X);
        var YY = fq.mul(Y, Y);
        var XY = fq.mul(XX, YY);
        var first = fq.sub(YY, XX);
        var second = fq.add(1n, fq.mul(D, XY));
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
            //console.log([U, V]);
            //console.log(Point.BASE);
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
        var arr = integer_to_array(x2, 32).reverse();
        if(!(fq.is_positive(y))){
            arr[0] = arr[0] + 128;
        };
        var result = array_to_string(arr);
        return(btoa(result));
    };
    function clear_torsion(p) {
        //console.log(p);
        var p2 = p.double().double().double();
        return(p2);
    };
    function point_hash(p){
        if(p instanceof Extended){
            var p2 = clear_torsion(p);
            var p3 = p2.toAffine();
            var p4 = affine2compressed(p3);//in base64
            var bin = string_to_array(atob(p4));
            //var n = array_to_int(string_to_array(bin).reverse());
            var n = array_to_int(bin);
            var result = (n % EllipticGroupOrder);
            return(result);
        } else {
            //console.log(p);
            return(["error", "hash of this is not implemented"]);
        };
    };
    function a_eq(a, b){
        var a2 = affine2extended(a);
        var b2 = affine2extended(b);
        return(eq(a2, b2));
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
    function sub(a, b){
        return(a.subtract(b));
    };
    function normalize(l){
        return(Extended.normalizeZ(l));
    };
    function gen_point(x) {
        //there are 513 generator points. so x is an integer from 0 to 512.
        var a = integer_to_array(BigInt(x), 32);
        var h = hash(a);
        //console.log(a);
        //console.log(h);
        return gen_point2(h);
    };
    function gen_point2(x){
        //x is 32 bytes. lets see if it decodes into an elliptic point. otherwise, try adding 1 to it, and testing the next to see if it is a valid point.
        //returns is a point in affine format.
        var b = compressed2affine2(x);
        if(b[0] === "error"){
            //console.log("gen point next");
            var n = array_to_int(x);
            var n2 = n+1n;
            var x2 = integer_to_array(n2, 32).reverse();
            //console.log(x);
            //console.log(x2);
            return(gen_point2(x2));
        } else {
            return(b);
        };
    };
    function affine2extended(p){
        if(p instanceof Array){
            return(p.map(function(x){
                return(affine2extended(x))
            }));
        };
        return(Extended.fromAffine(p));
    };
    function extended2affine(p){
        return(p.toAffine());
    };
    function extended2affine_batch(l){
        return(Extended.toAffineBatch(l));
    };
    function basis(s) {
        var g = [];
        var h = [];
        for(var i = 0; i < s; i++){
            g.push(Extended.fromAffine(gen_point(i)));
            h.push(Extended.fromAffine(gen_point(s + i)));
        };
        var q = Extended.fromAffine(gen_point(s * 2));
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
    function test_2(){
        var should_bes = [
            "Zmh6rfhivXdsj8GLjp+OIAiXFIVu4jOzkCpZHQ1fKSU=",
            "AdD6vSUfy74rk7S5J7Jq0qGpkHcVLkXe0eZ4r6RdvsY=",
            "V3j5hdt1TGYoaR9W+trlDGX92+jrLpMDljP++gXUXjI=",
            "kdOCfwUvWktE1f4r7WV8dSJHNl2U+AozywnBQ2oWsSU=",
            "S3gGO5wiTaMRvR0/uWm7oZ5+ke4HtQb5xMQ4gokVVkA=",
            "qudhN387Tx8H2YJ4O5AjFLYanL5sz9+pZVkDnwfjMu0=",
            "k4g01sY2mRcQHBgsWOeDSqh2P+4tNffgZVkHUojGIxE=",
            "9UEex+UeRhWcZUvb3zzCB4WiF7hzhIEO0uVB3AAWlDs="];
        var ids = [0,1,2,3,4,5,6,7];
        for(var i = 0; i<ids.length; i++){
            var affine1 = compressed2affine(should_bes[i]);
            var affine2 = gen_point(ids[i]);
            var e1 = Extended.fromAffine(affine1);
            var e2 = Extended.fromAffine(affine2);
            console.log(eq(e2, e1));
        };
        return(0);
    };
    function test_3(){
        var p0 = "Zmh6rfhivXdsj8GLjp+OIAiXFIVu4jOzkCpZHQ1fKSU=";
        var a0 = compressed2affine(p0);
        var e0 = Extended.fromAffine(a0);
        var h0 = hash(e0);
        var h1 = array_to_int(string_to_array(atob("3EGjINsYRlYMN3Hyv/98ZiQyvZDbWhpzqNy/BTjI8Qs=")).reverse(), 32);
        console.log(h0);
        console.log(fr.decode(h1));

        return(0);
    };
    function test_4(){
        //checking that the q point is correct.
        var c = "FhbEtcjbtEbyafLJcFuFe0pDFTVaUpZpM+aw5R2nSnk=";
        var a0 = compressed2affine(c);
        var e0 = Extended.fromAffine(a0);

        var q = precomputes.ghq()[2];
        var q2 = Extended.fromAffine(gen_point(512));

        console.log(q);
        console.log(e0);
        console.log(eq(q, q2));
        console.log(eq(q, e0));

    };
    return({
        affine2compressed: affine2compressed,
        compressed2affine: compressed2affine,
        compressed2affine_batch: compressed2affine_batch,
        affine2extended: affine2extended,
        extended2affine: extended2affine,
        extended2affine_batch: extended2affine_batch,
        is_on_curve: is_on_curve,
        hash: point_hash,
        extended_zero: extended_zero,
        eq: eq,
        a_eq: a_eq,
        mul: mul,
        add: add,
        sub: sub,
        normalize: normalize,
        gen_point: gen_point,
        basis: basis,
        test_0: test_0,
        test_1: test_1,
        test_2: test_2,
        test_3: test_3,
        test_4: test_4
    });
})();
