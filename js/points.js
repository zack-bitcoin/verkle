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
        var X = string_to_array(atob(X0));
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
            console.log("failed to square root 1");
            return "error";
        } else if (SqrtVV == [0, 0]){
            console.log("failed to square root 2");
            return("error");
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
        var p2 = p.double().double().double();
        return(p2);
    };
    function hash(p){
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

    return({
        affine2compressed: affine2compressed,
        compressed2affine: compressed2affine,
        is_on_curve: is_on_curve,
        hash: hash,
        extended_zero: extended_zero,
        eq: eq
    });
})();
