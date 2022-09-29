(function(){
    var Order = 57896044618658097711785492504343953926634992332820282019728792003956564819949n;
    var Extended = nobleEd25519.ExtendedPoint;
    var Point = nobleEd25519.Point;

        // -(121665/121666)
    var D = 37095705934669439343138083508754565189542113879843219016388785533085940283555n;

    function first_three_test() {
        var Base = Extended.fromAffine(Point.BASE);
        var Base2 = Base.add(Base);
        var Base3 = Base2.add(Base);
        var P = ([Base, Base2, Base3]).map(
            function(x) { return(x.toAffine())});
        console.log([P[0].x, P[1].x, P[2].x]);
    }
    //first_three_test();

    var compressed_base_64 =
        "dZ4jcH5gd9CYeZNrreS1t5ylmFYjluSJ4sq8VT+dooc=";
    var compressed_base = atob(compressed_base_64);

    function fmul(a, b) {
        var c = a * b % Order;
        return(c);
    };
    function fsub(a, b) {
        var c = a - b;
        if(c > 0){
            return(c);
        } else {
            return(Order + c);
        };
    };
    function fneg(a) {
        return(Order - a);
    };
    function fadd(a, b){
        var c = a + b;
        if(c < Order) {
            return(c);
        } else {
            return(c - Order);
        };
    };
    function finv(a){
        return(inverse(a, Order));
    };
    function inverse(A, N){
        var EEA = eea(A, N);
        if(EEA == "error"){
            return(["error", "inverse does not exist"]);
        } else {
            var [G, S, T] = EEA;
            if(G == 1){
                return((S + N) % N);
            } else {
                return(["error", "inverse does not exist"]);
            };
        };
    };
    function eea(A, B){
        console.log("eea");
        if((A < 1n)||(B<1n)){
            return("undefined");
        };
        return(eea_helper(A, 1n, 0n, B, 0n, 1n));
    };
    function eea_helper(G0, S0, T0, G1, S1, T1){
        if(G1 == 0n){
            return([G0, S0, T0]);
        } else {
            var Q = G0 / G1;
            return(eea_helper(G1, S1, T1,
                              G0 - (Q*G1),
                              S0 - (Q*S1),
                              T0 - (Q*T1)));
        }
    };
    
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
        var UU = fmul(U, U);
        var DUU = fsub(1n, fmul(D, UU));
        var T = fadd(1n, UU);
        var B = finv(DUU);
        return(decompress_point2(U, S, T, B));
    };
    function powmod(X, P) {
        if(P == 0){ return(1n);}
        else if(P == 1){ return(X);}
        else if((P % 2n) == 0){
            return(powmod(fmul(X, X), P / 2n));
        } else {
            return(fmul(X, powmod(fmul(X, X), P / 2n)));
        };
    };
    function sqrt(A){
        //var V = (A * 2n) ** ((Order - 5n) / 8n);
        var V = powmod(A*2n, ((Order - 5n) / 8n));
        var AV = fmul(A, V);
        var I = fmul(fmul(2n, AV), V);
        var R = fmul(AV, fsub(I, 1n));
        return([R, fneg(R)]);
    };
    function is_positive(N){
        var M = fq.encode(N);
        return((M % 2n) == 0);
    };
    function is_on_curve(P){
        var X = P.x;
        var Y = P.y;
        var XX = fmul(X, X);
        var YY = fmul(Y, Y);
        var XY = fmul(XX, YY);
        return((fsub(YY, XX) ==
                fadd(1n, fmul(D, XY))));
    };
    function decompress_point2(U, S, T, B){
        var VV = fmul(T, B);
        var SqrtVV = sqrt(VV);
        if(SqrtVV == "error"){
            console.log("failed to square root 1");
            return "error";
        } else if (SqrtVV == [0, 0]){
            console.log("failed to square root 2");
            return("error");
        } else {
            var [V1, V2] = SqrtVV;
            var SB = (S == 0);
            var S2 = is_positive(V1);
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
        var x = p.x;
        var y = p.y;
        //var s;
        //if(!(is_positive(y))){
        //    s = 1;
        //} else {
        //    s = 0;
        //}
        var x2 = fq.encode(x);
        var arr = integer_to_array(x2, 32);
        if(!(is_positive(y))){
            arr[0] = arr[0] + 128;
        };
        var result = array_to_string(arr);
        return(btoa(result));
    };
    function decompress_base_test(){
        var r = compressed2affine(compressed_base_64);
        console.log(r);
        return(r);
    };

    function point_hash(p){
        if(p instanceof Extended){
            var p2 = p.double().double().double();
            var p3 = affine2compressed(p2);//in base64
            var bin = atob(p3);
            var n = array_to_int(string_to_array(bin));
            return(n % Order);
        } else {
            console.log(p);
            return({"error", "hash of this is not implemented"});
        };
    };
    function point_eq(a, b){
        var c = a.subtract(b);
        var c2 = c.double().double().double();
        return(is_extended_zero(c2));
    };
    function is_extended_zero(e){
        return((e.x == 0) && (e.y == e.z));
    };
})();
