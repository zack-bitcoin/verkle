var fr = (function(){
    //this is the finite field that has the same number of elements as the elliptic curve group.
    const IN = 71336056475231800826343715077027849978041630819377026201054086228062141447707n;//neg(inverse(N)), mod R.
    const N = 7237005577332262213973186563042994240857116359379907606001950938285454250989n;//order of the elliptic curve group ed25519, div 8.
    const R = 115792089237316195423570985008687907853269984665640564039457584007913129639936n;//2^256
    const R2 = 1627715501170711445284395025044413883736156588369414752970002579683115011841n;// r*r mod N

    function redc(x){
        var tb = x % R;
        var m = (tb * IN) % R;
        var t2 = (x + (m * N)) / R;
        if (t2 > N){return (t2 - N);}
        else{return(t2)};
    };
    function decode(x){
        return(redc(x));
    };
    function montgomery_mul(x, y){
        return(redc(x*y));
    };
    function encode(x){
        if((x > N)||(x < 0)){
            return(["error", "can't montgomery encode outside of bounds"]);
        } else {
            return(redc(R2 * x));
        };
    };
    function order(){
        var x = N;
        return(x);
    };
    function mul(a, b){
        var c = a * b % N;
        return(c);
    };
    function sub(a, b) {
        var c = a - b;
        if(c > 0){
            return(c);
        } else {
            return(N + c);
        };
    };
    function neg(a) {
        return(N - a);
    };
    function add(a, b){
        var c = a + b;
        if(c < N) {
            return(c);
        } else {
            return(c - N);
        };
    };
    function dot(l, m){
        var r = [];
        for(var i = 0; i<l.length; i++){
            r.push(mul(l[i], m[i]));
        };
        return(add_all(r));
    };
    function add_all(l){
        var s = 0n;
        for(var i = 0; i<l.length; i++){
            s = add(s, l[i]);
        };
        return(s);
    };
    function inv(a){
        return(finite_inverse.doit(a, N));
    };
    function batch_inverse(l){
        return(finite_inverse.batch(l, N));
    };
    function pow(X, P) {
        if(P == 0){ return(1n);}
        else if(P == 1){ return(X);}
        else if((P % 2n) == 0){
            return(pow(mul(X, X), P / 2n));
        } else {
            return(mul(X, pow(mul(X, X), P / 2n)));
        };
    };
    function sqrt(A){
        //var V = (A * 2) ** ((N - 5) / 8);
        var V = powmod(A*2n, ((N - 5n) / 8n));
        var AV = mul(A, V);
        var I = mul(mul(2n, AV), V);
        var R = mul(AV, fsub(I, 1n));
        return([R, fneg(R)]);
    };
    function is_positive(N){
        var M = encode(N);
        return((M % 2n) == 0);
    };

    function batch_inverse_test(){
        var l = [2n,3n,4n,5n,6n];
        var inverse = batch_inverse(l);
        var l2 = batch_inverse(inverse);
        var ones = [];
        for(var i=0; i< l2.length; i++){
            ones.push(mul(l[i], inverse[i]));
        }
        return(ones);
    };

    return({
        decode: decode,
        encode:encode,
        order: order,
        mul: mul,
        sub: sub,
        neg: neg,
        add: add,
        inv: inv,
        pow: pow,
        sqrt: sqrt,
        is_positive: is_positive,
        batch_inverse: batch_inverse,
        add_all: add_all,
        batch_inverse_test: batch_inverse_test,
        dot: dot
    });
})();

