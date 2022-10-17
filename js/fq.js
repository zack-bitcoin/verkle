var fq = (function(){

    //we only need montgomery encoding stuff to be able to decode the points in the proof.
    //all the math tools we export are over integers mod the group size. It is not using montgomery encoding.

    const IN = 21330121701610878104342023554231983025602365596302209165163239159352418617883n;
    const N = 57896044618658097711785492504343953926634992332820282019728792003956564819949n;//order of group used to define ed25519. (2^255) - 19
    const R = 115792089237316195423570985008687907853269984665640564039457584007913129639936n;
    const R2 = 1444n;

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
    //function mul(x, y){
    //    return(redc(x*y));
    //};
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
        //var V = (A * 2n) ** ((N - 5n) / 8n);
        var V = pow(A*2n, ((N - 5n) / 8n));
        var AV = mul(A, V);
        var I = mul(mul(2n, AV), V);
        var R = mul(AV, sub(I, 1n));
        return([R, neg(R)]);
    };
    function is_positive(N){
        var M = encode(N);
        return((M % 2n) == 0);
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
        batch_inverse: batch_inverse,
        pow: pow,
        sqrt: sqrt,
        is_positive: is_positive
    });
})();
