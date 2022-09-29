var fq = (function(){
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
    function mul(x, y){
        return(redc(x*y));
    };
    function encode(x){
        if((x > N)||(x < 0)){
            return(["error", "can't montgomery encode outside of bounds"]);
        } else {
            return(redc(R2 * x));
        };
    };

    return({
        decode: decode,
        encode:encode,
        mul: mul
    });
})();
