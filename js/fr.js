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
    function order(){
        var x = N;
        return(x);
    };
    return({
        decode: decode,
        encode:encode,
        //mul: mul,
        order: order
    });
})();
