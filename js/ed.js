var ed = (function(){
    var Order = fq.order();
    var EllipticGroupOrder = 7237005577332262213973186563042994240857116359379907606001950938285454250989n;//order of the elliptic curve group ed25519, div 8.
    var Extended = nobleEd25519.ExtendedPoint;
    var Point = nobleEd25519.Point;

    function add(a, b){
        return(a.add(b));
    };
    function mul(a, b){
        //b is the scalar
        return(a.multiplyUnsafe(b));
    };
    return({
        add: add,
        mul: mul
    });
})();
