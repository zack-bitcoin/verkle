var finite_inverse = (function(){

    function mul(a, b, N){
        var c = a * b % N;
        return(c);
    };
    function pis(l, N){
        var a = 1n;
        var r = [];
        for(var i = 0; i<l.length; i++){
            var x = mul(l[i], a, N);
            r.push(x);
            a = x;
        };
        return(r);
    };
    function batch(l, n){
        if(l.length === 0){ return([]);}
        
        var v20 = pis(l, n).reverse();
        var all = v20[0];//720
        var v2 = v20.slice(1);//[120,24,6,2]
        var allI = inverse(all, n);//11056......279
        var vi = v2.map(function(v){ return(mul(allI, v, n))});
        //[603..., 265..., 663..., 221...]
        var v3 = (pis(l.reverse(), n)).reverse(); //[720, 360, 120, 30, 6]
        var v4 = v3.slice(1).concat([1n]);//[360, 120, 30, 6, 1]
        var vi2 = ([allI]).concat(vi.reverse());
        //[1105..., 221..., 663..., 265..., 603...]
        var result = [];
        for (var i = 0; i < v4.length; i++){
            result.push(mul(v4[i], vi2[i], n));
        };
        return(result);


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

    return({
        doit: inverse,
        batch: batch
    });
})();
