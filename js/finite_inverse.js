var finite_inverse = (function(){
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
        doit: inverse
    });
})();
