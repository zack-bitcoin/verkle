var precomputes = (function(){
    function range(a, b){
        //exclusive of b.
        if(a >= b){return([]);};
        return([BigInt(a)].concat(range(a+1, b)));
    };
    function calc_domain(many){
        return(range(1, many+1));
    };

    var cached_domain;
    function domain(){
        if(cached_domain){
            return(cached_domain);
        };
        var x = calc_domain(256);
        cached_domain = x;
        return(x);
    };

    var cached_da;
    function da(){
        if(cached_da){
            return(cached_da);
        };
        var x = poly.calc_da(domain());
        cached_da = x;
        return(x);
    };

    var cached_a;
    function a(){
        if(cached_a){
            return(cached_a);
        };
        var x = poly.calc_a(domain());
        cached_a = x;
        return(x);
    };

    var cached_ghq;
    function ghq(){
        if(cached_ghq){
            return(cached_ghq);
        };
        var x = points.basis(256);
        cached_ghq = x;
        return(x);
    };

    return({
        ghq: ghq,
        da: da,
        a: a,
        domain: domain
    });
})();
