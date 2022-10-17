var poly = (function(){

    //this part is all for generating parameters

    function base_polynomial_c(intercept){
        //coefficient format
        // x - intercept
        return([fr.neg(intercept), 1n]);
    }
    function mul_scalar(s, p){
        //multiply a polynomial by a scalar.
        var r = [];
        for(var i = 0; i < p.length; i++){
            r.push(fr.mul(s, p[i]));
        };
        return(r);
    };
    function mul_c(a, b){
        //multiplying 2 polynomials in coefficient form.
        if(a.length === 0){
            return([]);
        };
        if(b.length === 0){
            return([]);
        };
        if(a.length === 1){
            return(mul_scalar(a[0], b));
        };
        var x = mul_scalar(a[0], b);
        var y = mul_c(a.slice(1), [0n].concat(b));
        return(add_c(x, y));
    };

    //coefficient format doesn't need to be the same length
    function add_c(a, b){
        //adding 2 polynomials in coefficient form
        if(a.length === 0){
            return(b);
        };
        if(b.length === 0){
            return(a);
        };
        var c = fr.add(a[0], b[0]);
        var rest = add_c(a.slice(1), b.slice(1));
        return([c].concat(rest));
    };
    function mul_c_all(l){
        var p = l[0];
        for(var i = 1; i<l.length; i++){
            p = mul_c(p, l[i]);
        };
        return p;
    };
    function poly_add_all(l){
        var x = [];
        for(var i = 0; i < l.length; i++){
            x = add_c(x, l[i]);
        };
        return(x);
    };
    function remove_element(x, l){
        if(0 === l.length){
            console.log("error!");
            return("error");
        };
        var r = l.slice(1);
        if(x === l[0]){
            return(r);
        };
        return([l[0]].concat(remove_element(x, r)));
    };
    function calc_a(domain){
        var l = domain.map(
            function(d) {
                return(base_polynomial_c(d));
            });
        return(mul_c_all(l));
    };
    function calc_da(domain){
        var base_polys = domain.map(
            function(d){return(base_polynomial_c(d))});
        var forward = calc_da2(base_polys, [[1n]]);
        var backward = calc_da2(base_polys.reverse(),
                                [[1n]]).reverse();
        var l = [];
        for(var i = 0; i<forward.length; i++){
            l.push(mul_c(forward[i], backward[i]));
        };
        return(poly_add_all(l));
    };
    function calc_da2(ps, r){
        if(ps.length === 1){
            return(r.reverse());
        };
        var q = mul_c(ps[0], r[0]);
        return(calc_da2(ps.slice(1), [q].concat(r)));
    };
    function calc_da_old(domain){
        console.log("calc da");
        var x = domain.map(
            function(d){
                console.log(d);
                var domain2 = remove_element(d, domain);
                var y = domain2.map(function(x){
                    return(base_polynomial_c(x));
                });
                return(mul_c_all(y));
            });
        return(poly_add_all(x));
    };
    
    // the rest is for proof evaluation, not just parameters.
    
    function eval_c(x, p){
        //evaluate polynomial p for point x.
        var xa = 1n;
        var acc = 0n;
        for(var i = 0; i < p.length; i++){
            acc = fr.add(fr.mul(p[i], xa), acc);
            xa = fr.mul(x, xa);
        };
        return(acc);
    };
    //evaluation format, inside the domain.
    function eval_e(x, p, d) {
        for(var i = 0; i<p.length; i++){
            if(d[i] === x){
                return(p[i]);
            }
        };
        return(["error", "eval e error"]);
    };
    function eval_outside_v(z, domain, a, da) {
        //this is the first part of eval_outside.
        // z is a point not in domain.
        // a and ad are polynomials precomputed so that this computation can be faster.
        //a(z) * sum(P_i/(DA(domain(i)) * (z - domain(i))))
        var divisors = [];
        for(var i = 0; i < domain.length; i++){
            var x = fr.mul(da[i], fr.sub(z, domain[i]));
            divisors.push(x);
        };
        var ids = fr.batch_inverse(divisors);
        var az = eval_c(z, a);
        var r = ids.map(function(x){
            return(fr.mul(az, x))
        });
        return(r);
    };

    //maybe c2e is only for testing?
    function c2e(p, domain){
        //converts a polynomial to evaluation format.
        //costs (length of polynomial)*(elements in the domain);
        //can be faster if the domain is the roots of unity.
        var r = domain.map(function(x){
            return(eval_c(x, p));
        });
        return(r);
            
    };
    function test_2(){
        var domain = [1n, 2n, 3n, 4n];
        var a = calc_a(domain);
        console.log(a);//should be 
//[24,
// 7237005577332262213973186563042994240857116359379907606001950938285454250939,
// 35,
// 7237005577332262213973186563042994240857116359379907606001950938285454250979,
        // 1]
        var da0 = calc_da(domain);
        console.log(da0);//should be
//[7237005577332262213973186563042994240857116359379907606001950938285454250939,
// 70,
// 7237005577332262213973186563042994240857116359379907606001950938285454250959,
// 4]
        var da = c2e(da0, domain);
        var c = [1n, 0n, 0n, 0n];
        var e = c2e(c, domain);
        var z = 0n;

        console.log(eval_outside_v(z, domain, a, da));
        //[4,
        // 7237005577332262213973186563042994240857116359379907606001950938285454250983,
        // 4,
        // 7237005577332262213973186563042994240857116359379907606001950938285454250988],
        
    };
    function test_3(){
        var l = [[2n,1n,0n,0n],
                 [1n,1n,0n,0n],
                 [0n,1n,0n,0n]];
        var r = mul_c_all(l);
        //should be [0,2,3,1]
        return(r);
    };
    function test_da(){
        var domain = [1n, 2n, 3n, 4n, 5n];
        var da0 = calc_da_old(domain);
        var da1 = calc_da(domain);
        console.log(da0);
        console.log(da1);
        return(0);
    };
    return({
        eval_outside_v: eval_outside_v,
        calc_da: calc_da,
        calc_a: calc_a,
        eval_e: eval_e,
        test_2: test_2,
        test_3: test_3,
        test_da: test_da,
        c2e: c2e
    });
})();
