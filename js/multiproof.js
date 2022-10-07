var multiproof = (function(){
    var Extended = nobleEd25519.ExtendedPoint;
    function calc_R(cs, zs, ys){
        //cs is a list of affine points.
        //zs is a list of fr encoded values.
        //ys is a list of fr encoded values.
        var b = [];
        for(var i = 0; i<cs.length; i++){
            b = b.concat(integer_to_array(fr.encode(zs[i]), 32));
            b = b.concat(integer_to_array(fr.encode(ys[i]), 32));
            b = b.concat(integer_to_array(fq.encode(cs[i].x), 32));
            b = b.concat(integer_to_array(fq.encode(cs[i].y), 32));
        };
        var h = hash(b);
        var x = array_to_int(h, 32);
        return(x % fr.order());
    };
    function calc_T(a, r){
        //a is a affine point.
        //r is the result of R, so an integer less than fr.order().
        var b = [];
        b = b.concat(integer_to_array(fq.encode(a.x), 32));
        b = b.concat(integer_to_array(fq.encode(a.y), 32));
        b = b.concat(integer_to_array(fr.encode(r), 32));
        var h = hash(b);
        var x = array_to_int(h, 32);
        return(x % fr.order());
        
    //B = <<C1:256, C2:256, R:256>>,
    //<<R2:256>> = hash:doit(B),
    //fr:encode(R2 rem fr:prime()).

    };
    function mul_r_powers(r, a, c){
        if(c.length === 0){
            return([]);
        };
        return([fr.mul(c[0], a)]
               .concat(mul_r_powers(
                   r, fr.mul(a, r), c.slice(1))));
    };
    function calc_G2_2(r, t, ys, zs){
        var divisors = zs.map(function(z){
            return(fr.sub(t, z))});
        var ids = fr.batch_inverse(divisors);
        var rids = mul_r_powers(r, 1n, ids);
        var l1 = [];
        for(var i =0; i< ys.length; i++){
            l1.push(fr.mul(ys[i], rids[i]));
        };
        var result = fr.add_all(l1);
        return([rids, result]);
    };
    function verify(co, commits, zs, ys){
        var commitg = co[0];
        var open_g_e = co[1];
        var [gs, hs, q] = precomputes.ghq();
        var da = precomputes.da();
        var pa = precomputes.a();
        var domain = precomputes.domain();
        var affines = points.extended2affine_batch(
            [commitg].concat(commits));
        var acg = affines[0];
        var affine_commits = affines.slice(1);
        var r = calc_R(affine_commits, zs, ys);
        var t = calc_T(acg, r);
        var ev = poly.eval_outside_v(
            t, domain, pa, poly.c2e(da, domain));
        console.log(ev[1]);
        console.log(open_g_e);
        console.log(open_g_e[2]);

        //ev[0] and ev[1] are correct.
        var bool = ipa.verify(open_g_e, ev, gs, hs, q);
        if(!(bool)){
            return(["error", "ipa failure"]);
        };
        var [rids, g2] = calc_G2_2(r, t, ys, zs);
        var commit_e = multi_exponent.doit(rids, commits);
        //var commit_neg_e = points.neg(commit_e);
        //var commit_g_sub_e = points.add(commitg, commit_neg_e);
        var commit_g_sub_e = points.sub(commitg, commit_e);
        var bool2 = points.eq(commit_g_sub_e, open_g_e[0]);
        if(!(bool2)){
            return(["error", "multiproof error"]);
        };
        var bool3 = 0n === fr.add(g2, open_g_e[1]);
        if(!(bool3)){
            return(["error", "multiproof error 2 "]);
        };
        return(true);

    };
    function test_r(){
        //looking at multiproof test(9).
        var p = points.gen_point(0);
        //console.log(p);
        var r = calc_R([p], [6n], [5n]);
        return(r === fr.decode(array_to_int(string_to_array(atob("ZH19WZA9dBN/b0UWEjP1Ogiz/UlHXjkIBWvHNeDnVQ8=")).reverse(), 32))); // should be
    };
    function range(a, b){
        if(a >= b){ return([]);}
        return([a].concat(range(a+1, b)));
    };
           
    function test_verify(){
        var many = 3;
        var domain = precomputes.domain();
        var a = domain.slice().reverse().map(
            function(x){return(fr.neg(x)); });
        var as = range(0, many).map(
            function(x){return(a);});
        var zs = range(0, many).map(
            function(x){return(domain[1]); });
        var ys = [];
        for(var i = 0; i<as.length; i++){
            ys.push(poly.eval_e(zs[i], as[i], domain));
        };
        var proof0 =
            ["C1eYTCcJCer6jdziv52yKe/7HGqHIJLIN2byEizssgK9N+ui6FK8n/7qV/shOiWxTuVS10PCtNZRNBjP0W7TfGRC0XdMLwoTda9QnQWy1wh+tWVtEOjryxai9V++ses5xGdvBVejQWHaUbl4Gt+h6O9/Kzg/BcID7abDWNxRnAI=",
             ["8a3mjvoptwNNitQac8/NFNpynradLgSBJKjJPt1olwnoKYv1AOUzY2DlkIgIocH3n/zE0FdtJQkAe9jNth8tECYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAuu9noJkvfLWYtx7kgzwEFqBF8sKa0X8ru6lUTuAQFgQ=",
              "5+RhUSNa3lBjfCAs6wWQzelaM6jdWx5SSQrB+i8oRgE=",
              ["f6bIJkHg4IJtPdJCZILdN8mnzFsHyhqZpSWa/ZwCEF2KQNQuLifXsLHl9vVSlrQoJB4Ckp1V0bYIi5P9tvkKIiYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAiqRj7GmP9ikof+bq82jUHT/q2XBYMfKEDH+fS5HIdC4=",
               "Y+ERhhhph4w0DEmTLZ7Ufz+LMbbFvTGLwYDEJqqlXxVtvl7xe4MNWrnsXINlrVj/ZWYUtqe1sxLsIHZGEi4UeiYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAkLk8k7mG0HdtKW2x4HpZwptGwPt3uQoFRL3qURpOT0=",
               "zo2ZA/nKd9VZRped5lc+yu5dObjOORKVgb7wWWUgFiDfOdTBoLh1haeODu+HP0h9R62yVrz4PFUPWq2FQl+TASYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH4vt7uu7kBE6ZhI8XgNxYRCGeN+6Vlnfgy/I4w0BWw8=",
               "O+O5cS7lG2wV9YPJmWiKZ3yZf7IRA8BkaPv4Uo4uci82N16A9pt3FoxQ/etwuAmmpbD5jWC2cAqE5bakPx/9fSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAj9f+lFs89iTna7/JyDlf8UM1yjX4+0KhctiWOLSD4mo=",
               "8Jz1dNv9uJzSXxDw8UNvS436tSBX5HSvk/uzq6PSK2bmDlVz3Xqf8WyOVLusW3wLpu1Lvy3g+FUKPp3qFJhNVCYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAARE2YMoZ5z1GqKqGo+HyMZf5dJQfMfWxnSiuu3XY2emY=",
               "Mno5Ehacsqmj3+juuEuGQRkr8EU4ZIB1gETbGg4+Sn+2qtfMeWe8O8W+4yDUJL5AltGHNYIFuRihdkII6satDyYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAuLJIs7HLfADqIwiy7QBQFGqVIEttyPvbgF3odxgZ3AI=",
               "8Bv4EKqbslmdPKNEk9mCr4Us+BaHRDf1B2qO/LzvGnkoOq9rcuB1cCeQgJA7bpQiv2Qn5ZZcr1BEs+PjQU04ZyYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAvrg5Z9O19y3R2KAWtlYx1+zsUw+4HroqMNVk78kGJ38=",
    "ZHlH+pUVnnizGEGsmLesRt1//as/8/ah0I8usNCA3iKbHN0NuBO9gvR/XlFrazIjnHOR2yR4LDLzf8x4sLBESyYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA6Wq18Gg60TlQKNmdxOtLrLa92n6hYcyYafm6sh6T4TQ=",
    "HSzrwocxLr43heN8UXN2gMpbcAj5dvGFdWnT/zK/Vx7vGOkOPyqULDWKwe+NskBZ6nkX6lQ4gXl06ArguOFyYiYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHUJC5p74zN/DT9IGcbw8xkBGaRC/Y1y7S5gWb5JtWCQ=",
    "WfQ3X3TAfggkvdBZjJR9PI893fEDi9A7cT5Uwwh0Ay5IUqcbOicbI5ax4IsYKX8bhZ9XLXWYlULeD0/nmG6FMSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAO1uyW049ypyNdCfz6QwpqniuGo4+xX9K5HO4QD/FOzM=",
    "ageEyhMiFckhDd1cvpGkPYtiq6nlR+UV1dx1nbBcqW1eAGpPzQCqg+vc51++BBuqsLZ0SZOkSRxityXeZlHjfCYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAesxORpsB4qE/PgE9pbncW8fUDGwje29oZ3b/aZchIm0=",
    "i+GAaD64chCIOlly351IP3ns+N5DEX4at44T8nDlRhTmMMXsKuMwn4PoGMrv4rUcF++0bvGsoAL5TztuNmQYUyYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACBAhM/n1c8NlWPKDyQNShxHqC8N3Fu0FKNY3HaS03k=",
    "a+V1Uqck3sJ+/XAf+RfJ+RsBngLov3UpyKi5yyL1jljOHLDqzfmrECbZSX9DqGR8SUO+yNxL/GpfvN0xKQcgMyYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAzoCzingiT8BEVzXukxJKpDXH6nIO7mozjj3GpiU+8V0=",
    "1bE/cuoe5CldWwtJOfOHqOvsflAzcDLk2QU0f9X/cBuxxshzkeIDblRXsiZg4qKwFxBPLxMxYI346tlw2fGxdiYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAmDn/x0q/EoA0PfogzGJvRdVLkoeIirLCNc1jQRcc7UQ=",
    "MsGSkSjgRlg1wcWUU7zlR994WbX0vYq3q5AcrzKC3X9OAXkh6fPLaJSbFcHG6ph6ldgNCJCeOZWLSnbLC6ATHSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAALquom5rrAdTo6QaJfIzp+0bcZXLLQvAXaY1O0/p3v1A=",
    "VQFB4wGJKlMJNo7Lulb+39QfN7k+X5N3xKPMCeBN42rpZE3CFM3uc8PddpwoW9AWm1ATMpybKcs7QLWft8uoYSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA0jFNfiIbS/O4KgGx3CBJnoJihCn0QXNhZGry9NW7Oz4=",
    "ic0pUNHvMN8/h3OJrquji6+PAkSESgFym3GZXVKe9E2F61ZLvXWDW7j6ywungSem9Sb0X0lJDZl9QKIREfDCMSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADXPYElgxuGwTY4jaNEplu0Rggpp1f4YrOj9q7MmLKF4="],
              "7exa5FO+IKBA612HjUa3GIETl9pfLnNfmJBV4fp79gc=",
              "rWelWwadiAKNlPAkKX9xnc8Jj/tS9760I7vXYk9FbAo="]];
        var commits0 = ["yKiolMzmdNXEknQY+4vbhFNuI3zvIxiD6vGlVtrmb3UsTaxT4ktFxL1QOYdrfcu92zDTmqmKdZXVGapcU075MSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAjgG62SIm4J98Yo9jCq4Fkr6YSvBUInydkBcsJ3PeymI=",
                        "yKiolMzmdNXEknQY+4vbhFNuI3zvIxiD6vGlVtrmb3UsTaxT4ktFxL1QOYdrfcu92zDTmqmKdZXVGapcU075MSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAjgG62SIm4J98Yo9jCq4Fkr6YSvBUInydkBcsJ3PeymI=",
                        "yKiolMzmdNXEknQY+4vbhFNuI3zvIxiD6vGlVtrmb3UsTaxT4ktFxL1QOYdrfcu92zDTmqmKdZXVGapcU075MSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAjgG62SIm4J98Yo9jCq4Fkr6YSvBUInydkBcsJ3PeymI="];

        var proof = decode_helper(proof0);
        //console.log(proof0[1]);
        //console.log(proof[1]);
        var commits = decode_helper(commits0);
        //return(0);
        console.log(verify(proof, commits, zs, ys));
    };

    function decode_helper(x){
        if(x instanceof Array){
            var r = x.map(function(y)
                          {return(decode_helper(y));});
            return(r);
        };
        //console.log(x);
        var a = atob(x);
        if(a.length === 32){
            //is an fr.
            var b = string_to_array(a).reverse();
            var c = array_to_int(b, 32);
            return(fr.decode(c));
        } else if(a.length === 128){
            //must be an extended then.
            var x1 = string_to_array(a);
            var u = fq.decode(array_to_int(x1.slice(0, 32).reverse()));
            var v = fq.decode(array_to_int(x1.slice(32, 64).reverse()));
            var z = fq.decode(array_to_int(x1.slice(64, 96).reverse()));
            var t = fq.decode(array_to_int(x1.slice(96).reverse()));
            var d = new Extended(u, v, z, t);
            return(d);
        } else {
            console.log("weird error in decode helper");
            return("error");
        };
    };
    
    return({
        verify: verify,
        test_r: test_r,
        test_verify: test_verify,
        decode_helper: decode_helper
    });
})();
