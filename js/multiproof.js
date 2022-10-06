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
        var ev = poly.eval_outside_v(t, domain, pa, da);
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
        var proof0 = ["qMPkfqj8qjRP793lVYEP3Ioqi8J1A0Vftuwizg+3ViIAW+8ZkQ07Twhrbclf6xOrMMf4LdpbyzQSFc1ZDdiBQPOd9g+jP0imDAeIzBwWP80+v5gK/eoCr8+bhdyLUJoH7LTTdxtvDF5BYVcPreAO34fjrtis6lI2n4QN8xjexEs=",
                     ["PW8kzSwH+0GIXK9M6vcVSB+ei05b+L2BotnIi3m47xZVdMP+2iSHEzHHljlqQdjU8fK2V9QcdwOqn10BGcVwUiYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAANy/wYhqUccn/kamXaBN+WILRH/62TRY32NPBUdhjGUw=",
                      "S6X09IJZxbvCH1BZg9dVKKRpMTFpxfKS0RV6nSbmkQE=",
                      ["9OEC9gBv6mJLtGu+C4STBS/0BZIlQReKE4HSZH+RzwoZNHOpPbj7nKobyqJFBxnYb9PYzG5a1nhfPAQ7CbbKWSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAtnqLMQkQSqns3V4fg103f6q+v7Hg5YfS++qqcHggWmc=",
                       "RX09rr/VrLM5WMf+R2c/kHmro2nntVvS+T18amQA8WJPniapzdl8IM1fIdWZBM7Kipx1xMSXBORqqk3flchYLCYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAT0wqE+nOHzHhBve4fDapKjmozHsdwf4IEGvzPHDXlU0=",
                       "bu85m1bI4EwFvkVBTesippSjfSYCkP5unXiwtZCX1lAM9sNO2uhY1Zx62f+CDcMX+4+/zwhwTm6JMmmQuHikVSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAbKcj/oXWwAP5t6V9wMSKDGXzdPUxk3UCMue/VuJWJ0Y=",
                       "SbM28MclTN+4DFcoJGpoq7HtwWzLpnYf0R4//i/2BF6u+Pf+iJ1bTZvVnQHBuA+ZuODS7tbKFQzuG08SaQnTUCYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAd6zTg45b1KlmCV94FoA2zUDZqcjhWFlBFFXi1VpsKRQ=",
                       "r63OQ3bSiI3AqguyTLlqNdsRLFXP4hkHrBqorcIPgxYU3f+i34xKzxDjM6ODZG1ptokeS2BXLzOJz9lyOxAQeCYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAe+LVlckejF58RZx6Deh6nQWAS2IRZvODIC76jus1VhM=",
                       "epvAgs8RThoFJ/ov/eIEsEp2uUFtITOmVVJ5oYqoumIiR86dTT+Ws4GRt+WffzvQd0VIJYpDhU3Qr4HWone2aiYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAvXU9TEB458ZFv8uNLruUqi9jM57ZUEy4CRflCyXz5ys=",
                       "jl4g9h60aoM5mf6S0tfwuvlg1+boDARroAPDrnOxVwxZ8t9h8/7ePo7GFXDVUmZ+3ZN70JY+rz1C1WQKfCM5DyYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAwkcuuZMBsFEZwScLbbPbkZnE1TX150a4V8AHIaeOfTY=",
                       "IZHb2XzrD4voC8Eio0dWesNi/WFngQYtYmxObUNfkFrRTHwzYELgosKSqp+GgHALPjXTLOPSC8blO/zRLR6ZDyYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA5Klw9YRwqy109uw6lZL6fSd36Ww/dVGQDTh1B0sTAiI=",
                       "dClYg323h1JeLZp3UrW4q0kqf3l6bZ3OOLkinFX5+CnTCQ78g1Sfo6y8rUqMauNb3F9EOPiCqW9cEmEKmEW5JCYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAC/QX1qIE+LZxebU6Rx677c8u7iyDizEECwWMxFzCgQE=",
                       "qU3tTAmlM/bKmrjXh2hTHj+eGj3w45u2zu4kJX80FGNtwEfiHEmMqfkbt9etmJWaOtNVriuagk86Puv52ULmJSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA/V3ul04JRK0NU5xsOSrHPHXS6xB6kO3bb69Ft9VaakM=",
                       "26Pr2fp+12sdlK4DlX89DUsbjee8HBgldJzv8AbmJjTjbFptypBuemXzyiT9V98FbeaTUidZEMNdRMv6bEemNCYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAmpI5wcJ8+N3TheVuula7yLe8ARUxYtrVIkR46uaimVw=",
                       "NvB6JIgxtnX0jKLUEvHhgp71Fc+y5JL6bamwJAG9SEGVHu/guG9E8E42m5uVU+wEV9o1NOCK+MScU05R98nSJyYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAQGQOCgd+6iPKjLT+7vL1vlGencoJiJvtfbbrUyDZiCk=",
                       "GWwg7q5PozNYRaWXq6piurpAGTbcEaAUMZRcOXyAFF8q5pIkmJoDdcc3eWSLtcWZGCyDDSpHq9Yw2zz+7GtSBiYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA0ETQNRK7awaphE9IIc6r223qYXbjqfgeU7tT27moXHc=",
                       "F5gQIf4WboEOCQXzPzz9Lr74a23PaAaoKSflTLwTY2UDs0d7NRfJj3XFBqgTPMJb13Lmpl4HqEhW+rxHVAuNHyYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAATdWmR8gL9PbWUUGBbPxsSPu931FvmFF4HNnFaGCMxRk=",
                       "uB81NhRIqFXL8kWbu2bnM81dQLAuHZBpitjz17yjFSppghIylUeP/RyZfOu5jMjVA8ynQN1aFM7MZl9z96yITSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+U/6Z1J0NvSbiEO4XzU1giTHy7JjbX9fg3jTRAMuEm4=",
                       "K4aGv6+5QtTS67gXiQPcM6SHSbTmeHv8rvSSGNGNwkqRR50glz72NvS6cZewEGsp3TB5dN8GLyAPQtYnJ+OXOyYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAANP4TEVUBflvFmrgs/OoncyUD7srfOx7vLLWfTD5b+DI=",
                       "V95BZsZUP9y7EdtNVy4uKArVFZJvIMen3cMmtnOO5k2RkC30bCt/X1N02rsAyZJCRtrdzbXT+XOeQbtvNplxKSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAhI5NJvvkpM55lSsO1L8sJjIXD/n8ickTxzJu8g2PNDQ="],
                      "iNByzsGYy0dldeMh9+B8XI47DluWkAOmgDAYobfkxQs=",
                      "fMOS73SWctkucXXNcl0VjsFmLguUAhfE7ES4vB49sQM="]];
        var proof = decode_helper(proof0);
        var commits0 = ["JXq81/19PXxfeC0ZEJ4UJaU/60srt2zfimd0T129TgLbfPzTU3rXwmre5rae5dKBEbtNoSGx4iODhqS5GoBHKCYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOGYLxQM+OYgrV+ZFp0P7zE4moV0bIiZsvAaDgtErEW0=",
                       "JXq81/19PXxfeC0ZEJ4UJaU/60srt2zfimd0T129TgLbfPzTU3rXwmre5rae5dKBEbtNoSGx4iODhqS5GoBHKCYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOGYLxQM+OYgrV+ZFp0P7zE4moV0bIiZsvAaDgtErEW0=",
                        "JXq81/19PXxfeC0ZEJ4UJaU/60srt2zfimd0T129TgLbfPzTU3rXwmre5rae5dKBEbtNoSGx4iODhqS5GoBHKCYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOGYLxQM+OYgrV+ZFp0P7zE4moV0bIiZsvAaDgtErEW0="];
        var commits = decode_helper(commits0);
        console.log(zs);
        console.log(ys);
        console.log(proof);
        console.log(commits);
        console.log(verify(proof, commits, zs, ys));
    };

    function decode_helper(x){
        if(x instanceof Array){
            return(x.map(function(y)
                         {return(decode_helper(y));}));
        };
        console.log(x);
        var a = atob(x);
        if(a.length === 32){
            //is an fr.
            var b = string_to_array(a).reverse();
            var c = array_to_int(b, 32);
            return(fr.decode(c));
        } else {
            //must be an extended then.
            var x1 = string_to_array(a);
            var u = fq.decode(array_to_int(x1.slice(0, 32).reverse()));
            var v = fq.decode(array_to_int(x1.slice(32, 64).reverse()));
            var z = fq.decode(array_to_int(x1.slice(64, 96).reverse()));
            var t = fq.decode(array_to_int(x1.slice(96).reverse()));
            var d = new Extended(u, v, z, t);
            return(d);
        };
    };
    
    return({
        verify: verify,
        test_r: test_r,
        test_verify: test_verify
    });
})();
