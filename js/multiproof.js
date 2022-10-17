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
        
    //B = <<C1:256, C2:256, R:256,
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
    function commit(rs, xs){//xs is points.
        return(multi_exponent.doit(rs, xs));
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
        //for the fast version of verkle proofs, that include all 256 elements of the vector commitment, no bullet proof.
        var commitg = co[0];
        var ng2 = co[1];
        var gs = precomputes.ghq()[0];
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
        var ag = commit(ng2, gs);
        var [rids, g2] = calc_G2_2(r, t, ys, zs);
        var commit_e = multi_exponent.doit(rids, commits);
        var commit_g_sub_e = points.sub(commitg, commit_e);
        var bool2 = points.eq(commit_g_sub_e, ag);
        if(!(bool2)){
            return(["error", "multiproof error"]);
        };
        var ab = fr.dot(ng2, ev);
        if(!(0n === fr.add(g2, ab))){
            return(["error", "multiproof error2"]);
        };
        return(true);
    };
    function verify_unused(co, commits, zs, ys){
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
        var proof_old =
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
        var proof0 =
["C1eYTCcJCer6jdziv52yKe/7HGqHIJLIN2byEizssgK9N+ui6FK8n/7qV/shOiWxTuVS10PCtNZRNBjP0W7TfGRC0XdMLwoTda9QnQWy1wh+tWVtEOjryxai9V++ses5xGdvBVejQWHaUbl4Gt+h6O9/Kzg/BcID7abDWNxRnAI=",
  ["G3VoQ+woRNAEQd1B71JmjOruFMs12LOfS+d0+zSQsA4=",
   "58l/eJ01xUmSPN2R4hm/Y70cdtQcGxVTSO48vierEQE=",
   "oPKMCmmlWBv21NSEtNr2T5BK190DXnYGRfUEgRrGcgM=",
   "WRuanDQV7OxZbcx3hpsuPGN4OOfqoNe5QfzMQw3h0wU=",
   "EkSnLgCFf769BcRqWFxmKDammfDR4zhtPgOVBgD8NAg=",
   "y2y0wMv0EpAhnrtdKh2eFAnU+vm4JpogOwpdyfIWlgo=",
   "hJXBUpdkpmGFNrNQ/N3VANwBXAOgafvTNxEljOUx9ww=",
   "Pb7O5GLUOTPpzqpDzp4N7a4vvQyHrFyHNBjtTthMWA8=",
   "CRPmGRThuqx2yqqTwWVmxIFdHhZu7706MR+1EctnuQE=",
   "wjvzq99QTn7aYqKGkyaesFSLfx9VMh/uLSZ91L2CGgQ=",
   "e2QAPqvA4U8++5l5ZefVnCe54Cg8dYChKi1Fl7CdewY=",
   "NI0N0HYwdSGik5FsN6gNifrmQTIjuOFUJzQNWqO43Ag=",
   "7bUaYkKgCPMFLIlfCWlFdc0UozsK+0IIJDvVHJbTPQs=",
   "pt4n9A0QnMRpxIBS2yl9YaBCBEXxPaS7IEKd34jung0=",
   "cjM/Kb8cHT73v4CizvDVOHNwZU7YgAVvHUllonsJAAA=",
   "K1xMu4qMsA9bWHiVoLENJUaexle/w2YiGlAtZW4kYQI=",
   "5IRZTVb8Q+G+8G+IcnJFERnMJ2GmBsjVFlf1J2E/wgQ=",
   "na1m3yFs17IiiWd7RDN9/ev5iGqNSSmJE1696lNaIwc=",
   "VtZzce3baoSGIV9uFvS06b4n6nN0jIo8EGWFrUZ1hAk=",
   "D/+AA7lL/lXquVZh6LTs1ZFVS31bz+vvDGxNcDmQ5Qs=",
   "yCeOlYS7kSdOUk5UunUkwmSDrIZCEk2jCXMVMyyrRg4=",
   "lHylyjXIEqHbTU6krTx9mTexDZApVa5WBnrd9R7GpwA=",
   "TaWyXAE4pnI/5kWXf/20hQrfbpkQmA8KA4GluBHhCAM=",
   "Bs6/7synOUSjfj2KUb7scd0M0KL32nC9/4dtewT8aQU=",
   "v/bMgJgXzRUHFzV9I38kXrA6MazeHdJw/I41PvcWywc=",
   "eB/aEmSHYOdqryxw9T9cSoNokrXFYDMk+ZX9AOoxLAo=",
   "MUjnpC/387jORyRjxwCUNlaW876so5TX9ZzFw9xMjQw=",
   "6nD0Nvtmh4oy4BtWmcHLIinEVMiT5vWK8qONhs9n7g4=",
   "tsULbKxzCATA2xumjIgk+vvxtdF6KVc+76pVScKCTwE=",
   "b+4Y/nfjm9UjdBOZXklc5s4fF9thbLjx67EdDLWdsAM=",
   "KBcmkENTL6eHDAuMMAqU0qFNeORIrxml6Ljlzqe4EQY=",
   "4T8zIg/DwnjrpAJ/AsvLvnR72e0v8npY5b+tkZrTcgg=",
   "mmhAtNoyVkpPPfpx1IsDq0epOvcWNdwL4sZ1VI3u0wo=",
   "U5FNRqai6Ruz1fFkpkw7lxrXmwD+dz2/3s09F4AJNQ0=",
   "DLpa2HESfe0WbulXeA1zg+0E/Qnlup5y29QF2nIklg8=",
   "2A5yDSMf/makaemna9TLWsAyXhPM/f8l2NvNnGU/9wE=",
   "kTd/n+6OkTgIAuGaPZUDR5NgvxyzQGHZ1OKVX1haWAQ=",
   "SmCMMbr+JApsmtiND1Y7M2aOICaag8KM0eldIkt1uQY=",
   "A4mZw4VuuNvPMtCA4RZzHzm8gS+BxiNAzvAl5T2QGgk=",
   "vLGmVVHeS60zy8dzs9eqCwzq4jhoCYXzyvftpzCrews=",
   "ddqz5xxO336XY79mhZji994XREJPTOamx/61aiPG3A0=",
   "QS/LHM5aYPgkX7+2eF87z7FFpUs2j0daxAV+LRbhPQA=",
   "+lfYrpnK88mI97apSiBzu4RzBlUd0qgNwQxG8Aj8ngI=",
   "s4DlQGU6h5vsj66cHOGqp1ehZ14EFQrBvRMOs/sWAAU=",
   "bKny0jCqGm1QKKaP7qHikyrPyGfrV2t0uhrWde4xYQc=",
   "JdL/ZPwZrj60wJ2CwGIagP38KXHSmswntyGeOOFMwgk=",
   "3voM98eJQRAYWZV1kiNSbNAqi3q53S3bsyhm+9NnIww=",
   "lyMaiZP51OF78YxoZOSJWKNY7IOgII+OsC8uvsaChA4=",
   "Y3gxvkQGVlsJ7Yy4V6viL3aGTY2HY/BBrTb2gLmd5QA=",
   "HKE+UBB26SxthYSrKWwaHEm0rpZuplH1qT2+Q6y4RgM=",
   "1clL4tvlfP7QHXye+yxSCBziD6BV6bKopkSGBp/TpwU=",
   "jvJYdKdVENA0tnORze2J9O4Pcak8LBRco0tOyZHuCAg=",
   "RxtmBnPFo6GYTmuEn67B4ME90rIjb3UPoFIWjIQJago=",
   "AERzmD41N3P85mJ3cW/5zJRrM7wKstbCnFneTnckyww=",
   "uWyAKgqlykRgf1pqQzAxuWeZlMXx9Dd2mWCmEWo/LA8=",
   "hcGXX7uxS77telq6NveJkDrH9c7YN5kplmdu1FxajQE=",
   "Puqk8YYh349RE1KtCLjBfA31Vti/evrckm42l0917gM=",
   "9xKyg1KRcmG1q0mg2nj5aOAiuOGmvVuQj3X+WUKQTwY=",
   "sDu/FR4BBjMZREGTrDkxVbNQGeuNAL1DjHzGHDWrsAg=",
   "aWTMp+lwmQR93DiGfvpoQYZ+evR0Qx73iIOO3yfGEQs=",
   "Io3ZObXgLNbgdDB5ULugLVms2/1bhn+qhYpWohrhcg0=",
   "27Xmy4BQwKdEDShsInzYGSzaPAdDyeBdgpEeZQ380w8=",
   "pwr+ADJdQSHSCCi8FUMx8f4HnhAqDEIRf5jmJwAXNQI=",
   "YDMLk/3M1PI1oR+v5wNp3dE1/xkRT6PEe5+u6vIxlgQ=",
   "GVwYJck8aMSZOReiucSgyaRjYCP4kQR4eKZ2reVM9wY=",
   "0oQlt5Ss+5X90Q6Vi4XYtXeRwSzf1GUrda0+cNhnWAk=",
   "i60ySWAcj2dhagaIXUYQokq/IjbGF8fecbQGM8uCuQs=",
   "RNY/2yuMIjnFAv56LwdIjh3tgz+tWiiSbrvO9b2dGg4=",
   "ECtXEN2Yo7JS/v3KIs6gZfAa5UiUnYlFa8KWuLC4ewA=",
   "yVNkoqgIN4S2lvW99I7YUcNIRlJ74Or4Z8lee6PT3AI=",
   "gnxxNHR4ylUaL+2wxk8QPpZ2p1tiI0ysZNAmPpbuPQU=",
   "O6V+xj/oXSd+x+SjmBBIKmmkCGVJZq1fYdfuAIkJnwc=",
   "9M2LWAtY8fjhX9yWatF/FjzSaW4wqQ4TXt62w3skAAo=",
   "rfaY6tbHhMpF+NOJPJK3Ag8Ay3cX7G/GWuV+hm4/YQw=",
   "Zh+mfKI3GJypkMt8DlPv7uEtLIH+LtF5V+xGSWFawg4=",
   "MnS9sVNEmRU3jMvMARpIxrRbjYrlcTItVPMODFR1IwE=",
   "65zKQx+0LOeaJMO/09p/soeJ7pPMtJPgUPrWzkaQhAM=",
   "pMXX1eojwLj+vLqypZu3nlq3T52z9/STTQGfkTmr5QU=",
   "Xe7kZ7aTU4piVbKld1zvii3lsKaaOlZHSghnVCzGRgg=",
   "Fhfy+YED51vG7amYSR0ndwATErCBfbf6Rg8vFx/hpwo=",
   "zz//i01zei0qhqGLG95eY9NAc7lowBiuQxb32RH8CA0=",
   "iGgMHhnjDf+NHpl+7Z6WT6Zu1MJPA3phQB2/nAQXag8=",
   "VL0jU8rvjngbGpnO4GXvJnmcNcw2RtsUPSSHX/cxywE=",
   "DeYw5ZVfIkp/spDBsiYnE0zKltUdiTzIOStPIupMLAQ=",
   "xg4+d2HPtRvjSoi0hOde/x74994EzJ17NjIX5dxnjQY=",
   "fzdLCS0/Se1G43+nVqiW6/ElWejrDv8uMznfp8+C7gg=",
   "OGBYm/iu3L6qe3eaKGnO18RTuvHSUWDiL0CnasKdTws=",
   "8YhlLcQecJAOFG+N+ikGxJeBG/u5lMGVLEdvLbW4sA0=",
   "vd18YnUr8QmcD2/d7fBem2qvfASh1yJJKU438KfTEQA=",
   "dgaK9ECbhNv/p2bQv7GWhz3d3Q2IGoT8JVX/sprucgI=",
   "Ly+XhgwLGK1jQF7DkXLOcxALPxdvXeWvIlzHdY0J1AQ=",
   "6FekGNh6q37H2FW2YzMGYOM4oCBWoEZjH2OPOIAkNQc=",
   "oYCxqqPqPlArcU2pNfQ9TLZmASo946cWHGpX+3I/lgk=",
   "Wqm+PG9a0iGPCUWcB7V1OImUYjMkJgnKGHEfvmVa9ws=",
   "E9LLzjrKZfPyoTyP2XWtJFzCwzwLaWp9FXjngFh1WA4=",
   "3ybjA+zW5myAnTzfzDwG/C7wJEbyq8swEn+vQ0uQuQA=",
   "mE/wlbdGej7kNTTSnv096AEehk/Z7izkDoZ3Bj6rGgM=",
   "UXj9J4O2DRBIzivFcL511NRL51jAMY6XC40/yTDGewU=",
   "CqEKuk4moeGrZiO4Qn+twKd5SGKndO9KCJQHjCPh3Ac=",
   "w8kXTBqWNLMP/xqrFEDlrHqnqWuOt1D+BJvPThb8PQo=",
   "fPIk3uUFyIRzlxKe5gAdmU3VCnV1+rGxAaKXEQkXnww=",
   "NRsycLF1W1bXLwqRuMFUhSADbH5cPRNl/qhf1PsxAA8=",
   "AXBJpWKC3M9kKwrhq4itXPMwzYdDgHQY+68nl+5MYQE=",
   "uphWNy7yb6HIwwHUfUnlSMZeLpEqw9XL97bvWeFnwgM=",
   "c8FjyflhA3MsXPnGTwodNZmMj5oRBjd/9L23HNSCIwY=",
   "LOpwW8XRlkSQ9PC5IctUIWy68KP4SJgy8cR/38adhAg=",
   "5RJ+7ZBBKhb0jOis84uMDT/oUa3fi/nl7ctHorm45Qo=",
   "njuLf1yxvedXJeCfxUzE+REWs7bGzlqZ6tIPZazTRg0=",
   "V2SYESghUbm7vdeSlw385eRDFMCtEbxM59nXJ5/upw8=",
   "I7mvRtkt0jJJudfiitRUvbdxdcmUVB0A5OCf6pEJCQI=",
   "3OG82KSdZQStUc/VXJWMqYqf1tJ7l36z4OdnrYQkagQ=",
   "lQrKanAN+dUQ6sbILlbElV3NN9xi2t9m3e4vcHc/ywY=",
   "TjPX/Dt9jKd0gr67ABf8gTD7mOVJHUEa2vX3MmpaLAk=",
   "B1zkjgftH3nYGrau0tczbgMp+u4wYKLN1vy/9Vx1jQs=",
   "wITxINNcs0o8s62hpJhrWtZWW/gXowOB0wOIuE+Q7g0=",
   "jNkIVoRpNMTJrq3xl1/EMamEvAH/5WQ00ApQe0KrTwA=",
   "RQIW6E/Zx5UtR6XkaSD8HXyyHQvmKMbnzBEYPjXGsAI=",
   "/iojehtJW2eR35zXO+EzCk/gfhTNayebyRjgACjhEQU=",
   "t1MwDOe47jj1d5TKDaJr9iEO4B20rohOxh+owxr8cgc=",
   "cHw9nrIoggpZEIy932Kj4vQ7QSeb8ekBwyZwhg0X1Ak=",
   "KaVKMH6YFdy8qIOwsSPbzsdpojCCNEu1vy04SQAyNQw=",
   "4s1XwkkIqa0gQXujg+QSu5qXAzppd6xovDQADPNMlg4=",
   "riJv9/oUKieuPHvzdqtrkm3FZENQug0cuTvIzuVn9wA=",
   "Z0t8icaEvfgR1XLmSGyjfkDzxUw3/W7PtUKQkdiCWAM=",
   "IHSJG5L0UMp1bWrZGi3bahMhJ1YeQNCCsklYVMuduQU=",
   "2ZyWrV1k5JvZBWLM7O0SV+ZOiF8FgzE2r1AgF764Ggg=",
   "ksWjPynUd209nlm/vq5KQ7l86WjsxZLpq1fo2bDTewo=",
   "S+6w0fRDCz+hNlGykG+CL4yqSnLTCPScqF6wnKPu3Aw=",
   "BBe+Y8CznhAFz0ilYjC6G1/Yq3u6S1VQpWV4X5YJPg8=",
   "0GvVmHHAH4qSykj1VfcS8zEGDYWhjrYDomxAIokknwE=",
   "iZTiKj0ws1v2YkDoJ7hK3wQ0bo6I0Re3nnMI5Xs/AAQ=",
   "Qr3vvAigRi1a+zfb+XiCy9dhz5dvFHlqm3rQp25aYQY=",
   "++X8TtQP2v69ky/Oyzm6t6qPMKFWV9odmIGYamF1wgg=",
   "tA4K4Z9/bdAhLCfBnfrxo329kao9mjvRlIhgLVSQIws=",
   "bTcXc2vvAKKFxB60b7spkFDr8rMk3ZyEkY8o8EarhA0=",
   "JmAkBTdflHPpXBanQXxhfCMZVL0LIP43jpbwsjnG5Q8=",
   "8rQ7OuhrFe12WBb3NEO6U/ZGtcbyYl/rip24dSzhRgI=",
   "q91IzLPbqL7a8A3qBgTyP8l0FtDZpcCeh6SAOB/8pwQ=",
   "ZAZWXn9LPJA+iQXd2MQpLJyid9nA6CFShKtI+xEXCQc=",
   "HS9j8Eq7z2GiIf3PqoVhGG/Q2OKnK4MFgbIQvgQyagk=",
   "1ldwghYrYzMGuvTCfEaZBEL+OeyObuS4fbnYgPdMyws=",
   "j4B9FOKa9gRqUuy1TgfR8BQsm/V1sUVsesCgQ+pnLA4=",
   "W9WUSZOnd373TewFQs4pyOdZ/P5c9KYfd8doBt2CjQA=",
   "FP6h214XC1Bb5uP4E49htLqHXQhENwjTc84wyc+d7gI=",
   "zSavbSqHniG/ftvr5U+ZoI21vhEremmGcNX4i8K4TwU=",
   "hk+8//X2MfMiF9PetxDRjGDjHxsSvco5bdzATrXTsAc=",
   "P3jJkcFmxcSGr8rRidEIeTMRgST5/yvtaeOIEajuEQo=",
   "+KDWI43WWJbqR8LEW5JAZQY/4i3gQo2gZupQ1JoJcww=",
   "scnjtVhG7GdO4Lm3LVN4UdlsQzfHhe5TY/EYl40k1A4=",
   "fR776glTbeHb27kHIRrRKKyapECuyE8HYPjgWYA/NQE=",
   "NkcIfdXCALM/dLH68toIFX/IBUqVC7G6XP+oHHNalgM=",
   "728VD6EylISjDKntxJtAAVL2ZlN8ThJuWQZx32V19wU=",
   "qJgioWyiJ1YHpaDgllx47SQkyFxjkXMhVg05oliQWAg=",
   "YcEvMzgSuydrPZjTaB2w2fdRKWZK1NTUUhQBZUuruQo=",
   "Guo8xQOCTvnO1Y/GOt7nxcp/im8xFzaITxvJJz7GGg0=",
   "0xJKV8/x4coyboe5DJ8fsp2t63gYWpc7TCKR6jDhew8=",
   "n2dhjID+YkTAaYcJAGZ4iXDbTIL/nPjuSClZrSP83AE=",
   "WJBuHkxu9hUkAn/80SawdUMJrovm31miRTAhcBYXPgQ=",
   "Ebl7sBfeieeHmnbvo+fnYRY3D5XNIrtVQjfpMgkynwY=",
   "yuGIQuNNHbnrMm7idagfTulkcJ60ZRwJPz6x9ftMAAk=",
   "gwqW1K69sIpPy2XVR2lXOryS0aebqH28O0V5uO5nYQs=",
   "PDOjZnotRFyzY13IGSqPJo/AMrGC695vOExBe+GCwg0=",
   "CIi6mys6xdVAX10YDfHn/WHuk7ppLkAjNVMJPtSdIwA=",
   "wbDHLfepWKek91QL37Ef6jQc9cNQcaHWMVrRAMe4hAI=",
   "etnUv8IZ7HgIkEz+sHJX1gdKVs03tAKKLmGZw7nT5QQ=",
   "MwLiUY6Jf0psKETxgjOPwtp3t9Ye92M9K2hhhqzuRgc=",
   "7Crv41n5EhzQwDvkVPTGrq2lGOAFOsXwJ28pSZ8JqAk=",
   "pVP8dSVppu0zWTPXJrX+moDTeensfCakJHbxC5IkCQw=",
   "XnwJCPHYOb+X8SrK+HU2h1MB2/LTv4dXIX25zoQ/ag4=",
   "KtEgPaLlujgl7Soa7DyPXiYvPPy6AukKHoSBkXdaywA=",
   "4/ktz21VTgqJhSINvv3GSvlcnQWiRUq+GotJVGp1LAM=",
   "nCI7YTnF4dvsHRoAkL7+NsyK/g6JiKtxF5IRF12QjQU=",
   "VUtI8wQ1da1QthHzYX82I5+4XxhwywwlFJnZ2U+r7gc=",
   "DnRVhdCkCH+0TgnmM0BuD3LmwCFXDm7YEKChnELGTwo=",
   "x5xiF5wUnFAY5wDZBQGm+0QUIis+Uc+LDadpXzXhsAw=",
   "gMVvqWeELyJ8f/jL18Hd5xdCgzQllDA/Cq4xIij8EQ8=",
   "TBqH3hiRsJsJe/gby4g2v+pv5D0M15HyBrX55BoXcwE=",
   "BUOUcOQARG1tE/AOnUluq72dRUfzGfOlA7zBpw0y1AM=",
   "vmuhArBw1z7Rq+cBbwqml5DLplDaXFRZAMOJagBNNQY=",
   "d5SulHvgahA1RN/0QMvdg2P5B1rBn7UM/clRLfNnlgg=",
   "ML27JkdQ/uGY3NbnEowVcDYnaWOo4hbA+dAZ8OWC9wo=",
   "6eXIuBLAkbP8dM7a5ExNXAlVymyPJXhz9tfhstidWA0=",
   "og7WSt4vJYVgDcbNtg2FSNyCK3Z2aNkm896pdcu4uQ8=",
   "bmPtf488pv7tCMYdqtTdH6+wjH9dqzra7+VxOL7TGgI=",
   "J4z6EVusOdBRob0QfJUVDILe7YhE7puN7Ow5+7DuewQ=",
   "4LQHpCYczaG1ObUDTlZN+FQMT5IrMf1A6fMBvqMJ3QY=",
   "md0UNvKLYHMZ0qz2HxeF5Cc6sJsSdF705frJgJYkPgk=",
   "UgYiyL3780R9aqTp8de80PpnEaX5tr+n4gGSQ4k/nws=",
   "Cy8vWolrhxbhApzcw5j0vM2Vcq7g+SBb3whaBnxaAA4=",
   "14NGjzp4CJBu/psst19NlKDD07fHPIIO3A8iyW51YQA=",
   "kKxTIQbom2HSlpMfiSCFgHPxNMGuf+PB2Bbqi2GQwgI=",
   "SdVgs9FXLzM2L4sSW+G8bEYflsqVwkR11R2yTlSrIwU=",
   "Av5tRZ3HwgSax4IFLaL0WBlN99N8BaYo0iR6EUfGhAc=",
   "uyZ712g3Vtb9X3r4/mIsRex6WN1jSAfczitC1Dnh5Qk=",
   "dE+IaTSn6adh+HHr0CNkMb+oueZKi2iPyzIKlyz8Rgw=",
   "LXiV+/8WfXnFkGneouSbHZLWGvAxzslCyDnSWR8XqA4=",
   "+cysMLEj/vJSjGkulqv09GQEfPkYESv2xECaHBIyCQE=",
   "svW5wnyTkcS2JGEhaGws4Tcy3QIAVIypwUdi3wRNagM=",
   "ax7HVEgDJZYavVgUOi1kzQpgPgznlu1cvk4qovdnywU=",
   "JEfU5hNzuGd+VVAHDO6bud2NnxXO2U4Qu1XyZOqCLAg=",
   "3W/heN/iSzni7Uf63a7TpbC7AB+1HLDDt1y6J92djQo=",
   "lpjuCqtS3wpGhj/tr28LkoPpYSicXxF3tGOC6s+47gw=",
   "T8H7nHbCctypHjfggTBDflYXwzGDonIqsWpKrcLTTw8=",
   "GxYT0ifP81U3GjcwdfebVSlFJDtq5dPdrXEScLXusAE=",
   "1D4gZPM+hyebsi4jR7jTQfxyhURRKDWRqnjaMqgJEgQ=",
   "jWct9r6uGvn+SiYWGXkLLs+g5k04a5ZEp3+i9ZokcwY=",
   "RpA6iIoerspi4x0J6zlDGqLOR1cfrvf3o4ZquI0/1Ag=",
   "/7hHGlaOQZzGexX8vPp6BnX8qGAG8ViroI0ye4BaNQs=",
   "uOFUrCH+1G0qFA3vjruy8kcqCmrtM7penZT6PXN1lg0=",
   "cQpiPu1taD+OrATiYHzq3hpYa3PUdhsSmpvCAGaQ9w8=",
   "PV95c5566bgbqAQyVENDtu2FzHy7uXzFlqKKw1irWAI=",
   "9oeGBWrqfIp/QPwkJgR7osCzLYai/N14k6lShkvGuQQ=",
   "r7CTlzVaEFzj2PMX+MSyjpPhjo+JPz8skLAaST7hGgc=",
   "aNmgKQHKoy1HcesKyoXqemYP8JhwgqDfjLfiCzH8ewk=",
   "IQKuu8w5N/+qCeP9m0YiZzk9UaJXxQGTib6qziMX3Qs=",
   "2iq7TZipytAOotrwbQdaUwxrsqs+CGNGhsVykRYyPg4=",
   "pn/Sgkm2S0qcndpAYc6yKt+YE7UlS8T5gsw6VAlNnwA=",
   "X6jfFBUm3xsANtIzM4/qFrLGdL4MjiWtf9MCF/xnAAM=",
   "GNHspuCVcu1jzskmBVAiA4X01cfz0IZgfNrK2e6CYQU=",
   "0fn5OKwFBr/HZsEZ1xBa71ciN9HaE+gTeeGSnOGdwgc=",
   "iiIHy3d1mZAr/7gMqdGR2ypQmNrBVknHdehaX9S4Iwo=",
   "Q0sUXUPlLGKPl7D/epLJx/19+eOomap6cu8iIsfThAw=",
   "/HMh7w5VwDPzL6jyTFMBtNCrWu2P3Asub/bq5Lnu5Q4=",
   "yMg4JMBhQa2AK6hCQBpai6PZu/Z2H23ha/2yp6wJRwE=",
   "gfFFtovR1H7kw581EtuRd3YHHQBeYs6UaAR7ap8kqAM=",
   "OhpTSFdBaFBIXJco5JvJY0k1fglFpS9IZQtDLZI/CQY=",
   "80Jg2iKx+yGs9I4btlwBUBxj3xIs6JD7YRIL8IRaagg=",
   "rGttbO4gj/MPjYYOiB05PO+QQBwTK/KuXhnTsnd1ywo=",
   "ZZR6/rmQIsVzJX4BWt5wKMK+oSX6bVNiWyCbdWqQLA0=",
   "Hr2HkIUAtpbXvXX0K5+oFJXsAi/hsLQVWCdjOF2rjQ8=",
   "6hGfxTYNNxBluXVEH2YB7GcaZDjI8xXJVC4r+0/G7gE=",
   "ozqsVwJ9yuHIUW038SY52DpIxUGvNnd8UTXzvULhTwQ=",
   "XGO56c3sXbMs6mQqw+dwxA12JkuWedgvTjy7gDX8sAY=",
   "FYzGe5lc8YSQglwdlaiosOCjh1R9vDnjSkODQygXEgk=",
   "zrTTDWXMhFb0GlQQZ2ngnLPR6F1k/5qWR0pLBhsycws=",
   "h93gnzA8GChYs0sDOSoYiYb/SWdLQvxJRFETyQ1N1A0=",
   "UzL41OFImaHlrktTLPFwYFktq3AyhV39QFjbiwBoNQA=",
   "DFsFZ624LHNJR0NG/rGoTCxbDHoZyL6wPV+jTvOClgI=",
   "xYMS+XgowESt3zo50HLgOP+IbYMACyBkOmZrEead9wQ=",
   "fqwfi0SYUxYReDIsojMYJdK2zoznTYEXN20z1Ni4WAc=",
   "N9UsHRAI5+d0ECofdPRPEaXkL5bOkOLKM3T7lsvTuQk=",
   "8P05r9t3ernYqCESRrWH/XcSkZ+100N+MHvDWb7uGgw=",
   "qSZHQafnDYs8QRkFGHa/6UpA8qicFqUxLYKLHLEJfA4=",
   "dXtedlj0jgTKPBlVCz0YwR1uU7KDWQblKYlT36Mk3QA=",
   "LqRrCCRkItYt1RBI3f1PrfCbtLtqnGeYJpAbopY/PgM=",
   "58x4mu/TtaeRbQg7r76HmcPJFcVR38hLI5fjZIlanwU=",
   "oPWFLLtDSXn1BQAugX+/hZb3ds44Iir/H56rJ3x1AAg=",
   "WR6Tvoaz3EpZnvcgU0D3cWkl2NcfZYuyHKVz6m6QYQo=",
   "EkegUFIjcBy9Nu8TJQEvXjxTOeEGqOxlGaw7rWGrwgw=",
   "y2+t4h2TA+4gz+YG98FmSg+Bmurt6k0ZFrMDcFTGIw8=",
   "l8TEF8+fhGeuyuZW6oi/IeKu+/PULa/MErrLMkfhhAE=",
   "UO3RqZoPGDkSY95JvEn3DbXcXP27cBCAD8GT9Tn85QM=",
   "CRbfO2Z/qwp2+9U8jgov+ocKvgajs3EzDMhbuCwXRwY=",
   "wj7szTHvPtzZk80vYMtm5lo4HxCK9tLmCM8jex8yqAg=",
   "e2f5X/1e0q09LMUiMoye0i1mgBlxOTSaBdbrPRJNCQs=",
   "NJAG8sjOZX+hxLwVBE3WvgCU4SJYfJVNAt2zAAVoag0="]];
        var commits0 = ["yKiolMzmdNXEknQY+4vbhFNuI3zvIxiD6vGlVtrmb3UsTaxT4ktFxL1QOYdrfcu92zDTmqmKdZXVGapcU075MSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAjgG62SIm4J98Yo9jCq4Fkr6YSvBUInydkBcsJ3PeymI=",
                        "yKiolMzmdNXEknQY+4vbhFNuI3zvIxiD6vGlVtrmb3UsTaxT4ktFxL1QOYdrfcu92zDTmqmKdZXVGapcU075MSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAjgG62SIm4J98Yo9jCq4Fkr6YSvBUInydkBcsJ3PeymI=",
                        "yKiolMzmdNXEknQY+4vbhFNuI3zvIxiD6vGlVtrmb3UsTaxT4ktFxL1QOYdrfcu92zDTmqmKdZXVGapcU075MSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAjgG62SIm4J98Yo9jCq4Fkr6YSvBUInydkBcsJ3PeymI="];

        var proof = decode_helper(proof0);
        //console.log(proof0[1]);
        //console.log(proof[1]);
        var commits = decode_helper(commits0);
        //return(0);
        console.log(proof[0]);
        console.log(proof[1]);
        return(0);
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
