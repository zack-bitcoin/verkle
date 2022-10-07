var ipa = (function(){
//inner product arguments using pedersen commitments.
    //learn more about inner product arguments here https://dankradfeist.de/ethereum/2021/07/27/inner-product-arguments.html

    var Extended = nobleEd25519.ExtendedPoint;
    function commit(rs, xs){//xs is points.
        return(multi_exponent.doit(rs, xs));
    };
    function add(a, b){
        // elliptic addition
        return(a.add(b));
    };
    function mul(a, b){
        //elliptic multiplication. b is the scalar.
        return(b.multiplyUnsafe(a));
    };
    function point_to_entropy(l){
        return(point.hash(l));
    };
    function v_mul(a, bs){
        //a is a scalar. bs is a list of elliptic curve points.
        return(bs.map(function(x){
            return(mul(a, x))}));
    };
    function v_add(as, bs){
        //as and bs are lists of elliptic curve points. returns another list of elliptic curve points.
        var r = [];
        for(var i = 0; i < as.length; i++){
            r.push(add(as[i], bs[i]));
        };
        return(r);
    };
    function get_gn(x, gs){
        if(gs.length === 1){
            return(gs[0]);
        };
        var s2 = Number(BigInt(gs.length) / 2n);
        var gl = gs.slice(0, s2);
        var gr = gs.slice(s2);
        var gr2 = v_mul(x, gr);
        var g2 = v_add(gr2, gl);
        return(get_gn(x, g2));
    };
    function foldh_mul(x, xi, cs){
        if(cs.length === 1){
            return([cs[0]]);
        } else {
            var l = cs[0];
            var r = cs[1];
            return([mul(x, l), mul(xi, r)]
                   .concat(foldh_mul(x, xi, cs.slice(2))));
        };
    };
    function fold_cs(x, xi, cs){
        var cs3 = foldh_mul(x, xi, cs);
        return(fold_cs2(cs3, points.extended_zero()));
    };
    function fold_cs2(l, a){
        if(l.length === 0){
            return(a);
        };
        var b = add(a, l[0]);
        return(fold_cs2(l.slice(1), b));
    };
    function verify(proof, b, g, h, q){
        var [ag0, ab, cs0, an, bn] = proof;
        var simp = points.normalize([ag0].concat(cs0));
        var ag = simp[0];
        var cs = simp.slice(1);
        var c1 = cs.slice(-1)[0];
        var c1b = add(add(ag, commit(b, h)),
                      mul(ab, q));
        var eb = points.eq(c1, c1b);
        if(!(eb)){
            console.log("verify ipa false 1");
            return(false);
        };
        var x = points.hash(c1);
        var xi = fr.inv(x);
        var gn = get_gn(xi, g);
        var hn = get_gn(x, h);
        var cna = add(add(mul(an, gn),
                          mul(bn, hn)),
                      mul(fr.mul(an, bn), q));
        var cnb = fold_cs(x, xi, cs);
        var b2 = points.eq(cna, cnb);
        if(b2){
            return(true);
        };
        console.log("verify ipa false 2");
        return(false);
    };
    function fr_decode(x) {
        var x3 = string_to_array(atob(x)).reverse();
        var x2 = array_to_int(x3, 32);
        return(fr.decode(x2));
    };
    function decode_extendeds(l){
        var r = [];
        var x1;
        var u, v, z, t;
        for(var i = 0; i < l.length; i++){
            x1 = string_to_array(atob(l[i]));
            u = fq.decode(array_to_int(x1.slice(0, 32).reverse()));
            v = fq.decode(array_to_int(x1.slice(32, 64).reverse()));
            z = fq.decode(array_to_int(x1.slice(64, 96).reverse()));
            t = fq.decode(array_to_int(x1.slice(96).reverse()));
            r.push(new Extended(u, v, z, t));
        };
        return(r);
    };
    function decode_proof(proof) {
        var [ag, ab, cs, an, bn] = proof;
        var ab2 = fr_decode(ab);
        var an2 = fr_decode(an);
        var bn2 = fr_decode(bn);
        var t = decode_extendeds([ag].concat(cs));
        var ag2 = t[0];
        var cs2 = t.slice(1);
        return([ag2, ab2, cs2, an2, bn2]);
        //ab, an, bn are 32 byte fr encoded points.
        //ag, and the list cs are elliptic points in 128 byte extended format.
    };

    function test_1(){
        var a0 = [100n,101n,102n,103n,104n,105n,106n,107n];
        var a = a0.reverse();
        var s = a.length;
        var [g, h, q] = points.basis(s);
        var bv = [10n,0n,3n,1n,1n,2n,0n,10n];

        var encoded_proof = [//"d9LapjwYXF5btVsNlC2yO9m/XppuTjzItDZDTiFKfzaF1DllmIiIKtzXPjvYkx/S4ILbC2vEat880xYTTzR/USYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA9jwSrBuH8OnaO82SP4Rqye4l90wbv1So3xB24gV3sWM=",
                             "d9LapjwYXF5btVsNlC2yO9m/XppuTjzItDZDTiFKfzaF1DllmIiIKtzXPjvYkx/S4ILbC2vEat880xYTTzR/USYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA9jwSrBuH8OnaO82SP4Rqye4l90wbv1So3xB24gV3sWM=",
                     "LcyLjiUk7Mo3TKgcIEDO38Dx/////////////////w8=",
                     ["YmgH6zf4ol0YzD75nzYHtGtcGt/4QGPq34MWIYm3MymsnuRXFrTIf0HfPzHOBUvsvF9Y+ms7l8XXctieObifYCYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAawNhFmKjkxRhuc3jfu7Ickcgw12YhUYkAE0L41i2YHE=",
                      "BOoGB6l6k4ftOEAsaYukZKplJ2Fwn/TCQdgWEHtDVkSQNKWSzzOQFi5ae+F9Ikjx/32UQq8jO1u3gwmPdzkcHCYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAgdpH7BogqS2mwDIANLnovz3X81/XuW5UL9zb451zERE=",
                      "WUlrfzZBhNYyPt6VNnScGGWEUlkfBNzkiBAnlZib7V6H1Zqcb/RPAlfBH0vMWyf8pH8xNFm4bvHvIAwyOeAtOiYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAHkd/V0G0zetYsOxImOvnG4VS2HEqE04OYmst5JGMCmk=",
                      "D1xlwNqltbizznvuPzjaFbCt0CazIp5cztqeoTB5Uif6bqcBPC5Z2DwH+hd0u6XdpicKsgPJbppoXq10jUJxAiYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAts7z0zkfriIxtoNjSe+/sVi/GNrlMNfG5mk62qJgPkA=",
                      "9f79KPBRv6mSOiXr+TUBHAWTrKRB+4BJigll3em/TxzI5UOYxxmXO5WE4KIxvaOxqbSDLjiTCa/6gFvZvM+FTiYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA+8qN71cVQHzI+JI3sw29PxtE9cSepRO9HPQCLqvEmRI=",
                      "SlU5zufEKvsKZADB6lA+FQ6caDfcIvLIxuWp+Dru6VAJQxUmvHb6wokxpNBkGORiVlIiwbM8ltPVr2/9VqEjaiYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAASYaohJlzIfLrS+tNnbBDiKhQCTcP8oUA8Olvvns4clg=",
                      "lHgIdVNt1xRMLRZZFF0kaOY8LehuIyKuJ7tv3bVXn0APNfwyUjIoO5z6F2zG8va1TWibEQtEQbO3J9XRG6WzfyYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAOElmE6dDhRkXwtA19fEiHgT6kgrgYRvFqBKirZRXNWc="],
                     "OjYHmVXczy5cPQ2eObhdTFSfPFzcAEycAN8P9SsVAw8=",
                     "nGN7kfLVp8lHCKz7XbEKS7qOXvqax82YlNDw1nj7fA4="];
        var proof = decode_proof(encoded_proof);
        var proof2 = multiproof.decode_helper(encoded_proof);

        var com_bh = commit(bv, h);
        var com_bh2 = points.affine2extended(points.compressed2affine("okhsAVWF8fL4VbSV1/4Qm35qZCJMsCutGoIDUYCu7HY="));
        if(!(points.eq(com_bh, com_bh2))){
            return(["fail", "commit"]);
        };

        var q2 = points.affine2extended(points.compressed2affine("Vv0llW91nmToUwcf8BWHw2Tq9ihsl9pgDgvnjHAWN9s="));
        if(!(points.eq(q, q2))){
            return(["fail", "incorrect q"]);
        };

        var ab2 = 2796;
        var ab = proof[1];
        if(!(ab == ab2)){
            return(["fail", "incorrect ab"]);
        };
        //console.log(mul(q, ab));
        var abq = mul(ab, q);
        var abq2 = points.affine2extended(points.compressed2affine("HII+A/RrxoNdF75iqvfN3VlgybqfbE+JuAnNNbd3TLw="));
        if(!(points.eq(abq, abq2))){
            return(["fail", "incorrect abq"]);
        };

        var ag = proof[0];
        var ag2 = points.affine2extended(points.compressed2affine("tn9KIU5DNrTIPE5uml6/2TuyLZQNW7VbXlwYPKba0nc="));
        if(!(points.eq(ag, ag2))){
            console.log(points.affine2compressed(points.extended2affine(ag)));
            console.log(points.affine2compressed(points.extended2affine(ag2)));
            console.log(ag);
            console.log(ag2);
            return(["fail", "incorrect ag"]);
        };
        
        var agbh = add(ag, commit(bv, h));
        var agbh2 = points.affine2extended(points.compressed2affine("2vxh6uTdiwR4jIM+8ETSCN2bUe+R53n53PqJLFHk+dY="));
        if(!(points.eq(agbh, agbh2))){
            console.log(points.normalize([agbh])[0]);
            console.log(agbh2);
            return(["fail", "incorrect agbh"]);
        };

        var cs = proof[2];
        var c1 = cs.slice(-1)[0];
        var x = points.hash(c1);
        var xi = fr.inv(x);
        if(!(x === 3898199472263723027621061407270843773322283208812533451190715072240125531040n)){
            return(["fail", "bad point hash"]);
        };
        if(!(xi === 2367767890116161245529624526464261783028336926455660932013331042772803303985n)){
            return(["fail", "bad inverse"]);
        };
        

        return(verify(proof, bv, g, h, q));
    };

    return({
        verify: verify,
        test_1: test_1
    });
})();
