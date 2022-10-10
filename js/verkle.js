var verkle = (function(){
    //from get2.erl
    function compressed_points_list(x){
        var is_array = (x instanceof Array);
        if(is_array){
            if(x.length === 0){
                return([]);
            };
            var h = compressed_points_list(x[0]);
            var t = compressed_points_list(x.slice(1));
            return(h.concat(t));
        };
        var is_string = (typeof(x) === 'string');
        if(is_string){
            var s = atob(x);
            var a = string_to_array(s);
            if(a.length === 32){
                return(a);
            } else {
                return([]);
            }
        };
        return([]);
    };
    //from get2.erl
    function index2domain(zs){
        var r = [];
        for(var i = 0; i<zs.length; i++){
            r.push(zs[i] + 1);
        };
        return(r);
    };
    //get2
    function split3parts(l){
        var a = [];
        var b = [];
        var c = [];
        for(var i = 0; i < l.length; i++){
            a.push(l[i][0]);
            b.push(l[i][1]);
            c.push(l[i][2]);
        };
        return([a, b, c]);
    };
    //ed:a_eq(root1, root2)
    //  points.a_eq

    //verify2
    function fill_points(points, tree, result){
        if(tree.length === 0){
            return([result.reverse(), points]);
        };
        if(tree[0] instanceof Array){
            var [t2, ps2] = fill_points(points, tree[0], []);
            return(fill_points(ps2, tree.slice(1),
                               [t2].concat(result)));
        };
        if(typeof(tree[0]) === 'string'){
            var s = atob(tree[0]);
            var a = string_to_array(a);
            if(a.length === 32){
                return(fill_points(
                    points.slice(1),
                    tree.slice(1),
                    [points[0]].concat(result)));
            };
        };
        return(fill_points(points, tree.slice(1),
                           [tree[0]].concat(result)));
    };
    function leaf_hash(key, val){
        console.log(key);
        console.log(val);
        //hash() takes array of bytes to array of bytes.
        return("unimplemented");

        // sha256(<<Key/binary, Val/binary>>);
            //var bin = string_to_array(atob(p4));
            //var n = array_to_int(bin);
            //var result = (n % EllipticGroupOrder);
            //return(result);
    };
    function unfold(root, rest, r){
        //empty case
        if((rest instanceof Array) &&
           (rest.length === 2) &&
           (rest[1] === 0n)){
            var result = [[root, rest[1], 0n]]
                .concat(r);
            return(result.reverse());
        };
        //leaf case
        if((rest instanceof Array) &&
           (rest.length === 2) &&
           (rest[1] instanceof Array) &&
           (rest[1].length === 2)){
            var key = rest[1][0];
            var val = rest[1][1];
            //var leaf = leaf_new(key, val);
            //var lh = leaf_hash(leaf);
            var lh = leaf_hash(key, val);
            var result = [[root, rest[0], lh]]
                .concat(r);
            return(result.reverse());
        };
        //stem case
        if((rest instanceof Array) &&
           (rest[0] instanceof Array) &&
           (rest[0].length === 2) &&
           (rest[1] instanceof Extended)){
            var p = rest[1];
            var sh = points.hash(p);
            return(unfold(p, rest.slice(1),
                          [[root, rest[0][0], sh]]
                          .concat(r)));
        };
        //finished this sub-branch case.
        if((rest instanceof Array) &&
           (rest.length === 0)){
            return([]);
        };
        //2 sub-branches to unfold case.
        if((rest instanceof Array)){
            var h = rest[0];
            var j = rest.slice(0);
            var first = unfold(root, h, r);
            var second = unfold(root, j, []);
            return(first.concat(second));
        };
        console.log("unfold failure. unhandled case");
        return("error");
    };
    function proof(root, proof){
        var [tree0, commitg0, open0] = proof;
        var [open1, open2, openl, open4, open5] = open0;
        var cpl = compressed_points_list(tree0);
        if(cpl.length === 0){
            console.log("error");
            return(0);
        };
        var list = [commitg0, open1]
            .concat(openl).concat(cpl);
        var list2 = points.affine2extended(
            points.decompress_points_batch(
                list));
        var commitg = list2[0];
        var open1b = list2[1];
        var decompressed2 = list2.slice(2);
        var ol = openl.length;
        var openLb = decompressed2.slice(0, ol);
        var decompressed = decompressed2.slice(ol);
        var tree = fill_points(decompressed, tree0)[0];
        var open = [open1b, open2, openLB, open4, open5];
        var root = tree[0];
        var rest = tree.slice(1);
        var domain = parameters.domain();
        var root1 = decompressed[0];
        if(!(points.a_eq(root1, root))){
            console.log("verify fail unequal roots");
            return(false);
        };
        var tree2 = unfold(root, rest, []);
        var [commits, zs0, ys] = split3parts(tree2);
        var zs1 = index2domain(zs0);
        var b2 = multiproof.verify(
            [commitg, open], commits, zs, ys);
        if(!(b2)){
            console.log("verify fail, multiproof verify");
            return(false);
        };
        return([true, leaves(rest), tree]);

    };
    function leaves(r){
        if(!(r instanceof Array)){
            console.log("leaves error");
            return("error");
        };
        if((r.length === 0)){
            return([]);
        };
        if(r.length === 2){
            if(r[1] === 0){
                return([r]);
            };
            if(typeof(r[1]) === 'string'){
                return([]);
            };
            if((r[1] instanceof Array) &&
               (r[1].length === 2) &&
               (typeof(r[1][0]) === 'number') &&
               (typeof(r[1][1]) === 'string')){
                return([r[1]]);
            };
        };
        return([leaves(r[0]).concat(
            leaves(r.slice(1)))]);
    };
    return({
        proof: proof
    });
})();
