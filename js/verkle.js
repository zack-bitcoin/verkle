var verkle = (function(){
    var Extended = nobleEd25519.ExtendedPoint;
    //from get2.erl
    function compressed_points_list(x){
        var is_array = (x instanceof Array);
        if(is_array){
            if((x.length === 2)&&
               (typeof(x[0]) === 'number')&&
               (typeof(x[1]) === 'string')){
                //console.log(x);
                //a leaf
                return([x[1]]);
            };
            if((x.length === 2) &&
               (typeof(x[0]) === 'number')){
                return([]);
            };
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
                return([x]);
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
            r.push(BigInt(zs[i]) + 1n);
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
    //verify2
    function fill_points(pts, tree, result){
        if(tree.length === 0){
            //console.log("finished filling points");
            return([result.reverse(), pts]);
        };
        if((tree[0] instanceof Array)&&
           (tree[0].length === 2)&&
           (tree[0][1] instanceof Array)&&
           (tree[0][1].length === 2)&&
           (typeof(tree[0][0]) === 'number')
          ){
            return(fill_points(
                pts, tree.slice(1),
                [tree[0]].concat(result)));
        }
        if(pts.length === 0){
            console.log("ran out of points");
            1+1n;
        };
           
        if((tree[0] instanceof Array)&&
           (tree[0].length === 2)&&
           (typeof(tree[0][0]) === 'number')&&
           (typeof(tree[0][1]) === 'string')
          ){
            return(fill_points(
                pts.slice(1), tree.slice(1),
                [[tree[0][0], pts[0]]]
                    .concat(result)));
        };
        if(tree[0] instanceof Array){
            var [t2, ps2] = fill_points(
                pts, tree[0], []);
            return(fill_points(ps2, tree.slice(1),
                               t2.concat(result)));
        };
        if(typeof(tree[0]) === 'string'){
            var s = atob(tree[0]);
            var a = string_to_array(s);
            return(fill_points(
                pts.slice(1),
                tree.slice(1),
                [pts[0]].concat(result)));
        };
        return(fill_points(pts, tree.slice(1),
                           [tree[0]].concat(result)));
    };
    function leaf_hash(key, val){
        var key2 = string_to_array(atob(key));
        var val2 = string_to_array(atob(val));
        var leaf = key2.concat(val2);
        var h = hash(leaf);
        var n = array_to_int(h);
        var result = (n % fr.order());
        return(result);
    };
    function unfold(root, rest, r){
        //empty case
        if(!(rest)){
            console.log("error, rest does not exist.");
            1+1n;
            return(0);
        }
        if((rest instanceof Array) &&
           (rest.length === 2) &&
           (rest[1] === 0n)){
            console.log("empty case");
            var result = [[root, rest[0], 0n]]
                .concat(r);
            return(result.reverse());
        };
        //leaf case
        if((rest instanceof Array) &&
           (rest.length === 2) &&
           (typeof(rest[0]) === 'number') &&
           (rest[1] instanceof Array) &&
           (rest[1].length === 2)){
            var key = rest[1][0];
            var val = rest[1][1];
            var lh = leaf_hash(key, val);
            var result = [[root, rest[0], lh]]
                .concat(r);
            return(result.reverse());
        };
        //stem case
        if((rest instanceof Array) &&
           (rest[0] instanceof Array) &&
           (rest[0].length === 2) &&
           (rest[0][1] instanceof Extended)
          ){
            var p = rest[0][1];
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
            var j = rest.slice(1);
            var first = unfold(root, h, r);
            var second = unfold(root, j, []);
            return(first.concat(second));
        };
        console.log("unfold failure. unhandled case");
        return("error");
    };
    function decompress_proof(open0, tree0, commitg0){
        var cpl = compressed_points_list(tree0);
        if(cpl.length === 0){
            console.log("error, nothing to prove");
            return("error");
        };
        var list = [commitg0].concat(cpl);
        var list2 = points.affine2extended(
            points.compressed2affine_batch(list));
        var commitg = list2[0];
        var decompressed = list2.slice(1);
        var tree = fill_points(decompressed, tree0, [])[0];
        var root1 = decompressed[0];
        return([tree, open0, root1, commitg]);
    };
    function verify(root, proof){
        var [tree0, commitg0, open0] = proof;
        var [tree, open0, root1, commitg] =
            decompress_proof(open0, tree0, commitg0);
        //tree should be [rootpoint, {0, pt},[{186, pt},{115, l}], [{187, pt}, {115, l}],[{188, pt}, {115, l}]]
        var root = tree[0];
        var rest = tree.slice(1);

        var domain = precomputes.domain();
        if(!(points.eq(root1, root))){
            console.log("verify fail unequal roots");
            return(false);
        };
            //rest should be [{0, pt},[{186, pt},{115, l}], [{187, pt}, {115, l}],[{188, pt}, {115, l}]]
        //return(0);
        var tree2 = unfold(root, rest, []);
        var [commits, zs0, ys] = split3parts(tree2);
        var zs1 = index2domain(zs0);
        var b2 = multiproof.verify(
            [commitg, open0], commits, zs1, ys);
        if(!(b2)){
            console.log("verify fail, multiproof verify");
            return(false);
        };
        return([true, leaves(rest), tree]);

    };
    function leaves(r){
        if(!(r instanceof Array)){
            console.log("leaves error");
            console.log(r);
            1+1n;
            return("error");
        };
        //all done
        if((r.length === 0)){
            return([]);
        };
        //empty leaf
        if((r.length === 2) &&
           (r[1] === 0)
        ){
            return([r]);
        };
        //ignore a stem
        if((r.length === 2) &&
           (r[1] instanceof Extended)
           //(typeof(r[1]) === 'string')
          ){
            return([]);
        };
        //normal leaf
        if((r.length === 2) &&
           (typeof(r[0]) === 'number') &&
           (r[1] instanceof Array) &&
           (r[1].length === 2) &&
           (typeof(r[1][0]) === 'string') &&
           (typeof(r[1][1]) === 'string')){
            return([r]);
        };
        return([leaves(r[0]).concat(
            leaves(r.slice(1)))]);
    };
    function test(){
        var root = "kw9EIb+hCX0VL5MAcv4tdLq7UyPEF/wHBV2Nj6FCSGptCA6y0RKWgk7crzvXtKDW9FLFEA6emxCChsCcSShbVSYAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAZ3mYcSRygmoZh/CTWUvnknDXH9wrz7Cp4K3AuoCP/jk=";
        var proof = [["6khCoY+NXQUH/BfEI1O7unQt/nIAky8VfQmhvyFED5M=",
  [0,
   "bmkaBeVcbgVo0pEwQphowH7zVBP2ZbNDrJQVUElr1AM="],
  [[186,
    "yq6FSYjTIHWv6lB4wo73mZQHpzXhtpxKoBusn0PnPvY="],
   [115,
    ["AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADtzugA=",
     "AAE="]]],
  [[187,
    "OMeg/wTnTkwDgA2Ul0GYYmMndn4ImqAc8cLE1qr2HtM="],
   [115,
    ["AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADtzuwA=",
     "AAI="]]],
  [[188,
    "3tjsZzfLExuaGc4atk8XA0Ff2rVv5syWOcMnYU5rPR0="],
   [115,
    ["AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAADtzvAA=",
     "AAM="]]]],
 "HyEcbL5HYPlPIFZn60FMst7JpcRnmLYPfQlFLGwIX50=",
 ["VKCjUVkN2uQeE9SNsI0Bo+/FoYIMpwnAiio4RKTAJgU=",
  "HJBJAkPRpYGIhAaTKxhF7z4zQ06pyWK5AQDgqXptSAM=",
  "DGagIKUinSwQOBhOVjGMGLoZoe6DtXGhlZ5Dm6KxxwY=",
  "O5oDCZT61wVYm0SRzALgHYwss5uciy7cLs6ZGKIpqA4=",
  "HYNokg6iVqH/6vVCHQJPD+UIv7+RPO+aCdK7jF/1dA8=",
  "SGQTE520td6FnU7BhaYXz3G9lK7AdSyAxXAtvWQ7PgM=",
  "x3uGL6JC454ojEGqkH+O3VlMsaoicHbePnQuV7zDxAI=",
  "VFYqShhrZwA1F+OJNTuPlAzOW4i0lMuckZTi7m/5YAE=",
  "1zJIB2B2LI5z9OZn+s0ztiOvCYQ+Ld8ibsxf40BYIQs=",
  "x4tYZWLWxyQmC4MoMwhfZ4q37eEtlhpAW9m/m8k+Sw8=",
  "x9H6KfuLz4tryl5hnGp3pdVajgCIEg53g7WH1VimPwg=",
  "kf9DaGUOdE3uM3E4pVLD1enkXxnAHhYfAhc0gw/Nyg8=",
  "oykHZ/Fhwcjs0qWrLmAl5hbfJX7L2eaLqELy/Q07mg0=",
  "cBjPgjCw9C0D8dxtjgSo5Q1DptYualAVR3gHsQ8YHQE=",
  "l9JrSUCGH3NCm0grYhQn/OBtEH2sFH3cuw8a6Nn2zQk=",
  "eFdEbNpbrtxqOD349KZMsd/d7HDpyyJGdF3AiEqLFQo=",
  "Le3q+1wQfTNzAAflvMhkDvAB8IiPsGLzp2pi8fJ8ywE=",
  "EVgCiSJqKZ4wTSBDpgMEo+Edbf3od/+A+TwlX65aaAQ=",
  "LeD6zI98Zk0hX3EiwIBjlpkQFbZKkv9ODvR6d5YGrgs=",
  "AoTrtSVvt+im3IEn7yRdPYd58UNCo/aYlJfdJlYUuwQ=",
  "VTyAj61tRpGUfwLk7OXZgiSQqWV2ZkunnZ0pn7MS/w8=",
  "DxCv1L8qfbaamkR7Sz3IduGKD7YexlaLFG4lzeLOIw4=",
  "XsliEI49I4EPidQ0ZbR080WvGdnJ8vIJLShpr0TwwwY=",
  "2CdXGkOyrYphYniQlT8pOH+d9d4tDbkxSIWdBPebJwc=",
  "wc89YSiW+n7sXmasfaMGvzmHnGaaWr4Z2QdMezeHaws=",
  "OX3SBaTIG10qypJ1jmHvkn7c9H866CRSNJv9XHZ69gs=",
  "mnITS5k3qSPs95Cy8JwTjflU10c+Ia4HGY3QbSS3dwI=",
  "Fg+b54Wzr72WbTxHXVHyq3DmDqa3wVU/UthQrCYf2wk=",
  "Fx0JGq1GKqYPehbW5sXSVIlpCVkiIrp5THr5zagS6gw=",
  "FEbVU/77aB0PRMap02WW3NyuUCwyzsXEJIAwEYgligU=",
  "eB7h1ZZ94PxhWPOO2O4FGdSvTHj9QjlzHZFQNwi7bww=",
  "fn8tYsxBVtnKJ5E9D72pIhr32wru7+IKJzfPVjPOLgo=",
  "pCz8ZmOQ15BrORKnUNUmcGEp5rt9oibpJ6Cy5Oe8tQU=",
  "YfPg4OqIn777RPqAVeJ6al20Fod3c3O3muHkeUwN7As=",
  "6/MzqRHnLyx/ujoI0J2VvhD3YLAg0BAPWyhLKPGgCwg=",
  "554ehca5ZJDmABC7Y+cwS7Gxq3GYnV1cWmE38KBo6wI=",
  "V8N0O4EjFwjN/cscwL+1u9AyjePuhn/HSKSG3MUQ5A0=",
  "KWagqtG3vVUrJIcLaXqJlyBwryY0r4q75eSuWQHKxAk=",
  "HfaaclqwA+qAMCelB4epJsfnSZ68Mtd6M8SxYwwu9wE=",
  "emw6x9PHzk+bIYABgHTop9cchhFlV3leclNZkh9YjQY=",
  "tmMqzGl7G57GK1ocBKIZ70QY2S1AiUU3ZtQz+urF5g4=",
  "lTq/xulnFCF2efWY+kmEUI9yeZ4dpQXthvrQ4RPWdgQ=",
  "vzJPIdP0DgMvmBYBJbjDgSLGwIS+q9Hzx83sJm//0Q0=",
  "ye6bteJDSi2t1FJBxGF6+KxXT/AYKmU89VhXcBBaTQw=",
  "NZEJ0/nW9tLRL72Q2ZmvwSnrGAPqwh46sZurU72riwk=",
  "2TtHgv5Rdw/SgVOGdfQ2wThmytpfQSFDDCrmQnxuTQU=",
  "9IoY/tYb+OZlxTVXzoXQWaMCIg3/yFk/KEModgR2xQE=",
  "iUnOfuOUhCCxOCFzE5O1MDBPBspfOoNnV5MzKKhmvAA=",
  "A3oXPrHP7P+egJTw/yHhatafaemB1yOfeR5BfeJRxQY=",
  "mVZ77MBUUBcCTqY/jjnbIVaqM0tWSWzXXPuNxkyiyws=",
  "XXhIYlCC5jEObs7oPwRZHNad2qFOZbkrGXgODnmczAc=",
  "Wpjy1O5Cu53s/BhO9Wy9TO5EzKgmNSnYU2M+bPIXegU=",
  "Lzxa51t5+icQeuZLt7UjSUhMjD8bbDBKC1717+W5+g0=",
  "WlEkMlV9blxVQuxQz9O2kO7X9e9b76pWR0uNFQ39vQA=",
  "yw93Bz/ow34F/Pd4J1UuNGRm+1xLQOeDV3RcBJ4QjQc=",
  "/eYq17MHXj5N5JsWL4Ui3NQGVRZqtH14dgnIYX8K2AM=",
  "nDXT3rqbyJVOXIMmYi34urxs3T2Mkdwf4lwgITIkMAA=",
  "KVaPd1yO686/putnUizxLwIrucudryOBC63MEwUmNws=",
  "d+XyWN1XMlGDTkpAnqKZit5obD60+gZwtWen74md6Qk=",
  "jXGbgtzWMz67V9pC5d/FRn9sBPRMBXcaThwVQZPqBgo=",
  "ivKGf5j4LqFaUYNF+LgKl7bD8gmrjyZLsJ9ACpE/VQQ=",
  "XpLInJwCfPnXy2V0+gv+AThrzanii7zImH2pCuaOMwU=",
  "G31ZFDgdWBahSq9W7izSbKmdO7etdmnnGwSMUcNxqwU=",
  "fcdBxEMCbY9/CzqLSJrowRHtWIhHqmvdggDU5LMzUgk=",
  "LWzK8biFY063gfPlr9XIgJwyeSrmr7fnj8HdN+T61Qc=",
  "rAlR4o2hiaoID4Jpolux8Ark+3AsLeqTJqQ3sO+vKgs=",
  "/Br71+kuNSv9h9JpFe7rFzhV2B1UrGIL2MuI68AJMQQ=",
  "E/T42L1UepQKexUKenaqKkFuW8NXorwplozYGBOvwQ8=",
  "iEiVBLTNAGKopGo4zOo4+f1Byq+JXH7TQRAinZPLZQY=",
  "vk9o7hPxlDmYNM2r+aX9Ic+qTscuNTLjqvENQUJaSwg=",
  "sTByPyuRD+iIZVZJ3LZhOQKk42EDYfvhFVG56wV/ywc=",
  "t99VKyToN3l73i/TtF4pSGD1ddutLzitXgMHou4lowI=",
  "asdR3QUlqnL9DWU+cJU8y5cyutn8JQ7Xkm4i3Rx8zgY=",
  "8lE1qU70ndjisFYzqImLba3Sl1Hip9YQslL6VHapygA=",
  "uH6lPgV4pRMPHLTkDb5a0fbjhJ9T5ADQf1eCPLPYHAw=",
  "pF6/0QYZ9vKaFvfR1q6aJFIDAaCRVE/jBuhwjTWpRAA=",
  "Vf03dCqt5w88+NXx2HY0vvljmuEGqRUYu4P/DJ07WgE=",
  "66qrZcdEy/10JOp+l/mb+XovixgDyD0rgBw/i/prjAA=",
  "e2oJSBBMOy859QNtPKa1Rvm9BNXgU1YCR5/660/1Rg8=",
  "qgFzF8UerFBTq/4l2Me6t94LU/RgPnUHNsOk6t4WjgQ=",
  "uvf+V9T3SogHRCGAoSxsT/pszlZiQ6kS+WzQ1sYsNwo=",
  "NeI+ayhdsNpRsk9NzKXUt2BmQ2OKQC6lSvKzUm+3ggQ=",
  "RLcaJGfRLBKwf2VbChgakRIr/0RhN7UIIJ9agtM4wAk=",
  "LmK8KHLWr/U+k6UePKuh1sEsR5q0N05jwQGFj6l9UwA=",
  "4rZKimpi64pLhyfZO6pMVBomfvdgt4b5iNfQyQtJ/AI=",
  "oHg9Jz7yYJ3987SJ8gdxcBUwAWZ0F4jay4e6y+I1Lwo=",
  "R2SKnVAy/5T1CRQ+Ctr4CNe7Mcp2ho/KUpkySiTGRwc=",
  "E9w6l3dk2C5HaHYAcBN30HVU8S9nLjp0it+sB3ETSwI=",
  "8cbxziEeWeOK3wVr8NYZbyJMsAz+v6d5fqFbj/DvuAc=",
  "D68ds+QKLY0GK3wG2a42kHHi+shiAoe1RsumxIjOkw4=",
  "G1ZWeXz+ZxZsykogP5thFkHTk+ouB+phCTDLXmbMQgg=",
  "GXFSIsPcJ8DaAAZiA0HUS0klERTlD4pPfqyCY5raHQI=",
  "sDJ8UMHDrQRZA3BZvvfMqPuLqIqE5mlnWJooZ4+FKQU=",
  "o2TpgAX7xROwW2+fr5cgz4HoBgVt4dwHbZEJ60tNBg8=",
  "uagqFSpfmxNApAQ57DLLXoZgQdH1ui64wgYKp2xhOgI=",
  "ehgFJVPiQu52FyusGfpm6CAVhEWya7ZCz9LRZeRVfgM=",
  "xYUnM8aqyZDDszGSh8Yy36sU9cGn8okoDXYk8iq/jAo=",
  "JFOhIPFCPXr0PHAWiUB1wFxqc3f361aQEJO+EoLxBAM=",
  "+RV4qoaIte2QL2oqCeuld5mu/761aDdhoZsGRHuqJQ0=",
  "6cqrReiyf7YiNlkZ6jQZzI7DhIXIlIFzK6EUzujLzgM=",
  "viZnwluqADBAa42cXnKFEtQzmhZFdDojRB+lxNvCZgw=",
  "dk5EagDbbb/E7D21oIn98VbdHfq75jsHrBtO5UVPkQw=",
  "Onn7K/UyNFhIA9BKAAjk8EDoMAZ+E6wT+78yUCBtjQc=",
  "KIqi8vERKtLWdKLr2hJSGMl2gxXRT5RCKXwjRvswfwY=",
  "qm91WtWeeAA6hED3oRmKK+HePu85J0v2bxdGMgDBKws=",
  "5WmwIVuSYRJg/8rpEDbnsnxGsYv6lzXX8gwIQWJEpg4=",
  "zIXlVBk1r6pW7Vz5taRp8xAevXJDu9XKpj2rOscqGAA=",
  "kQmD/EIKHV+L0Ctxi9foV89J84Wd216PmTHgFXJNvQY=",
  "uycl3c8QRIuPYXOnwUMBx/EMg2bnQdvMt2q9CrWOawk=",
  "XeYwgzn8Fy+AnIWVZmAjY54BML/aYnQlqVmIjzXLAAQ=",
  "J26MY4fxldj094xLblMZjEDedIgc5tpFn4Nc4cfZbQ0=",
  "fguDfYT9sYznawwbDTbSfz//Bw+MoNvZolfEcCh7/gQ=",
  "WNMZ0NoFwMRMQrB9OvRQkYoqtfJKLOg0XTPrq6JIUQE=",
  "ekIKL7tZdz3b6N2nIpVIGtvZFFET+AVnMUvDjyztPAc=",
  "Kcw4TdrSYQtfjl+G33hdfEd9uKV6a+/gYXZW9uyFPgo=",
  "DbKlMH+hCMf0ry13itjjx1Kn5rkFwtJGja6yyYrArgQ=",
  "t8T9AQh8LtoCyM+YV/GDkpwbOSJdWCBu7ebJciaFZAI=",
  "+9//PvuxTjMI7+r6/XT7sOP7atEUO50Cu7wAUPvzUQs=",
  "rREmC82n/8DvoACR9rjyn4SfqQmnZxrqlZP13CMbnww=",
  "uXtNQKSGl8BkuAAglzU5OCRTdFoHnem8rFhuRGcN+ww=",
  "6Gske/ZyA5L7Ogfi6d9bWrPqbIg3ungZle3U8hxY3As=",
  "O9cIHi2MwoxkxroNJlZpPk0lx3/i5ttTOvNnS5x0vgQ=",
  "kUgGwWHu0P6JDG+Fb5yIGrIX0KEw/ad25wUZcAzqbgU=",
  "1bLK4RDH5wOl5rLwexuXLT+06cvu89X76Ph08KylCQ4=",
  "VjAV0fMzbsdUWDmLqbkn45+DWMg4D9aTHKmQ0yMzswE=",
  "nUq+D6UYL3ZMlFwMQh7RyJWL1GmfcvABonoK7LQotAY=",
  "NklGJjYyaliKetaHWmj79dFiZphB0eZx96BgIBacJQ0=",
  "WfJa5dqfcykxeg916DKGhaMoT35IKdMxxBpCdUg5Iwc=",
  "Wkinvx56IOjSU4Xi7FpA/dwnDHH3dmCjOYX9B2Ix1w0=",
  "K/AJ1lJKWyHMUlTH/PE79235FhpVJTQcvq0/CZjC3w4=",
  "+iWw0Zpjppc0No8zRjV+sSkKN5sI1ByXMbilHyAJoQc=",
  "JiSWJf8iDUJzjCGZQCq4Fqwk9LPghCdcXmtAyfe5fgY=",
  "FKSYZwFriGo3jgd4cgfC8x/RL4EnMdl21/hJXNZ9FAs=",
  "y6V1CRfM6oTjHgBain3xyE6tzSDUPWN5bSfnfHfAlwI=",
  "SW98wVmGNPMB0a0+CkGBmMK6EExFa+uDy00CRkmQeww=",
  "1heWxHcIB4J37dvfEkTUqmUye729Vz4Nz8y8tDndew8=",
  "3MZ1NPyPT6drZqBXrw7yjZzvBzotc8eaplAIFXgjgwQ=",
  "qu1q8BlCLKN0F9F3GqZebVA/AkZXpBljx5AaBacewAg=",
  "2x2hDA/gVPzbameKYomzU3uutU/F+Cmm7l7nR19hTw8=",
  "FgGH1PH2Wt3RM2+Jben+YpHw4UUAauSV6qaAX+IiRg8=",
  "aco1IdHCGQihf2Cu4gpsaXFtDdgT/fvUzOi1gYKSwQ0=",
  "FLg+jy2xdaYnd7MKO9KE4qd7qVR2x5I7VhXFdBPCTws=",
  "l9MkdqJLeI4/DKBl2sZxeo6m+ec3pClcTtwLc5fMHA4=",
  "puVredpm6Jv+3LzgxsC2gcTWu5RaT//+T8KxEzMZtA4=",
  "0sdn9DgVe3biOXW2RSGaNSa3NdCBsSHTyTtKqEjdagA=",
  "zeQ0oI0tfD1eUREgQi4D2LJXTWnyUpYtFA0irQco7g8=",
  "5b3zFqx7RiBoDtbX+nq5vdNPuy/Gg/7NJ9HyHxJK0wQ=",
  "3eqM5VPBMldbkK7uMvg0qGQELKg86oABDxYRj0WaNgk=",
  "X/gwCQXd0wW2z13xbBKh9ycWOlxEh5Jz327ZY8XpcAA=",
  "bmyJe9TtvxcKKmVXXDv9f/4Ne0K/zC4Ox5FmRhHRhgI=",
  "tqsF3RVsUdVnK9LoqQ54xZ1C+QXTCcIl5v8OVxcl8wI=",
  "O6pbe1zexKdvUg4TbxV+ZZ3ygkgoe7JtzsVDBByc6g8=",
  "7IeL485JDr5hzlGuJCToxJB+U2E8DO19yx5+HSTzQQE=",
  "8N6dzVUV3/k5P1WNTBae6aDuLN1YQ9ab+1+LI7WDwQU=",
  "3+gpkS/qD9knIgybdnLFDKJ2TTIf/WbQ+5KUl5OfMg8=",
  "57Uo8itxXVRnycVKZe+zkrOE3EYXAYuXq0W6R+1sNAM=",
  "v8ZNXLIl4ec1IYPmPqimTFQr3e8rGZSO9ppqQAxP+Ac=",
  "0FGdhHJA1dO63HNyNrLUUl/6vrGNGMQ7ZzkRBU+Nags=",
  "H0Fdh3cAqYV65QIr+bctlRYoTPDlpv3zmxII9GMg0gA=",
  "LvAxH+hJNSBuThqFf3xFMWfNLMWzNzYKY08q+hH/Nw0=",
  "R92gg5li0Ld9xUov+tGyQLFS+nPMOghLnwx1920yFQE=",
  "ESl0KKXC5Zf+6cx4iwtghnzENf+8OzVGlHFkmujs2gI=",
  "gPN+dlBpxUfmRGfv7gebRniprN+J+NWlj7RfRwVWLQI=",
  "8BPKdgRHXI+KxBBbCxscu1W4GyC1Q5F4iyK6sBeRDQQ=",
  "YA3Zw8swv/xG9swBleCsgRXkHA2Rkb7C9xKd3i3gTgw=",
  "e94U+Z0QNYsFlnc0UwYdVE8jBsuJzxO1GumbhCaPQAk=",
  "NZ1G6IAfyG4ACmMf/1QIoOlkUQOkEBeqsEPf7fzvcQU=",
  "Hd4DcjMaY7GfG+cEHQRCkmxYQCo0sK2tBGclUriJwQM=",
  "Ifg1y+3ffcpa+ut7bzHtkwYB57VvkdEXNG7tPD9aew8=",
  "ExqXdht4vUZwvK3bnIeCI862dLVd2bX0bPCFtuxxUwM=",
  "KYfKV6hnfl40hGM7j0+ih/fpdMX7+4gpQ5TiZc5eTgA=",
  "hrytskjjhrMtMI5+tF0rBmNuowFNWxJ2euNbfJN9+A4=",
  "vTDBQ9i8j5FEs2ZpWCtucA6h5+ksYdAK1t5j6CK5VA8=",
  "cphtQUuC7OfjpINcF/9+W1wSBXSJX7tQ/Pxfix3vuAI=",
  "uVY0Oh+IUqAPIWHlQs4mXjD6L22V7QBAJvBP7A+Fmgg=",
  "O4OiphIfGtpbDAt8YIXmwkHHrXE6xHANsFBP8m6dvQY=",
  "ftqVr+eo6EtCqMqiB6p0NOd7dSfiNUtPNKHV6mQlWwo=",
  "I82ryyYs49N/TuK93oGJQ+BI98qHvCHOaGtYTRQnmw4=",
  "L/xv5mfI6YgyHCLNqerb/qcFn2ROIyrkmgW+2AMq5w4=",
  "ASlr5Kt8nxxgA5BC+a10u2/laUanBwu7IYkyGZXkrwY=",
  "RmZTvZYxM8K12onzuf4qleDAwF+/1sQfqEPpoSaIVAw=",
  "RuOONM39VXPpBSKemnflxvIkAFdekx/O2e0i0v48gwc=",
  "4UUC/6qzeriLnDEDCl2aYH8gcH4H/w9vfeZ92GNASQs=",
  "x2g2i5LYts4F5Luh1WrP9Is4Z/C8HShwt0UweIBhngI=",
  "m5w3K+3FThDbb7+ultA/yW3cOwS8ROWFET9UrEqNngM=",
  "Tu3bxROIakyA+uaCXEvN7zxlUhtK7OwViI55yD9sewQ=",
  "9WbXFqH+h2db4UpfWpkZCfvPuftPZktb6OS+2eEmfAo=",
  "RXD3hFfo5GMdmqQvGngszR+UYAsMFeQukFVs2jFqvww=",
  "yfGnQyxUu4pAZ2FQ7RBjt1nOoy4KsDaLl+/fk0JCZAs=",
  "UUFo1VOk7DN1urV+AYk+ZE5tWS4mc6ROqwMNVqhYAQ8=",
  "kfvDkT4r2RmWJwJeJVKAW9N3JxT/T/RaKgakph8vCAc=",
  "D+WNxcYqH2GfSalBjk62r5Mm7CvKQRgXr74IRqzYeQc=",
  "bH1dfvqo+8HhYsBPmm+na1s3MDVGLTTHfrocYunwFgg=",
  "k0FEcwMgW8hAp4yno7BaJQkReXiorfAJBsNgAePmPAg=",
  "oinl7CWq03moxbFkZ+N8VU5aTuiq94CrVCR35mZKzwE=",
  "C/AxNv3vs8ppWAKgshYnwaQQEiLQbfur+8CmoMdlnwU=",
  "wsImzb3ViVlpvKuxTalPgAZe4aUJgnFBXjSESTWcCwY=",
  "UP+mKHi3pe8acaqCiaT1cs3IMDJrfzg2eLSDfs5xjgs=",
  "tWLlj3ap8/ateDqQrVqPx7kT7Gu2EGDyMKOB+Fw3HAw=",
  "cKO/Ei2AVWSU+cubtV6k/oNXVfCGc1MvNYP7Uc1m7QY=",
  "pW3i766CMw7me7BmS0h0ckwPfOI3N41NQGhrRzeFOg0=",
  "PiaC8EhoBifdAYc+lb9W/TDochsYj+SRXVvFY+I/EAw=",
  "ZWD5Y35elSDPSGGS+ckCOU1Kns5J1yHr/t9uwjqzawE=",
  "49DMME6I8TNvMxg5I5QmOgfo8tDfqTrO3GMg4W4+0Q8=",
  "05naz5u/jeQzk2/x6PRHqtUPAn7UOnAhrvaObSM3PQQ=",
  "C1rLf8E2e8xLdvVGlbtSbZDm5p2aAz7fR5qobP5hjAg=",
  "kGtv0+O/ylGHhxkTX4isOYlmgLHME/AIPSZo4DMlQw0=",
  "uxAV0VdTMUfEH0O+k7pC4HUU9ywKa+hh/89JvBAgUwc=",
  "mkeCsZvRmR0mz8gcUnw0swToD+UW3wslqeonaYobaQM=",
  "mI7OCX9OILGRq32Fz9IYyGV4Dhp6Dp3kqiqhV6g53gM=",
  "OsAeIz9DLcLKZ1uO7Y75cRfGS2o5hlM6dAKYNHG/JAM=",
  "qb5sayw4OwGi7VDJNOmbNkvHFtiwh37zucisjz/b1Ak=",
  "rVURAWuRBlnGhxkKBPkFl6Deo5d4dYbWlyERJ+CtVA4=",
  "TUio9A2fsLEyHm5+EbVcMZFrYtNUCrEgZqtmsE4dXgk=",
  "AmFEp+2DNOLMU2gHt66H3GGFJ7aMSt1r4u9cvuWdFwo=",
  "hGWIGlSPt/j+D8ej1dJHlv7XzgayUO3MVCK7n6GLlg0=",
  "M//+ycWLnfU+1PL8A+jkF/N+tMW2dz6GYoh+K2sIAA8=",
  "fItwfw6siH67Py6igLYBP5TOVNdAv78eDQ1fsSHd7gA=",
  "nP9gLLINrKlb7DWyuT0FkvQPbmcEEg3ItOPZjlh8rA0=",
  "CaTWd2KAeMzkwSfViSxMHeK5pVh1aiItNQSiMAzLhAg=",
  "2A3ds3yHhdexp1vpGsxITKYwq8LHPrbpeLsKeKSexg4=",
  "mm30Yxu1wQgejHACPALxpdSb5ulGT6s9The/W7JPAgE=",
  "CxSk+gbm9bHd2jKV4dfIfBs6KzCEfjShj7v+C1LOYgU=",
  "sI7Vd6pAe2kViztAy0Q+6MjE+I0uwVkkPUtdiCBzHAs=",
  "XfyCGZfBauTqb/VAjmoIGKLl/EnMKD8XCHT0wYQrag4=",
  "J1xOA7MimOnBDOi5nvCKlgZKtwPR/kwk4oW2gQVWUQQ=",
  "N68bny6O2+Fp0XmwwBQw9s1M4NptJkWvKUArP6WSpwI=",
  "icpzx5u377vBoD+GdryWu9DZnzEeiErm7aVVeQCvogk=",
  "pkBkbY5DDuBS24WwfIclMdVma/jUJPaoAYFof0SJqgc=",
  "Ylf4iPybHZZnNF5RuM8UZFAFNCppE4tm0Z7RjsU+NQE=",
  "sHmV6DCbuJc4g8MaSfx5dqfZY/AxzDACBblkL3/vCQU=",
  "81SkqSv+vaEJHbp1O9Ku8r7xjWgDX6J+pcffCsPOsww=",
  "WobsrIWW4dHWvP5BcWuI7ATGCj8FHfsBGkhF6lqMDAE=",
  "IQpSZBUdNTr18gclJTgexEXWH/1uuWuksk+f7aaX0Qw=",
  "Sc/sgoKWtN/9HMyOYNkByLcw76VoT+zgLfsQ5CI3DA4=",
  "X/Vx4oKVme4L1NtdyQmpONXlP/K/6vad3hBpCW66EAc=",
  "ikQLev4w7UJK9KnhANsw+yhbZGM1LN3hXfGZswbcGAU=",
  "72h4zFNRHD9vM4zLkJZoBsY1jueQ3JIUsr5sOJFu9gs=",
  "RmNL2ybdVFBE5EhuqR3zC9AKnU2dGx7ZE+2a6r3Z2gk=",
  "uU4UANUrsRHnVzn04/1bwRn/Fdjq2i/YPV36UqhdTwo=",
  "RcrKrG7BzhSAyDH5m0HDGwUU/Q6xe6N8cNEO7nawCQk=",
  "jLf5HViYZz0ZbAsepN1sNa2LQb20Ml4A+Sh65Z6AvQw=",
  "YX08rAwOnUpL3WgMw/YZjg4+tdRGKW1Shh1HYGQ43wY=",
  "pGk/aegL4Dbv9HkxqsWCf6Z6BR/CZGUQPZVt8XYxogk=",
  "efZQzkGJ7ryd4e2XzobwMAbsBfWTvBZ9nV6Mko0BBgg=",
  "bqjnTwZ21Z60PQ5z0RyZzDbdC/R6OiGWagkzkOrL8Q0=",
  "pksEyfDNQnVVMcg+legwSuYQgAO/Xc3s02JQ3PO64QM=",
  "Igepgr5TdUYzpK/i3U8Xl0Z9WtAUntmNAbJm5cBfzQg=",
  "cSQI+0BSlREdBBNWFlYe+VYMu8uAuTKxN/jUmPLMZwY=",
  "GupNYyFhPw7TQRdwI/frNHd8vpU2CYkQXPiHOTGjJgI=",
  "zhcuzS4DBV9tKM9IahWPs0fJEXxJjzjpB76/dK8hzQA=",
  "Ls8YnUXiYan1kc6j7grzgYToZ5n76DRZ4xyRNiC7BQg=",
  "JnbUpKwlVe3tNFS+7Es9QKxZ9Jtr+q7Sc790bz8+fwE=",
  "cvRY9sHWDQo7JIAa99jslquHGWd+NKS4Ih6osAPergM=",
  "A8or/AD3+82mIUTPjEyoDN36gU2WY1dZsPU1PlOiEQY=",
  "oc7KG5r9pAOSeAypV+sMv4mpY6eZb/FlwRqoIcw9+QA="]];
        var opening =
            multiproof.decode_helper(proof[2]);
        return(verify(root, [proof[0], proof[1], opening]));

    };
    return({
        verify: verify,
        test: test
    });
})();
