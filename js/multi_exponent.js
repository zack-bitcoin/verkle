var multi_exponent = (function(){

    function remove_zero_terms(rs, gs){
        var rs2 = [];
        var gs2 = [];
        for(var i = 0; i<rs.length; i++){
            if(!(rs[i] == 0n)){
                rs2.push(rs[i]);
                gs2.push(gs[i]);
            };
        };
        return([rs2, gs2]);
    };
    function simple_exponent(rs, gs){
        var p = points.extended_zero();
        for(var i = 0; i<rs.length; i++){
            p = points.add(
                p, points.mul(gs[i], rs[i]));
        };
        return(p);
    };

    function doit(rs0, gs0){
        //rs are 32 byte integers.
        //gs are extended points
        var [rs, gs] = remove_zero_terms(rs0, gs0);
        return(simple_exponent(
            rs, gs, points.extended_zero()));
    };

    return({
        doit: doit
    });
})();
