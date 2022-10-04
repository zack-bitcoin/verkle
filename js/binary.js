
function string_to_array(x) {
    var a = new Uint8Array(x.length);
    for (var i=0; i<x.length; i++) {
        a[i] = x.charCodeAt(i);
    }
    return Array.from(a);
}
function array_to_string(x) {
    var a = "";
    for (var i=0; i<x.length ; i++) {
        a += String.fromCharCode(x[i]);
    }
    return a;
}
function array_to_int(l) {
    var x = BigInt(0);
    for (var i = 0; i < l.length; i++) {
        x = (256n * x) + BigInt(l[i]);
    }
    return x;
}

function integer_to_array(i, size) {
    //this is not the inverse function of array_to_int.
    //because array to int is accepting big endian encoded binaries, but integer_to_array is returning little endian encoded binaries.
    var a = [];
    for ( var b = 0; b < size ; b++ ) {
        
        c = ((i % 256n) + 256n) % 256n;
        a.push(Number(c));
        i = i/256n;
    }
    return(a);//in little endian.
    //return a.reverse();
}
