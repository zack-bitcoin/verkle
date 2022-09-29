
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


