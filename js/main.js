(function(){
    console.log(nobleEd25519.ExtendedPoint.ZERO);
    var Extended = nobleEd25519.ExtendedPoint;
    var Point = nobleEd25519.Point;

    var Base = Extended.fromAffine(Point.BASE);

    console.log(Base.add(Base));

    
    //ExtendedPoint {x: 0n, y: 1n, z: 1n, t: 0n}t: 0nx: 0ny: 1nz: 1n[[Prototype]]: Object
})();
