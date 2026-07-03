-module(store_land).
-export([test/1,
         leaf_hash/1,
         %verified/3,
	 serialize/1,
	 deserialize/1,
	 vec2bin/1,
	 put/2, get/2,
	 batch/3
        ]).
-include("constants.hrl").

-define(sanity, false).

-record(bstem, {line, value, x, y}).
-record(parcel, {price, binary}).

%binary positions are like: {row, col}. where col =< row.

% 1
% 2 3
% 4 5 6 7
% 8 9 10 11 12 13 14 15

%row N has 2^(N-1) elements.

% vec2bin(1) -> {0, 1}
zero() ->
    fr:encode(0).

bin2vec(Row, Col) ->
    RR = pow(2, Row),
    true = (Col =< RR),
    RR + Col.
vec2bin(X) ->
    true = (X < 256),
    true = (X > 0),
    Row = log2(X),
    Col = X - pow(2, Row),
    {Row, Col}.
log2(1) -> 0;
log2(2) -> 1;
log2(N) when N > 2-> 
    1 + log2(N div 2).
pow(_A, 0) -> 1;
pow(0, _A) -> 0;
pow(A, 1) -> A;
pow(1, _A) -> 1;
pow(A, N) when ((N rem 2) == 0) -> 
    pow(A*A, N div 2);
pow(A, N) -> 
    A*pow(A, N-1).

to_bits(0, 0) -> [];
to_bits(1, 1) -> [1];
to_bits(1, 0) -> [0];
to_bits(Many, N) -> 
    [N rem 2|
     to_bits(Many-1, N div 2)].
bin_tree_read(Row, Col, Tree) ->
    %row+1 tells how many bits to make the binary number.
    %col is the number we represent as a binary number.
    %turn the bits into car/cdr, to read into the binary tree.
    bin_tree_read2(lists:reverse(to_bits(Row, Col)),
		   Row,
    %bin_tree_read2(to_bits(Row, Col),
		   Tree).
bin_tree_read2([], 7, P) -> P;
bin_tree_read2([], _, P = #bstem{}) -> P;
bin_tree_read2([], _, P = #parcel{}) -> 0;
bin_tree_read2([0|T], Row, P = #parcel{}) -> 
    bin_tree_read2(T, Row, P);
bin_tree_read2([1|_T], _, #parcel{}) -> 0;
bin_tree_read2([0|T], Row, B = #bstem{}) -> 
    bin_tree_read2(T, Row, B#bstem.x);
bin_tree_read2([1|T], Row, B = #bstem{}) -> 
    bin_tree_read2(T, Row, B#bstem.y).

many(_, 0) -> [];
many(X, N) when (N > 0) -> 
    [X|many(X, N-1)].


batch(Loc, Data, ID) ->%loc is a pointer to a verkle stem.
    io:fwrite("batch\n"),
    MEP = parameters:multi_exp(),
    Stem = stem_verkle:get(Loc, ID),
    #stem{
           hashes = Hashes,
           pointers = Pointers,
           types = Types,
           root = Root
         } = Stem,
    R0 = list_to_tuple(many(0, 256)),
    {Hashes2, Pointers2, Types2, Rs} = 
	batch_loop(Hashes, Pointers, Types, R0, Data, 1, ID),
    %io:fwrite({Rs}),
    EllDiff = precomputed_multi_exponent:doit(tuple_to_list(Rs), MEP),
    NewRoot = ed:e_add(EllDiff, Root),
    [Affine] = ed:extended2affine_batch([NewRoot]),
    Stem2 = Stem#stem{hashes = Hashes2, pointers = Pointers2, 
		      types = Types2, root = NewRoot},
    Loc2 = stem_verkle:put(Stem2, ID, Affine),
    {Stem2, Loc2}.
    %todo. store the new version.
batch_loop(Hashes, Pointers, Types, Rs, _Tree, 256, _ID) ->
    {Hashes, Pointers, Types, Rs};
batch_loop(Hashes, Pointers, Types, Rs, Tree, I, ID) ->
    %type can be 0, 1, or 2. indicating empty, leaf, or stem.
    Hash = element(I, Hashes),
    P = element(I, Pointers),
    T = element(I, Types),
    {Row, Col} = vec2bin(I),
    X = bin_tree_read(Row, Col, Tree),
    io:fwrite("bin tree read " ++ integer_to_list(Row) ++ " " ++ integer_to_list(Col) ++ " " ++ integer_to_list(bin_tree_size(Tree)) ++ "\n"),
    %io:fwrite({Row, Col, X}),
    {Hash2, P2, T2, R} = batch_center(Hash, P, T, X, ID, Row),
    Hashes2 = setelement(I, Hashes, Hash2),
    Pointers2 = setelement(I, Pointers, P2),
    Types2 = setelement(I, Types, T2),
    Rs2 = setelement(I, Rs, R),
    batch_loop(Hashes2, Pointers2, Types2, Rs2, Tree, I+1, ID).

bin_tree_size(#parcel{}) -> 1;
bin_tree_size(#bstem{x = X, y = Y}) -> 
    1 + bin_tree_size(X) + bin_tree_size(Y).

line_hash(B = #bstem{line = {line, X, Y, Z}, value = P}) ->
    <<N:96>> = <<P:48, X:16, Y:16, Z:16>>,
    fr:encode(N).
decode_line(<<P:48, XS:1, X:15, YS:1, Y:15, ZS:1, Z:15>>) ->
    X1 = X * (1 - (XS*2)),
    Y1 = Y * (1 - (YS*2)),
    Z1 = Z * (1 - (ZS*2)),
    #bstem{line = {line, X1, Y1, Z1}, value = P}.
    
    
		 
		 


leaf_hash(0) -> zero();
leaf_hash(P = #parcel{}) -> 
    S = serialize(P),
    H = sha256:doit(S),
    <<N:256>> = H,
    fr:encode(N).
put(P = #parcel{}, ID) ->
    file_bytes:store(serialize(P), ID).
get(Pointer, ID) ->
    {ok, L} = file_bytes:read(Pointer, ID),
    deserialize(L).

serialize(#parcel{price = P, binary = B}) ->
    <<P:48, B/binary>>.
deserialize(<<P:48, B/binary>>) ->
    #parcel{price = P, binary = B}.




%the 9 principle cases we need to handle are starting in the 3 different states, and ending in the 3 different states. empty, stem, leaf. 0, 1, 2.
batch_center(<<0:256>>, _, 0, 0, _, _) ->
    %started empty, still empty.
    {zero(), 0, 0, zero()};
batch_center(<<0:256>>, _, 0, X = #parcel{}, ID, _) ->
    %started empty, now it has a leaf.
    io:fwrite("empty to leaf \n"),
    Hash2 = leaf_hash(X),
    R = Hash2,%fr:sub(Hash2, <<0:256>>),
    Pointer = store_land:put(X, ID),
    {Hash2, Pointer, 2, R};
batch_center(Hash, _P, _, 0, _ID, _) ->
    %started as a leaf or stem, and now it is empty.
    R = fr:sub(zero(), Hash),
    {zero(), 0, 0, R};
batch_center(Hash, P, _, X=#parcel{}, ID, _) ->
    %started as a leaf or stem, and it is now a leaf.
    io:fwrite("stem/leaf to leaf \n"),
    Hash2 = leaf_hash(X),
    if
	(Hash == Hash2) ->
	    {Hash, P, 2, zero()};
	true ->
	    R = fr:sub(Hash2, Hash),
	    P2 = store_land:put(X, ID),
	    {Hash2, P2, 2, R}
    end;
batch_center(Hash, P, 1, X=#bstem{}, ID, 7) ->
    %started as pointing to a verkle stem, and it is still a verkle stem
    {Stem, P2} = batch(P, X, ID),
    Hash2 = stem_verkle:hash(Stem),
    R = fr:sub(Hash2, Hash),
    {Hash2, P2, 1, R};
batch_center(<<0:256>>, _, 0, X=#bstem{}, ID, 7) ->
    %started as a empty, now it points to a verkle stem.
    {Stem, P2} = batch(1, X, ID),
    Hash2 = stem_verkle:hash(Stem),
    R = Hash2,
    {Hash2, P2, 1, R};
batch_center(Hash, _P, 2, X=#bstem{}, ID, 7) ->
    %started as a leaf, now it points to a verkle stem.
    {Stem, P2} = batch(1, X, ID),
    Hash2 = stem_verkle:hash(Stem),
    R = fr:sub(Hash2, Hash),
    {Hash2, P2, 1, R};
batch_center(Hash, P, _, X=#bstem{}, ID, _) ->
    %started as pointing to a binary stem or leaf or empty, and it is now a binary stem
    Hash2 = line_hash(X),
    R = fr:sub(Hash2, Hash),
    {Hash2, 0, 1, R}.

	





test(1) ->
    %testing mapping points in the binary land tree to locations in the vector commitment.
    {0, 0} = vec2bin(1),
    {1, 0} = vec2bin(2),
    {1, 1} = vec2bin(3),
    {2, 0} = vec2bin(4),
    {2, 1} = vec2bin(5),
    {2, 2} = vec2bin(6),
    {2, 3} = vec2bin(7),
    {3, 0} = vec2bin(8),
    
    1 = bin2vec(0,0),
    2 = bin2vec(1,0),
    3 = bin2vec(1,1),
    4 = bin2vec(2,0),
    5 = bin2vec(2,1),
    6 = bin2vec(2,2),
    7 = bin2vec(2,3),
    8 = bin2vec(3,0),

    test_vec2bin(1),
    success;
test(2) ->
    %the blockchain gives us the update data in a kind of binary tree, with branches that don't get changed left empty.
    T = {bstem, {line, 10, 10, 20}, 900, 
	 {parcel, 100, <<1>>},
	 {bstem, {line, 1, -5, 4}, 800,
	  {parcel, 100, <<2>>},
	  {bstem, {line, 1, 5, 4}, 700,
	   {parcel, 100, <<3>>},
	   {bstem, {line, 2, 5, 8}, 600,
	    {parcel, 100, <<4>>},
	    {bstem, {line, 2, 8, 8}, 500,
	     {parcel, 100, <<5>>},
	     {bstem, {line, 2, 18, 8}, 400,
	      {parcel, 100, <<6>>},
	      {bstem, {line, 2, 18, 18}, 300,
	       {parcel, 100, <<7>>},
	       {bstem, {line, 2, 18, 28}, 200,
		{parcel, 100, <<8>>},
		{parcel, 100, <<9>>}}}}}}}}},
    {Stem, P} = batch(1, T, tree01),
    Stem2 = stem_verkle:get(element(255, Stem#stem.pointers), tree01),
    io:fwrite("batch done\n"),
    ok = stem_verkle:check_root_integrity(Stem),
    {Stem, Stem2}.

    
		
    
%we need to convert this binary tree into a radix-128 tree so it can be stored in the verkle tree.


test_vec2bin(256) -> success;
test_vec2bin(N) -> 
    {Row, Col} = vec2bin(N),
    N = bin2vec(Row, Col),
    test_vec2bin(N+1).
