-module(get).
-export([get/3, same_end/3, test/0]).
-include("constants.hrl").

get(Path, Root, CFG) ->
    S = stem:get(Root, CFG),
    H = stem:hash(S),
    case get2(Path, S, [stem:root(S)], CFG) of
	{unknown, Proof} -> {H, unknown, Proof};
	{empty, Proof} -> {H, empty, Proof};
	{A, Proof} -> {H, A, Proof}
    end.       
get2([<<N:?nindex>> | Path], Stem, Proof, CFG) ->
    NextType = stem:type(N+1, Stem),
    PN = stem:pointer(N+1, Stem),
    if
	NextType == 0 -> %empty
	    %Next = stem:get(PN, CFG),
	    {empty, Proof};
	PN == 0 -> {unknown, Proof};
	NextType == 1 -> %another stem
	    Next = stem:get(PN, CFG),
	    get2(Path, Next, [stem:root(Next)|Proof], CFG);
	NextType == 2 -> %leaf
	    Leaf2 = leaf:get(PN, CFG),
	    LPath = leaf:path(Leaf2, CFG),
	    B = same_end(LPath, Path, CFG),
	    LV = leaf:key(Leaf2),
	    if
		B -> {Leaf2, Proof};
		LV == 0 -> 
		    {empty, Proof};
		true -> 
		    {empty, [leaf:serialize(Leaf2, CFG)|Proof]}
	    end
    end.
same_end(LPath, Path, _CFG) ->
    S = length(Path)*4,
    LS = (length(LPath)*4) - S,
    Path2 = tl_times(LS div 4, LPath),
    Path2 == Path.
tl_times(N, L) when N < 1 -> L;
tl_times(N, L) ->
    tl_times(N-1, tl(L)).

test() ->
    CFG = trie:cfg(trie01),
    A = [1,2,3,4,5],
    B = [3,4,5] ++ A,
    true = same_end(B, A, CFG),
    success.
