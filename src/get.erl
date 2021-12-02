-module(get).
-export([
batch/3, index2domain/2, paths2tree/1,
%get/3, same_end/3, 
test/0]).
-include("constants.hrl").

keys2paths(Keys, CFG) ->
    Paths0 = lists:map(
              fun(K) -> leaf:path_maker(K, CFG) 
              end, Keys),
    lists:map(
      fun(Path) ->
              lists:map(
                fun(<<P:?nindex>>) ->
                        P end, Path)
      end, Paths0).
batch(Keys, Root, CFG) ->
    RootStem = stem:get(Root, CFG),
    Paths = keys2paths(Keys, CFG),
    %Paths example: [[1,4,3,2],[1,1,1,2],[1,1,1,1],[2,1,1,1]]
    Tree = paths2tree(Paths),
    %Tree example [[1,[[4,3,2], [1,1,[[1], [2]]]]], [2,1,1,1]],
    %list of lists means or. list of integers means and.
    Tree2 = points_values(Tree, RootStem, CFG),
    %Tree example [[{point, 1, Hashes},[[{point, 4, hashes}], [{point, 1, hashes},{point, 1, hashes},[[{point, 1, hashes}], [2]]]]], [{2, point}]],
    Lookups = flatten(Tree2, []),
    Leaves = get_leaves(Tree2, []),
    {Commits, Zs0, As0} = split3parts(Lookups, [], [], []),
    Zs = index2domain(Zs0, ?p#p.domain),
    As = binary2int(As0),
    %io:fwrite({hd(As), hd(Zs), hd(Commits)}),
    Proof = multiproof:prove(As, Zs, Commits, ?p),
    {Leaves, Proof}.
    %multiproof:prove(stem:hashes, slot in each commit to read from, commits, ?p)
                      
    %batch2(Paths, [P], CFG).
binary2int([]) -> [];
binary2int([Tup|R]) when is_tuple(Tup) -> 
    L1 = tuple_to_list(Tup),
    L = binary2int(L1),
    [L|binary2int(R)];
binary2int([<<H:256>>|T]) -> 
    [H|binary2int(T)].
    
    
flatten(X = {Point, Index, Hashes}, T) -> [X|T];
flatten([H|T], R) -> 
    R2 = flatten(H, []),
    flatten(T, R ++ R2);
flatten([_|T], R) -> flatten(T, R);
flatten(_, R) -> R.
get_leaves(L, R) when is_record(L, leaf) ->
    [L|R];
get_leaves([H|T], R) ->
    R2 = get_leaves(H, []),
    get_leaves(T, R ++ R2);
get_leaves([_|T], R) -> get_leaves(T, R);
get_leaves(_, R) -> R.
split3parts([], A, B, C) -> {A, B, C};
split3parts([{X, Y, Z}|T], A, B, C) -> 
    split3parts(T, [X|A], [Y|B], [Z|C]).

index2domain(Zs, Domain) ->
    D = setup_domain_dict(0, Domain, dict:new()),
    lists:map(fun(Z) -> dict:fetch(Z, D) end, Zs).
setup_domain_dict(_, [], D) -> D;
setup_domain_dict(I, [A|T], D) -> 
    D2 = dict:store(I, A, D),
    setup_domain_dict(I+1, T, D2).
    
paths2tree([Path]) -> Path;
paths2tree(Paths0) ->
    Paths = lists:sort(
              fun([A|_], [B|_]) -> A < B end, 
              Paths0),
    {Same, Others} = starts_same_split(Paths),
    H = hd(hd(Same)),
    Same2 = lists:map(fun(S) -> tl(S) end,
                      Same),
    Path1 = [H|paths2tree(Same2)],
    case Others of
        [] -> Path1;
        _ -> [Path1,paths2tree(Others)]
    end.
starts_same_split([[X|B]|T]) ->
    starts_same_split2(X, T, [[X|B]]).
starts_same_split2(X, [[X|B]|T], Sames) ->
    starts_same_split2(X, T, [[X|B]|Sames]);
starts_same_split2(_, Rest, Sames) ->
    {lists:reverse(Sames), Rest}.


points_values([Loc|R], Root, CFG) 
  when is_integer(Loc)->
    Type = stem:type(Loc+1, Root),
    P = stem:pointer(Loc+1, Root),
    EllipticPoint = stem:root(Root),
    Hashes = stem:hashes(Root),
    V = {EllipticPoint, Loc, Hashes},
    case Type of
        0 -> %empty
            [V];
        1 -> %stem
            [V|points_values(R, stem:get(P, CFG), 
                             CFG)];
        2 -> %leaf
            [V, leaf:get(P, CFG)]
    end;
points_values([H|T], Root, CFG) ->
    [points_values(H, Root, CFG)|
     points_values(T, Root, CFG)];
points_values([], _, _) -> [].

%LP = stem:pointer(Loc, Root),
%    L = leaf:get(LP, CFG),
%    {Loc, L}.

            
                              
    
    

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
