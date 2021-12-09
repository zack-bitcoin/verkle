-module(get).
-export([
batch/3, index2domain/2, paths2tree/1,
%get/3, same_end/3, 
split3parts/4, 
keys2paths/2, points_values/3, 
withdraw_points/1, withdraw_points2/1,
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
      end, Paths0),
    Paths0.

batch_stream(Keys, Root, CFG) ->
    %This strategy uses a lot less memory, but we would need to read everything from the tree 3 times instead of just once. it is probably a lot better for the ram version, and might be worse for the hard drive version.
    E = ?p#p.e,
    Gs = ?p#p.g,
    RootStem = stem:get(Root, CFG),
    Paths = keys2paths(Keys, CFG),
    Tree = paths2tree(Paths),
    {R, Ys, Zs, Commits} = 
        batch_stream2(Tree, RootStem),
    DivEAll = parameters:div_e(),
    {G2} = batch_stream3(Tree, RootStem, DivEAll),

    CommitG_e = ipa:commit(G2, Gs, E),
    %T = calc_T(secp256k1:to_affine(CommitG_e), R),
    ok.
    
    
batch_stream2(Tree, RootStem) ->
    %Tree: [[1|[[4,3,2], [1,1|[[1], [2]]]]], [2,1,1,1]],
    %tree2: [stem, {I, stem}, [{I, leaf}], [{I, stem}, {I, leaf}], [{I, stem}, [{I, leaf}], [{I, leaf}]]]
    %tree3: [El, {I, El}, [{I, leaf}], [{I, El}, {I, El}], [{I, El}, [{I, El}], [{I, El}]]]

    %{hash, Z, commit} for every relationship in tree2. Hash is in integer form, committed data being proved at this index. Z is an element of the domain, the index being looked up. commit is the elliptic point of the child, in simplified format.
    %Y = hash

    %Affinecommit: commit in affine format

    %accumulating into R using affinecommit, Z, and Y. appends binary data, we eventually hash it all.

    %{R, Ys, Zs, Commits}
    ok.
batch_stream3(Tree, RootStem, DivEAll) ->
    %{hashes, Y, Z, commit} for every relationship in tree2. Hashes are in integer form, committed data of the parent. Z is an element of the domain, the index being looked up. commit is the elliptic point of the child, in simplified format.
    %A is hashes.
    %Y is the hash we are looking up.

    %accumulate into G2 with R, A, Y, Z, Domain, DA). basically, one iteration of calc_G_e2.

    %{G2}.
    ok.

batch(Keys, Root, CFG) ->
    RootStem0 = stem:get(Root, CFG),
    RootStem = RootStem0#stem{
                 hashes = binary2int2(
                            tuple_to_list(
                              RootStem0#stem.hashes))},
    io:fwrite("get 0\n"),
    Paths = keys2paths(Keys, CFG),
    %Paths example: [[1,4,3,2],[1,1,1,2],[1,1,1,1],[2,1,1,1]]
    io:fwrite("get 0.5\n"),
    Tree = paths2tree(Paths),
    %Tree example [[1|[[4,3,2], [1,1|[[1], [2]]]]], [2,1,1,1]],
    %list of lists means or. list of integers means and.
    io:fwrite("get 1\n"),
    %a little slow.
    %[[1,0,0,0],[2,0,0,0]...
    Tree2 = points_values(Tree, RootStem, CFG),
    %io:fwrite(Tree2),
    %obtains the stems and leaves by reading from the database.
    %[stem, {I, stem}, [{I, leaf}], [{I, stem}, {I, leaf}], [{I, stem}, [{I, leaf}], [{I, leaf}]]]
    %list of things is AND, list of lists is OR.
    io:fwrite("get 2\n"),
    Tree3 = withdraw_points(Tree2),%removing duplicate elliptic points by shifting all the points one step towards the root.
    %looks the same, just changes which elliptic point is written where.
    io:fwrite("get 3\n"),
    Tree4 = remove_hashes(Tree3),%the hashes in each stem aren't needed to verify the verkle proof, so they are removed.
    %[El, {I, El}, [{I, leaf}], [{I, El}, {I, El}], [{I, El}, [{I, El}], [{I, El}]]]

    io:fwrite("get 4\n"),

    Lookups = flatten(Tree2, []),
    io:fwrite("get 5\n"),
    {Zs0, Commits, As0} = split3parts(Lookups, [], [], []),
    io:fwrite("get 6\n"),
    P = parameters:read(),
    io:fwrite("get 7\n"),
    Zs = index2domain2(
           Zs0, list_to_tuple(P#p.domain)),
    io:fwrite("get 8\n"),
    As = As0,

    io:fwrite("get 9\n"),
    %the slow step.
    {CommitG, Opening} = 
        multiproof:prove(As, Zs, Commits, P),%this is the slow step.
    io:fwrite("get 10\n"),

    %sanity checks
    %Tree5 = verify:unfold(Root4, Tl4, [], CFG),
    %tree5 is empty.
    %{Commitsb, Zs0b, _} = 
    %    split3parts(Tree5, [], [], []),
    %io:fwrite({Tree5}),
    %Ys = lists:zipwith(
    %       fun(F, Z) ->
    %               poly:eval_e(Z, F, P#p.domain, 
    %                           secp256k1:order(
    %                             P#p.e))
    %       end, As, Zs),
    %true = multiproof:verify({CommitG, Opening}, Commits, Zs, Ys, P), 

    {Tree4, CommitG, Opening}.
   
binary2int([]) -> [];
binary2int([H|T]) ->
    L = tuple_to_list(H),
    L2 = binary2int2(L),
    [L2|binary2int(T)].
binary2int2([]) -> [];
binary2int2([<<H:256>>|T]) -> 
    [H|binary2int2(T)].
              
    %remove duplicate elliptic points in the tree structure by moving where they are written more towards the root of the tree.
withdraw_points(X = [[{_, R}|_]|_]) ->
    T = withdraw_points2(X),
    %R2 = R, %HERE
    R2 = {-1, R},
    case T of
        [] -> R2;
        _ -> [R2|T]
    end;
    %[R|withdraw_points2(X)];
withdraw_points(X = [{_, R}|_]) ->
    %[R|withdraw_points3(X)].
    [{-1, R}|withdraw_points3(X)].
withdraw_points2(Xs) ->
    L = lists:map(fun withdraw_points3/1,
                  Xs),
    lists:filter(fun(X) -> not(X == []) end,
                 L).
                             
withdraw_points3(X = [{I, _}, 
                      {_, P = #stem{}}
                      |_]) ->
    [_|Y] = X,
    [{I, P}|withdraw_points3(Y)];
withdraw_points3(X = [{I, _}, 
                      [{_, P = #stem{}}|_]
                      |_]) ->
    [_|Xs] = X,
    [{I, P}|withdraw_points2(Xs)];
withdraw_points3([{I, _}, L = #leaf{}]) ->
    [{I, L}];
withdraw_points3([{_, #stem{}}|R]) -> 
    withdraw_points3(R);
%withdraw_points3([{_, S = #stem{}}]) -> S;
withdraw_points3([H|T]) when is_list(H) ->
    X = withdraw_points3(H),
    Y = withdraw_points3(T),
    case X of
        [] -> Y;
        _ -> [X|Y]
    end;
withdraw_points3([]) -> [].

   
remove_hashes({-1, X = #stem{}}) -> X#stem.root;
remove_hashes({Index, X = #stem{}}) -> 
    {Index, X#stem.root};
remove_hashes({Index, X = #leaf{}}) -> 
    {Index, {X#leaf.key, X#leaf.value}};
remove_hashes(X = #leaf{}) -> 
    {X#leaf.key, X#leaf.value};
remove_hashes([H|T]) -> 
    [remove_hashes(H)|
     remove_hashes(T)];
remove_hashes(X) -> X.
    
flatten({Index, S = #stem{}}, T) -> 
    %[{Index, S#stem.root, S#stem.hashes}|T];
    H = S#stem.hashes,
    %H = binary2int2(tuple_to_list(S#stem.hashes)),
    [{Index, S#stem.root, H}|T];
flatten(X = {_Index, _Point, _Hashes}, T) -> [X|T];
flatten([H|T], R) -> 
    R2 = flatten(H, []),
    flatten(T, R ++ R2);
flatten(_, R) -> R.
    

split3parts([], A, B, C) -> {A, B, C};
split3parts([{X, Y, Z}|T], A, B, C) -> 
    split3parts(T, [X|A], [Y|B], [Z|C]).

index2domain2([], _Domain) -> [];
index2domain2([H|T], Domain) ->
    [element(H+1, Domain)|
     index2domain2(T, Domain)].

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


points_values([<<Loc:?nindex>>|R], Root, CFG) 
  when is_integer(Loc)->
    Type = stem:type(Loc+1, Root),
    P = stem:pointer(Loc+1, Root),
    %EllipticPoint = stem:root(Root),
    %Hashes = stem:hashes(Root),
    V = {Loc, Root},
    case Type of
        0 -> %empty
            [V];
        1 -> %stem
            S0 = stem:get(P, CFG),
            S = S0#stem{
                  hashes = binary2int2(
                             tuple_to_list(
                               S0#stem.hashes))},
            [V|points_values(R, S, CFG)];
        2 -> %leaf
            L = leaf:get(P, CFG),
            [V, L]
    end;
points_values([H|T], Root, CFG) ->
    [points_values(H, Root, CFG)|
     points_values(T, Root, CFG)];
points_values([], _, _) -> [].

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
