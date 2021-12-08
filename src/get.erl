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
      end, Paths0).
batch(Keys, Root, CFG) ->
    RootStem = stem:get(Root, CFG),
    io:fwrite("get 0\n"),
    %a little slow.
    Paths = keys2paths(Keys, CFG),
    %Paths example: [[1,4,3,2],[1,1,1,2],[1,1,1,1],[2,1,1,1]]
    Tree = paths2tree(Paths),
    %Tree example [[1|[[4,3,2], [1,1|[[1], [2]]]]], [2,1,1,1]],
    %list of lists means or. list of integers means and.
    io:fwrite("get 1\n"),
    %a little slow.
    Tree2 = points_values(Tree, RootStem, CFG),
    %obtains the stems and leaves by reading from the database.

    io:fwrite("get 2\n"),
    Tree3 = withdraw_points(Tree2),%removing duplicate elliptic points by shifting all the points one step towards the root.
    io:fwrite("get 3\n"),
    Tree4 = remove_hashes(Tree3),%the hashes in each stem aren't needed to verify the verkle proof, so they are removed.

    io:fwrite("get 4\n"),
    Lookups = flatten(Tree2, []),
    io:fwrite("get 5\n"),
    {Zs0, Commits, As0} = split3parts(Lookups, [], [], []),
    io:fwrite("get 6\n"),
    P = parameters:read(),
    io:fwrite("get 7\n"),
    Zs = index2domain(Zs0, P#p.domain),
    io:fwrite("get 8\n"),
    %medium slow.
    As = binary2int(As0),

    io:fwrite("get 9\n"),
    %the slow step.
    %crashes here.
    {CommitG, _Commits2, Opening} = multiproof:prove(As, Zs, Commits, P),%this is the slow step.
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
    %true = multiproof:verify({CommitG, Commits2, Opening}, Zs, Ys, P), 

    {Tree4, CommitG, Opening}.
                      
binary2int([]) -> [];
binary2int([Tup|R]) when is_tuple(Tup) -> 
    L1 = tuple_to_list(Tup),
    L = binary2int(L1),
    [L|binary2int(R)];
binary2int([<<H:256>>|T]) -> 
    [H|binary2int(T)].

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
    [{Index, S#stem.root, S#stem.hashes}|T];
flatten(X = {_Index, _Point, _Hashes}, T) -> [X|T];
flatten([H|T], R) -> 
    R2 = flatten(H, []),
    flatten(T, R ++ R2);
flatten(_, R) -> R.
    

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
    %EllipticPoint = stem:root(Root),
    %Hashes = stem:hashes(Root),
    V = {Loc, Root},
    case Type of
        0 -> %empty
            [V];
        1 -> %stem
            [V|points_values(R, stem:get(P, CFG), 
                             CFG)];
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
