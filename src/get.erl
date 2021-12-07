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
    Paths = keys2paths(Keys, CFG),
    %Paths example: [[1,4,3,2],[1,1,1,2],[1,1,1,1],[2,1,1,1]]
    Tree = paths2tree(Paths),
    %Tree example [[1,[[4,3,2], [1,1,[[1], [2]]]]], [2,1,1,1]],
    %list of lists means or. list of integers means and.
    Tree2 = points_values(Tree, RootStem, CFG),
    %obtains the stems and leaves by reading from the database.

    %Tree3b = remove_hashes(Tree2),
    %removes the lists of hashes, as they aren't needed to verify a verkle proof.
    %io:fwrite({Tree3}),
    %Tree4b = withdraw_points(Tree3b),
    Tree3 = withdraw_points(Tree2),
    %io:fwrite(Tree2),
    Tree4 = remove_hashes(Tree3),
    %io:fwrite(Tree3),
    %io:fwrite({Tree4, Tree4b}),
    %removes repeated elliptic points, by shifting all the elliptic points one step towards the root.
%this is the version we will send to them, so we should use it to build up the commits.

    [Root4|Tl4]=Tree4,
    %io:fwrite({Tree4}),%[[{1, 35}, [{0, l1}],[{1,l5}]], [{2, 10},{0,l2}, {3, 17},{0, l3}]]
            %error is in "l2}, {3,", there should be a list seperation here.


    %io:fwrite(Tree2),
    %Tree example [[{point, 1, Hashes},[[{point, 4, hashes}], [{point, 1, hashes},{point, 1, hashes},[[{point, 1, hashes}], [2]]]]], [{2, point}]],
    Lookups = flatten(Tree2, []),
    %io:fwrite({Lookups}),
    %Leaves = get_leaves(Tree2, []),
    %Structure = structure(Tree2, 0),
    %io:fwrite({Leaves, Structure, Tree2}),
    {Zs0, Commits, As0} = split3parts(Lookups, [], [], []),
    Zs = index2domain(Zs0, ?p#p.domain),
    %io:fwrite({Zs}),
    As = binary2int(As0),


    %io:fwrite({length(As), length(Zs), length(Commits)}),
    %io:fwrite({hd(As), hd(Zs), hd(Commits)}),
    %Proof = multiproof:prove(As, Zs, Commits, ?p),
    %io:fwrite({Zs}),%[1,4,1,3,2,1,2]
    %io:fwrite(Commits),%[17,88,10,88,35,35,88]
    {CommitG, Commits2, Opening} = multiproof:prove(As, Zs, Commits, ?p),

    %sanity check
    Tree5 = verify:unfold(Root4, Tl4, [], CFG),
    %tree5 is empty.
    {Commitsb, Zs0b, _} = 
        split3parts(Tree5, [], [], []),
    %io:fwrite({Tree5}),
    Ys = lists:zipwith(
           fun(F, Z) ->
                   poly:eval_e(Z, F, ?p#p.domain, 
                               secp256k1:order(
                                 ?p#p.e))
           end, As, Zs),
    true = multiproof:verify({CommitG, Commits2, Opening}, Zs, Ys, ?p),

    %[[{1, p1}, [{0, p2}, l1], [{1, p2}, l2]]
    % [{3, p1}, {0, p3} l3]]
    %io:fwrite({Tree3, RootStem}),

    %io:fwrite({Tree3}),%[{1, p1}, [{0, p2},l1], [[{1, p2}, l2], [{2, p2},l3]]]
    %fail. withdraw_points3([[{1, p1}, l2], [{2, p1}, l3]]

    %io:fwrite({Tree4}),
    %{p1 [{1, p2},
    %{p1, [{1, p2}, [{0, l1}, {1, l2}]],
    %     [{3, p3}, [{0, l3}]]}
    %io:fwrite({Tree3}),
    %{Tree4, Proof}.
    {Tree4, CommitG, Opening}.
    %multiproof:prove(stem:hashes, slot in each commit to read from, commits, ?p)
                      
    %batch2(Paths, [P], CFG).
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
    R = lists:filter(fun(X) -> not(X == []) end,
                 L),
    R.
%    case R of
%        [R1] -> R1;
%        _ -> R
%    end.
            
                             
withdraw_points3(X = [{I, _}, 
                      {_, P = #stem{}}
                      |T]) ->
    [_|Y] = X,
    [{I, P}|withdraw_points3(Y)];
%withdraw_points3(X = [{I, _}, 
%                      {_, P = {_, _, _}}
%                      |T]) ->
%    [_|Y] = X,
%    [{I, P}|withdraw_points3(Y)];
withdraw_points3(X = [{I, _}, 
                      [{_, P = #stem{}}|T1]
                      |T2]) ->
    [_|Xs] = X,
    [{I, P}|withdraw_points2(Xs)];
%withdraw_points3(X = [{I, _}, 
%                      [{_, P = {_, _, _}}|T1]
%                      |T2]) ->
%    [_|Xs] = X,
%    [{I, P}|withdraw_points2(Xs)];
%withdraw_points3(X = [{I, _}, L = {_, B}]) 
%  when is_binary(B) ->
%    [{I, L}];
withdraw_points3(X = [{I, _}, L = #leaf{}]) ->
    [{I, L}];
withdraw_points3([{_, S = #stem{}}|R]) -> 
    withdraw_points3(R);
%withdraw_points3([[{_, S = #stem{}}]]) -> S;
withdraw_points3([{_, S = #stem{}}]) -> S;
withdraw_points3([H|T]) when is_list(H) ->
    X = withdraw_points3(H),
    Y = withdraw_points3(T),
    case X of
        [] -> Y;
        _ -> [X|Y]
    end;
%    [withdraw_points3(H)|
%        withdraw_points3(T)];
    %withdraw_points3(H) ++
    %    withdraw_points3(T);
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
    
%flatten(X = {Point, Index, Hashes}, T) -> [X|T];
flatten(X = {Index, S = #stem{}}, T) -> 
    [{Index, S#stem.root, S#stem.hashes}|T];
    %[X|T];
flatten(X = {Index, Point, Hashes}, T) -> [X|T];
flatten([H|T], R) -> 
    R2 = flatten(H, []),
    flatten(T, R ++ R2);
%flatten([_|T], R) -> flatten(T, R);
flatten(_, R) -> R.
get_leaves(L = {A, B}, R) ->
    [L|R];
get_leaves([H|T], R) ->%when is_list(H) ->
    R2 = get_leaves(H, []),
    get_leaves(T, R ++ R2);
%get_leaves([_|T], R) -> get_leaves(T, R);
get_leaves(_, R) -> R.
%structure([H|T], N) when is_list(H) ->
%    structure(H, N) ++ structure(T, N);
%structure([L|T], N) when is_record(L, leaf) ->
%    [N] ++structure(T, N);
%structure([{_, _, _}|T], N) ->
%    structure(T, N+1);
%structure([[]|T], N) ->
%    structure(T, N);
%structure([], _) -> [].



%structure([_|T], N) ->
%    structure(T, N+1);
%structure(_, N) -> [].


    
    

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
