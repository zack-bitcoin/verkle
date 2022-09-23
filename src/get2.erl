-module(get2).
-export([
batch/3, index2domain/2, paths2tree/1,
%get/3, same_end/3, 
split3parts/4, 
keys2paths/2, 
withdraw_points/1, withdraw_points2/1,
compressed_points_list/1,
test/1]).
-include("constants.hrl").

-define(pipe, false).
-define(sanity, true).

keys2paths(Keys, CFG) ->
    Paths0 = lists:map(
              fun(<<K:256>>) -> 
                      leaf:path_maker(K, CFG) 
              end, Keys),
    lists:map(
      fun(Path) ->
              lists:map(
                fun(<<P:?nindex>>) ->
                        P end, Path)
      end, Paths0),
    Paths0.

batch(Keys, Root, CFG) ->
    RootStem0 = stem2:get(Root, CFG),
    %io:fwrite(RootStem0#stem.hashes),
    RootStem = RootStem0#stem{
                 %hashes = 
                 %      RootStem0#stem.hashes},
                 hashes = 
                     %binary2int2(
                     %fr:decode(
                       tuple_to_list(
                         RootStem0#stem.hashes)},
    io:fwrite("get keys2paths\n"),
    benchmark:now(),
    Paths0 = keys2paths(Keys, CFG),
    Paths = lists:sort(fun(A, B) -> A < B end, 
                       Paths0),
    %Paths example: [[1,4,3,2],[1,1,1,2],[1,1,1,1],[2,1,1,1]]
    io:fwrite("get paths2tree\n"),
    benchmark:now(),

    Tree = paths2tree(Paths),
    %Tree example [[1|[[4,3,2], [1,1|[[1], [2]]]]], [2,1,1,1]],
    %list of lists means or. list of integers means and.
    io:fwrite("get lookup stems and leaves\n"),% 25%
    benchmark:now(),
    Tree2 = points_values(Tree, RootStem, CFG),

    if
        true ->
            GoodPoint = element(2, element(2, hd(tl(hd(Tree2))))),
            128 = size(GoodPoint),
            C = ed:compress_point(GoodPoint),
            Good2 = ed:affine2extended(ed:decompress_point(C)),
            C = ed:compress_point(Good2),
            ed:e_eq(GoodPoint, Good2),
            Hash1 = stem2:hash_point(GoodPoint),
            Hash2 = stem2:hash_point(Good2),
            Hash1 = Hash2,
            
            


                %fr:decode(hd(element(5, element(2, hd(hd(Tree2))))))},%good
               %fr:decode(ed:compress_point(element(2, element(2, hd(tl(hd(Tree2))))))),%bad
               %fr:decode(stem2:hash_point(ed:decompress_point(ed:compress_point(element(2, element(2, hd(tl(hd(Tree2))))))))),%good
            ok;
        true -> ok
    end,
    %obtains the stems and leaves by reading from the database.
    %[stem, {I, stem}, [{I, leaf}], [{I, stem}, {I, leaf}], [{I, stem}, [{I, leaf}], [{I, leaf}]]]
    %list of things is AND, list of lists is OR.
    io:fwrite("get remove duplicate elliptic points\n"),
    benchmark:now(),
    Tree3 = withdraw_points(Tree2),%removing duplicate elliptic points by shifting all the points one step towards the root.
    %looks the same, just changes which elliptic point is written where.
    io:fwrite("get remove hashes\n"),
    benchmark:now(),
    Tree4 = remove_hashes(Tree3),%the hashes in each stem aren't needed to verify the verkle proof, so they are removed.
    %[El, {I, El}, [{I, leaf}], [{I, El}, {I, El}], [{I, El}, [{I, El}], [{I, El}]]]
    %io:fwrite(fr:decode(ed:compress_point(element(2, hd(hd(tl(Tree4))))))),%bad point!


    io:fwrite("get flatten\n"),
    benchmark:now(),

    Lookups = flatten(Tree2, []),
    io:fwrite("get split3\n"),
    benchmark:now(),
    {Zs0, Commits, As0} = 
        split3parts(Lookups, [], [], []),
    ToPrint4 = fr:decode(hd(hd(tl(As0)))),
    <<_:256>> = hd(hd(tl(As0))),
    %confirmed that As are not points, they are hashes.
    io:fwrite(integer_to_list(ToPrint4)), %This is the version being used when generating the proof. 
    io:fwrite("\n"),
    %io:fwrite(integer_to_list(PHash)), 
    io:fwrite("get lookup parameters\n"),
    benchmark:now(),
    Domain = parameters2:domain(),
    io:fwrite("get index to domain conversion\n"),
    benchmark:now(),
    Zs = index2domain2(
           Zs0, list_to_tuple(Domain)),
    As = As0,
    %io:fwrite({As}),

    io:fwrite("get make multiproof\n"),% 8%
    benchmark:now(),
    %the slow step.
    io:fwrite("param 0\n"),% 8%
    {Gs, Hs, Q} = parameters2:read(),
    io:fwrite("param 1\n"),% 8%
    DA = parameters2:da(),
    io:fwrite("param 2\n"),% 8%
    PA = parameters2:a(),
    io:fwrite("param 3\n"),% 8%
    Domain = parameters2:domain(),
    io:fwrite("param done\n"),% 8%
    %io:fwrite({As}),
    %FAs = fr:encode(As),%crashes here.
    FAs = As,
    io:fwrite("Fas done\n"),% 8%
    FZs = fr:encode(Zs),
    io:fwrite("Fzs done\n"),% 8%
    %io:fwrite({length(hd(FAs)), length(FAs), length(FZs), length(Commits), hd(FAs), hd(FZs), hd(Commits)}),
    %256,1,1,1
    %FAs is list of binaries. FZs is binaries. commits is binaries

    if
        ?sanity -> 
            lists:map(
              fun(Z) ->
                      B = is_in(Z, Domain),
                      if
                          B -> ok;
                          true -> io:fwrite({Z, Domain})
                      end
              end, FZs),
            true = (length(Commits)) == (length(As)),
            lists:zipwith(
              fun(Old, A) ->
    %verify that the commits are over FAs.
                      New = ipa2:commit(A, Gs),
                      B = ed:e_eq(Old, New),
                      if
                          B -> ok;
                          true -> 1=2
                      end
              end, Commits, As),
            ok;
        true -> ok
    end,

    {CommitG, Opening} = 
        multiproof2:prove(
          FAs, FZs, Commits,
         Gs, Hs, Q, DA, PA, Domain),

    if
        ?sanity ->
            Ys = lists:zipwith(
                    fun(F, Z) ->
                            poly2:eval_e(Z, F, Domain)
                    end, FAs, FZs),
            true = multiproof2:verify(
                     {CommitG, Opening}, 
                   %Commits, Zs, fr:decode(Ys)),
                     Commits, FZs, Ys);
        true -> ok
    end,


    io:fwrite("get done\n"),
    benchmark:now(),

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

    %io:fwrite(
    %{Tree4, CommitG, Opening}),
    %{Tree, E, {E, E, [E...]}}
    TLO = tuple_to_list(Opening),
    Listed = [Tree4, CommitG, TLO],
    PointsList = 
        points_list(Listed),
    %Spoints = fq:compress(PointsList),
    %Spoints = ed:compress_points(PointsList),
    %TODO this can be batched!!!!!
    Spoints = lists:map(fun(X) ->
                                %stem2:hash_point(X)
                                ed:compress_point(X)
                        end, PointsList),
    {[Tree5, CommitG2, Opening2], []} =
        fill_points(Spoints, Listed, []),
    {Tree5, CommitG2, list_to_tuple(Opening2)}.
    %{Tree4, CommitG, Opening}.
%points_list([<<E:1024>>|T]) ->%1024 bits in an extended bit.
%    [<<E:1024>>|points_list(T)];
%tree_leaves(X = {<<_:256>>, Value}) 
%  when is_binary(Value) -> [X];
%tree_leaves([]) -> [];
%tree_leaves([H|T]) -> 
%    tree_leaves(H) ++ tree_leaves(T);
%tree_leaves(T) when is_tuple(T) -> 
%    tree_leaves(tuple_to_list(T));
%tree_leaves(_) ->  [].

points_list(<<E:1024>>) -> [<<E:1024>>];
points_list({I, <<E:1024>>}) when is_integer(I) ->
    %[<<E:1024>>];
    [<<E:1024>>];
points_list([H|T]) ->% when is_list(H) ->
    points_list(H) ++ points_list(T);
%points_list([_|T]) ->
%    points_list(T);
points_list({I, {_Key, _Value}}) 
  when is_integer(I) -> 
    %a leaf.
    [];
points_list(<<_:256>>) -> [];
points_list([]) -> [].
%points_list(_) -> [].

compressed_points_list(X = <<_:256>>) -> 
%    1=2,
    [X];
compressed_points_list(X = <<_:512>>) -> 
    1=2,
    [ed:compress_point(X)];
compressed_points_list(X = <<_:1024>>) -> 
    1=2,
    ed:compress_points([X]);
compressed_points_list({I, X = <<_:256>>}) 
  when is_integer(I) -> 
    %1=2,
    [X];
compressed_points_list({I, X = <<_:512>>}) 
  when is_integer(I) -> 
    1=2,
    [ed:compress_point(X)];
compressed_points_list({I, X = <<_:1024>>}) 
  when is_integer(I) -> 
    %[stem2:hash_point(X)];
    1=2,
    P2 = ed:e_mul2(X, <<8:256/little>>),
    ed:compress_points([P2]);
%ed:compress_points([X]);
compressed_points_list([H|T]) -> 
    compressed_points_list(H) ++
        compressed_points_list(T);
compressed_points_list([]) -> [];
compressed_points_list({_Key, _Value}) -> 
    %a leaf
    [];
%compressed_points_list(X) -> 
%    io:fwrite({X, size(X)});
compressed_points_list(_) -> [].

fill_points(Points, [], Result) -> 
    {lists:reverse(Result), Points};
fill_points(Ps, [T|R], Result) when is_list(T) ->
    {T2, Ps2} = fill_points(Ps, T, []),
    fill_points(Ps2, R, [T2|Result]);
fill_points([P|PT], [{I, <<_:1024>>}|R], Result) 
  when is_integer(I) ->
    fill_points(PT, R, [{I, P}|Result]);
fill_points([P|PT], [<<_:1024>>|R], Result) ->
    fill_points(PT, R, [P|Result]);
fill_points(Ps, [T|R], Result) ->
    fill_points(Ps, R, [T|Result]).


    

   
%binary2int([]) -> [];
%binary2int([H|T]) ->
%    L = tuple_to_list(H),
%    L2 = fr:decode(L),
%    [L2|binary2int(T)].
%binary2int2([]) -> [];
%binary2int2([<<H:256>>|T]) -> 
%    [H|binary2int2(T)].
%binary2int2([<<H:256>>|T]) -> 
%    [fr:decode(<<H:256>>)|
%     binary2int2(T)].
              
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
%withdraw_points3([{I, _}, {Next, 0}]) ->
withdraw_points3([{I, _}, 0]) ->
    %[{I, {Next, 0}}];
    [{I, 0}];
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
withdraw_points3([0]) -> [];
withdraw_points3([]) -> [].

   
remove_hashes({-1, X = #stem{}}) -> X#stem.root;
remove_hashes({Index, X = #stem{}}) -> 
    {Index, X#stem.root};
    %{Index, stem2:hash_point(X#stem.root)};
remove_hashes({Index, X = #leaf{}}) -> 
    %{Index, {leaf:key(X), leaf:value(X)}};
    {Index, {leaf:raw_key(X), leaf:value(X)}};
remove_hashes([H|T]) -> 
    [remove_hashes(H)|
     remove_hashes(T)];
remove_hashes(X) -> X.
    
flatten({Index, S = #stem{}}, T) -> 
    %[{Index, S#stem.root, S#stem.hashes}|T];
    H = S#stem.hashes,
    %H = binary2int2(tuple_to_list(S#stem.hashes)),
    
    [{Index, S#stem.root, H}|T];
flatten([H|T], R) -> 
    R2 = flatten(H, []),
    flatten(T, R ++ R2);
flatten(_, R) -> R.

    

split3parts([], A, B, C) -> {A, B, C};
split3parts([{X, Y, Z}|T], A, B, C) -> 
    split3parts(T, [X|A], [Y|B], [Z|C]).

index2domain2([], _Domain) -> [];
index2domain2([H|T], Domain) ->
    [%element(H+1, Domain)|
     H+1|%for domain that is the integers.
     index2domain2(T, Domain)].

index2domain(Zs, Domain) ->
    D = setup_domain_dict(0, Domain, dict:new()),
    lists:map(fun(Z) -> dict:fetch(Z, D) end, Zs).
setup_domain_dict(_, [], D) -> D;
setup_domain_dict(I, [A|T], D) -> 
    D2 = dict:store(I, A, D),
    setup_domain_dict(I+1, T, D2).
    
paths2tree([]) -> [];
paths2tree([[]]) -> [];
paths2tree([Path]) -> [Path];
%paths2tree([Path]) -> Path;
paths2tree(Paths) ->
    {Same, Others} = starts_same_split(Paths),
    H = hd(hd(Same)),
    Same2_0 = lists:map(fun(S) -> tl(S) end,
                      Same),
    Same2_1 = paths2tree(Same2_0),
    Same2 = case Same2_1 of
                [X] -> X;
                Y -> Y
            end,
    Path1 = [H|Same2],
    Recurse = paths2tree(Others),
    if
        (Others == []) -> Path1;
        (is_list(hd(Recurse))) -> 
            [Path1|Recurse];
        true -> [Path1, Recurse]
    end.
starts_same_split([[X|B]|T]) ->
    starts_same_split2(X, T, [[X|B]]).
starts_same_split2(X, [[X|B]|T], Sames) ->
    starts_same_split2(X, T, [[X|B]|Sames]);
starts_same_split2(_, Rest, Sames) ->
    {lists:reverse(Sames), Rest}.


points_values([<<Loc:?nindex>>|R], Root, CFG) ->
    % Root is a #stem{}
    Type = stem2:type(Loc+1, Root),
    P = stem2:pointer(Loc+1, Root),
    %EllipticPoint = stem:root(Root),
    %Hashes = stem:hashes(Root),
    V = {Loc, Root},
    case Type of
        0 -> %empty
            %[<<NextLoc:?nindex>>|_] = R,
            %[V, {NextLoc, 0}];
            [V, 0];
        1 -> %stem
            S0 = stem2:get(P, CFG),
            S = S0#stem{
                  %hashes= fr:decode(S0#stem.hashes)
                  %hashes = binary2int2(
                  hashes = %fr:decode(
                             tuple_to_list(
                               S0#stem.hashes)%)
                 },
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

is_in(X, [X|_]) -> true;
is_in(X, []) -> false;
is_in(X, [_|T]) -> 
    is_in(X, T).



test(1) ->
    CFG = trie:cfg(trie01),
    A = [1,2,3,4,5],
    B = [3,4,5] ++ A,
    true = same_end(B, A, CFG),
    success.
