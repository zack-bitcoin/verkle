-module(get_verkle).
-export([
batch/3, batch/4, 
paths2tree/1,
index2domain2/1,
%get/3, same_end/3, 
split3parts/4, 
keys2paths/2, 
withdraw_points/1, withdraw_points2/1,
compressed_points_list/1,
serialize_proof/1, deserialize_proof/1,
unverified/3,
test/1]).
-include("constants.hrl").

-define(pipe, false).
-define(sanity, false).

keys2paths(Keys, CFG) ->
    Paths0 = lists:map(
              fun(<<K:256>>) -> 
                      leaf_verkle:path_maker(K, CFG) 
              end, Keys),
    lists:map(
      fun(Path) ->
              lists:map(
                fun(<<P:?nindex>>) ->
                        P end, Path)
      end, Paths0),
    Paths0.

remove_stems_from_straight_branches(L) ->
    lists:map(fun(X) -> lists:last(hd(X)) end, L).

%returns the consensus state and meta values for each leaf. Does not create any proof.
unverified(Keys, Root, CFG) ->
    RootStem0 = stem_verkle:get(Root, CFG),
    RootStem = RootStem0#stem{
                 hashes = 
                       tuple_to_list(
                         RootStem0#stem.hashes)},
    Paths0 = keys2paths(Keys, CFG),
    Paths = lists:sort(fun(A, B) -> A < B end, 
                       Paths0),
    Tree3 = lists:map(fun(P) ->
                              Tree = paths2tree([P]),
                              Tree2 = points_values(Tree, RootStem, CFG)
                      end, Paths),
    Leaves0 = remove_stems_from_straight_branches(Tree3),
    Leaves = lists:zipwith(fun(L, K) ->
                                   {K, L}
                           end, Leaves0, 
                           depth_order(Keys)),
    Leaves.

depth_order(Keys) ->
    K2 = lists:map(fun(K) ->
                           <<A:256/little>> = K,
                           <<B:256>> = 
                               <<A:256/big>>,
                           {K, B}
                   end, Keys),
    K3 = lists:sort(fun({K, B}, {K2, B2}) ->
                            B < B2
                    end, K2),
    lists:map(fun({K, _}) ->
                      K end, K3).
    
    

%returns a verkle proof, and a dictionary of meta data from each leaf.
batch(Keys, Root, CFG) ->
    batch(Keys, Root, CFG, small).

batch(Keys, Root, CFG, Type) ->
    true = ((Type == small) or (Type == fast)),
    RootStem0 = stem_verkle:get(Root, CFG),
    RootStem = RootStem0#stem{
                 hashes = 
                       tuple_to_list(
                         RootStem0#stem.hashes)},
    %io:fwrite("get keys2paths\n"),
    benchmark:now(),
    Paths0 = keys2paths(Keys, CFG),
    Paths = lists:sort(fun(A, B) -> A < B end, 
                       Paths0),
    %Paths example: [[1,4,3,2],[1,1,1,2],[1,1,1,1],[2,1,1,1]]
    %io:fwrite("get paths2tree\n"),
    benchmark:now(),

    Tree = paths2tree(Paths),
    %Tree example [[1|[[4,3,2], [1,1|[[1], [2]]]]], [2,1,1,1]],
    %list of lists means or. list of integers means and.
    %io:fwrite("get lookup stems and leaves\n"),% 25%
    benchmark:now(),
    Tree2 = points_values(Tree, RootStem, CFG),
    %io:fwrite({RootStem}),

    %obtains the stems and leaves by reading from the database.
    %[stem, {I, stem}, [{I, leaf}], [{I, stem}, {I, leaf}], [{I, stem}, [{I, leaf}], [{I, leaf}]]]
    %list of things is AND, list of lists is OR.
    %io:fwrite("get remove duplicate elliptic points\n"),
    benchmark:now(),
    Tree3 = withdraw_points(Tree2),%removing duplicate elliptic points by shifting all the points one step towards the root.
    %looks the same, just changes which elliptic point is written where.
    %io:fwrite("get remove hashes\n"),
    benchmark:now(),
    Tree4 = remove_hashes(Tree3),%the hashes in each stem aren't needed to verify the verkle proof, so they are removed.
    
    %todo, strip the meta data from the leaves.

    %[El, {I, El}, [{I, leaf}], [{I, El}, {I, El}], [{I, El}, [{I, El}], [{I, El}]]]
    %io:fwrite(fr:decode(ed:compress_point(element(2, hd(hd(tl(Tree4))))))),%bad point!


    %io:fwrite("get flatten\n"),
    benchmark:now(),

    Lookups = flatten(Tree2, []),
    %io:fwrite({Lookups}),
    %io:fwrite("get split3\n"),
    benchmark:now(),
    {Zs0, Commits, As0} = 
        split3parts(Lookups, [], [], []),
    %ToPrint4 = fr:decode(hd(hd(tl(As0)))),
    %<<_:256>> = hd(hd(tl(As0))),
    %confirmed that As are not points, they are hashes.
    %io:fwrite(integer_to_list(ToPrint4)), %This is the version being used when generating the proof. 
    %io:fwrite("\n"),
    %io:fwrite(integer_to_list(PHash)), 
    %io:fwrite("get lookup parameters\n"),
    benchmark:now(),
    Domain = parameters:domain(),
    %io:fwrite("get index to domain conversion\n"),
    benchmark:now(),
    Zs = index2domain2(
           Zs0),
    As = As0,
    %io:fwrite({As}),

    %io:fwrite("get make multiproof\n"),% 8%
    benchmark:now(),
    %the slow step.
    %io:fwrite("param 0\n"),% 8%
    {Gs, Hs, Q} = parameters:read(),
    %io:fwrite("param 1\n"),% 8%
    DA = parameters:da(),
    %io:fwrite("param 2\n"),% 8%
    PA = parameters:a(),
    %io:fwrite("param 3\n"),% 8%
    Domain = parameters:domain(),
    %io:fwrite("param done\n"),% 8%
    %io:fwrite({As}),
    %FAs = fr:encode(As),%crashes here.
    FAs = As,
    %io:fwrite("Fas done\n"),% 8%
    FZs = fr:encode(Zs),
    %io:fwrite("Fzs done\n"),% 8%
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
                      New = ipa:commit(A, Gs),
                      B = ed:e_eq(Old, New),
                      if
                          B -> ok;
                          true -> 
                              io:fwrite([ed:extended2affine_batch([Old, New]), A]),
                              1=2
                      end
              end, Commits, As),
            ok;
        true -> ok
    end,

    {CommitG, Opening} = 
        case Type of
            small ->
                multiproof:prove(
                  FAs, FZs, Commits,
                  Gs, Hs, Q, DA, PA, Domain);
            fast ->
                multiproof:fast_prove(
                  FAs, FZs, Commits,
                  Gs, Hs, Q, DA, PA, Domain)
        end,

    if
        ?sanity ->
            Ys = lists:zipwith(
                    fun(F, Z) ->
                            poly:eval_e(Z, F, Domain)
                    end, FAs, FZs),
            true = multiproof:verify(
                     {CommitG, Opening}, 
                   %Commits, Zs, fr:decode(Ys)),
                     Commits, FZs, Ys);
        true -> ok
    end,


    %io:fwrite("get done\n"),
    benchmark:now(),

    %sanity checks
    %Tree5 = verify_verkle:unfold(Root4, Tl4, [], CFG),
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
    TLO = case Type of
              small -> tuple_to_list(Opening);
              fast -> Opening
          end,
    Listed = [Tree4, CommitG, TLO],
    PointsList = 
        points_list(Listed),
    Spoints = ed:compress_points(PointsList),
    {[Tree5, CommitG2, Opening2], []} =
        fill_points(Spoints, Listed, []),
    Opening3 = case Type of
                   small -> list_to_tuple(Opening2);
                   fast -> Opening2
               end,
    {Tree6, Meta} = strip_meta(Tree5, dict:new()),
    %todo. return meta data from the leaves.
    [Root2, First|Rest] = Tree6,
    Tree7 = if
                is_list(First) and (Rest == []) ->
                    [Root2|First];
                true -> Tree6
            end,
    {{Tree7, CommitG2, Opening3}, Meta}.
    %{Tree4, CommitG, Opening}.

deserialize_tree(<<Root:256, 0, S2/binary>>) ->
    %io:fwrite("deserialize tree 0\n"),
    {D, Leftover} = deserialize_thing(S2),
    %[<<Root:256>>|D].
    %io:fwrite(D),
    Leftover = <<>>,
    if
        is_list(D) ->
            [<<Root:256>>|D];
        true ->
            [<<Root:256>>, D]
    end;
deserialize_tree(<<Root:256, N, R/binary>>) ->
    %io:fwrite("deserialize tree 1\n"),
    NumberChildren = N + 1,
    {D, <<>>} = deserialize_times(
                  NumberChildren, R),
    [<<Root:256>>|D].

deserialize_thing(<<>>) -> {[], <<>>};
deserialize_thing(<<1, I, B:256, 0, R/binary>>) ->
    {D, R2} = deserialize_thing(R),
    case D of
        <<>> ->
            {[{I, <<B:256>>}], R2};
        _ ->
            {[{I, <<B:256>>}|D], R2}
    end;
deserialize_thing(<<1, I, B:256, N0, R/binary>>) ->
    NumberChildren = N0 + 1,
    {D, R2} = deserialize_times(NumberChildren, R),
    case D of
        <<>> -> 
            {[{I, <<B:256>>}], R2};
        _ ->
            {[{I, <<B:256>>}|D], R2}
    end;
deserialize_thing(<<2, I, K:256, S:32, R/binary>>) ->
    S8 = S*8,
    <<V:S8, R2/binary>> = R,
    {[{I, {<<K:256>>, <<V:S8>>}}], R2};
deserialize_thing(<<3, I, R/binary>>) ->
    {[{I, 0}], R};
deserialize_thing(<<4, I, R/binary>>) ->
    {[{I, 1}], R}.


deserialize_times(0, R2) -> {[], R2};
deserialize_times(
  N, <<4, I, R/binary>>) -> 
    {X, <<>>} = deserialize_thing(
                  <<4, I>>),
    {Y, R2} = deserialize_times(N-1, R),
    {[X|Y], R2};
deserialize_times(
  N, <<3, I, R/binary>>) -> 
    {X, <<>>} = deserialize_thing(
                  <<3, I>>),
    {Y, R2} = deserialize_times(N-1, R),
    {[X|Y], R2};
deserialize_times(
  N, <<2, I, K:256, S:32, R/binary>>) -> 
    S8 = S * 8,
    <<V:S8, R2/binary>> = R,
    {X, <<>>} = deserialize_thing(
                  <<2, I, K:256, S:32, V:S8>>),
    {Y, R3} = deserialize_times(N-1, R2),
    {[X|Y], R3};
deserialize_times(
  N, <<1, I, B:256, 0, R/binary>>) -> 
    {X, R2} = deserialize_thing(
                  <<1, I, B:256, 0, R/binary>>),
    {Y, R3} = deserialize_times(N-1, R2),
    {[X|Y], R3};
deserialize_times(
 N, <<1, I, B:256, N0, R/binary>>) -> 
    {DT, R2} = deserialize_thing(
                <<1, I, B:256, N0, R/binary>>),
    {DT2, R3} = deserialize_times(N-1, R2),
    %{[[{I, <<B:256>>}|DT]|DT2], R3}.
    {[DT|DT2], R3}.
    


    
    

serialize_tree([<<Root:256>>, L|Rest]) 
  when is_list(L) ->
    %first stem has more than one child.
    N = length([L|Rest]),
    A = lists:map(
          fun(X) -> serialize_thing(X)
          end, [L|Rest]),
    A2 = ordered_fold(A),
    <<Root:256, (N-1), A2/binary>>;
serialize_tree([<<Root:256>>|Rest]) ->
    S2 = serialize_thing(Rest),
    <<Root:256, 0, S2/binary>>.
serialize_thing([{I, B}, L|T]) when is_list(L) ->
    %the stem has multiple children.
    N = length([L|T]),
    A = lists:map(
          fun(X) -> serialize_thing(X)
          end, [L|T]),
    A2 = ordered_fold(A),
    <<_:256>> = B,
    true = is_integer(I),
    <<1, I, B/binary, (N-1), A2/binary>>;
serialize_thing([{I, B}|L]) when is_integer(I) and (I < 256) and is_binary(B)->
    %stem with one child.
    A3 = serialize_thing(L),
    <<1, I, B/binary, 0, A3/binary>>;
serialize_thing({I, {K, V}}) 
  when is_integer(I) and
       is_binary(K) and
       is_binary(V) ->
    S = size(V),
    <<2, I, K/binary, S:32, V/binary>>;
serialize_thing([{I, {K, V}}]) ->
    serialize_thing({I, {K, V}});
serialize_thing({I, 0}) when is_integer(I) ->
    <<3, I>>;
serialize_thing([{I, 0}]) ->
    serialize_thing({I, 0});
serialize_thing([[{I, 0}]]) ->
    serialize_thing({I, 0});
serialize_thing({I, 1}) when is_integer(I) ->
    <<4, I>>;
serialize_thing([{I, 1}]) ->
    serialize_thing({I, 1});
serialize_thing([[{I, 1}]]) ->
    serialize_thing({I, 1}).


ordered_fold(L) ->
    lists:foldl(
      fun(B, A) -> 
              <<A/binary, B/binary>> end, 
      <<>>, L).
chop_binary(Chunks, <<X:256, R/binary>>) 
->
    [<<X:256>>|chop_binary(Chunks-1, R)];
chop_binary(0, <<>>) -> [].

    
    
serialize_proof({Tree, Commit, Opening}) ->
    %io:fwrite({size(Commit), Tree, Commit, Opening}),
    {<<A:256>>, <<B:256>>, L3, <<C:256>>, <<D:256>>} = Opening,
    L17 = ordered_fold(L3),
    TreeBin = serialize_tree(Tree),
    32 = size(Commit),
    17 = length(L3),
    lists:map(fun(X) -> <<_:256>> = X end,
              L3),
    if
        %?sanity ->
        true ->
            Tree2 = deserialize_tree(TreeBin),
            if
                Tree2 == Tree -> ok;
                true -> io:fwrite({Tree, Tree2, size(hd(Tree)), size(hd(Tree2)), hd(Tree) == (hd(Tree2)), tl(Tree) == tl(Tree2)})
            end;
        true -> ok
    end,
    %io:fwrite("size treebin "),
    %io:fwrite(integer_to_list(size(TreeBin))),
    %io:fwrite("\n"),
    <<Commit/binary, A:256, B:256, C:256, D:256, 
      L17/binary, TreeBin/binary>>.
deserialize_proof(<<Commit:256, A:256, B:256, C:256, D:256, L17:(256*17), TreeBin/binary>>) ->
    %io:fwrite("size treebin "),
    %io:fwrite(integer_to_list(size(TreeBin))),
    %io:fwrite("\n"),
    Tree = deserialize_tree(TreeBin),
    L3 = chop_binary(17, <<L17:(256*17)>>),
    Opening = {<<A:256>>, <<B:256>>, L3, <<C:256>>, <<D:256>>},
    {Tree, <<Commit:256>>, Opening}.

strip_meta([], D) -> {[], D};
strip_meta([H|T], D) -> 
    {H2, D2} = strip_meta(H, D),
    {T2, D3} = strip_meta(T, D2),
    {[H2|T2], D3};
strip_meta({Key, Value, Meta}, D) -> 
    {{Key, Value}, dict:store(Key, Meta, D)};
strip_meta(T, D) when is_tuple(T) ->
    L = tuple_to_list(T),
    {L2, D2} = strip_meta(L, D),
    T2 = list_to_tuple(L2),
    {T2, D2};
strip_meta(B, D) when is_binary(B) -> {B, D};
strip_meta(I, D) when is_integer(I) -> {I, D}.


points_list(<<E:1024>>) -> [<<E:1024>>];
points_list({I, 0}) when is_integer(I) -> [];
points_list({I, <<E:1024>>}) when is_integer(I) ->
    [<<E:1024>>];
points_list([H|T]) ->% when is_list(H) ->
    points_list(H) ++ points_list(T);
%points_list([_|T]) ->
%    points_list(T);
points_list({I, {_Key, _Value, _Meta}}) 
  when is_integer(I) -> 
    %a leaf.
    [];
points_list(<<_:256>>) -> [];
points_list([]) -> [].
%points_list(_) -> [].

compressed_points_list(X = <<_:256>>) -> 
%    1=2,
    [X];
compressed_points_list({I, X = <<_:256>>}) 
  when is_integer(I) -> 
    %1=2,
    [X];
%ed:compress_points([X]);
compressed_points_list([H|T]) -> 
    compressed_points_list(H) ++
        compressed_points_list(T);
compressed_points_list([]) -> [];
compressed_points_list({_Key, _Value, _Meta}) -> 
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
remove_hashes({Index, X = #leaf{}}) -> 
    {Index, {leaf_verkle:raw_key(X), leaf_verkle:value(X), 
             leaf_verkle:meta(X)}};
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

index2domain2([]) -> [];
index2domain2([H|T]) ->
    [%element(H+1, Domain)|
     H+1|%for domain that is the integers.
     index2domain2(T)].

index2domain(Zs, Domain) ->
    %unused.
    %this is the general version that works for any domain.
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


%we are looking up the elliptic points from the database to incude with the proof. 
points_values([<<Loc:?nindex>>|R], Root, CFG) ->
    % Root is a #stem{}
    Type = stem_verkle:type(Loc+1, Root),
    P = stem_verkle:pointer(Loc+1, Root),
    V = {Loc, Root},
    E = case Type of
        0 -> %empty
                %io:fwrite("point values empty\n"),
                [V, 0];
        1 -> %stem
                %io:fwrite("point values stem\n"),
                S0 = stem_verkle:get(P, CFG),
                S = S0#stem{
                      hashes = tuple_to_list(
                                 S0#stem.hashes)
                     },
                [V|points_values(R, S, CFG)];
                %V;
        2 -> %leaf
                %io:fwrite("point values leaf\n"),
                L = leaf_verkle:get(P, CFG),
                [V, L]
    end,
    E;
points_values([H|T], Root, CFG) ->
    %io:fwrite("point values branching \n"),
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
is_in(_, []) -> false;
is_in(X, [_|T]) -> 
    is_in(X, T).



test(1) ->
    CFG = tree:cfg(tree01),
    A = [1,2,3,4,5],
    B = [3,4,5] ++ A,
    true = same_end(B, A, CFG),
    success.
    

