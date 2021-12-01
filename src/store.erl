-module(store).
-export([store/3, %non-batched store is not needed.
         %restore/5, %is not used.
         %get_branch/5, store_branch/6, %only used to delete. maybe we don't need these.
         batch/3]).
-include("constants.hrl").

%This file seems more complicated than it needs to be, but there is a method to the madness.
%The ram version of dump and the hard drive version have a critical difference.
%For the hard drive version, we use the location on the hard drive as a pointer to the data. In the ram version, each new data has the next higher integer as it's pointer, and we don't reuse integers.
%After some data gets deleted, it becomes difficult or impossible for the hard drive version to predict which integer it will use for a batch until after the batch is written to the hard drive. So that is why in the hard drive version, we write the data one at a time. So we can produce the intermediate pointers.
%For the ram version, writing one at a time is unnecessarily slow. We want to write it all as a single batch, and we can do this, because we can calculate all the pointers beforehand.

    
max_list([X]) -> X;
max_list([A|[B|T]]) ->
    max_list([max(A, B)|T]).
store(Leaf, Root, CFG) ->
    batch([Leaf], Root, CFG).
batch(Leaves, Root, CFG) ->
    %first we should sort the leaves by path. This way if any of the proofs can be combined, they will be adjacent in the list. So we can combine all the proofs by comparing pairs of adjacent proofs.
    Leaves2 = sort_by_path(Leaves, CFG),
    case cfg:mode(CFG) of
	ram ->
	    Top = dump:highest(ids:leaf(CFG)),

            %store leaves
	    {BranchData0, ToStore} = 
                store_batch_helper_ram(
                  Leaves2, CFG, [], 
                  Root, Top, []),
	    leaf:put_batch(ToStore, CFG),

	    BranchData = extra_stem(BranchData0, CFG),
	    BStart = max_list(
		       lists:map(
			 fun(Branch) ->
				 {_,_,_,B,_} = 
                                     Branch,
				 length(B)
			 end, BranchData)),
	    StemTop = dump:highest(ids:stem(CFG)),
{FHash, FLoc, SToStore} = batch2_ram(BStart, BranchData, CFG, StemTop, []),
	        %io:fwrite("store batch ram mode 2\n"),
	    stem:put_batch(SToStore, CFG),%store stems
	        %io:fwrite("store batch ram mode 3\n"),
	    {FHash, FLoc};

	hd ->
	    BranchData0 = store_batch_helper(Leaves2, CFG, [], Root),
	    BranchData = extra_stem(BranchData0, CFG),
    %leaf-pointer, leaf-hash, leaf-path, branch, type
	    BStart = max_list(
		       lists:map(
			 fun(Branch) ->
				 {_, _, _, B, _} = Branch,
				 length(B)
			 end, BranchData)),
	    batch2(BStart, BranchData, CFG)
    end.
extra_stem([], _) -> [];
extra_stem([X], _) -> [X];
extra_stem([A|[B|T]], CFG) ->
    {Pa,Ha,Aa,Ra,Tya} = A,
    {Pb,Hb,Ab,Rb,Tyb} = B,
    LRA = length(Ra),
    LRB = length(Rb),
    S = min(LRA, LRB),
    {Pta, _} = lists:split(S, Aa),
    {Ptb, _} = lists:split(S, Ab),
    Bool = Pta == Ptb,
    if
	Bool -> %add extra stem to the one(s) that have only S stems. recurse to check if they still match.
	    Ra2 = if
		      LRA == S -> empty_stems(1, CFG) ++ Ra;%add extra stem
		      true -> Ra
		  end,
	    Rb2 = if
		      LRB == S -> empty_stems(1, CFG) ++ Rb;%add extra stem
		      true -> Rb
		  end,
	    A2 = {Pa,Ha,Aa,Ra2,Tya},
	    B2 = {Pb,Hb,Ab,Rb2,Tyb},
	    extra_stem([A2|[B2|T]], CFG);
	true -> [A|extra_stem([B|T], CFG)]
    end.
    %{pointer, hash, path, branch, type}
batch2_ram(1, Branches, _CFG, Pointer, T) ->
    
    {_, Hash, _, [Stem], _} = hd(Branches),
        Stem2 = batch3(Stem, 1, Branches),
        H = {Pointer, Stem2},
        %Loc = stem:put(Stem2, CFG),
    {Hash, Pointer, [H|T]};
batch2_ram(N, Branches, CFG, Pointer, T) ->
    %If the first N-1 nibbles of the path are the same, then they should be combined using batch3.
    {NewBranches, Pointer2, T2} = branch2helper_ram(N, Branches, CFG, Pointer, T, []),
    %Store the nth thing in each branch onto the blockchain, update the pointer and hash etc
    batch2_ram(N-1, NewBranches, CFG, Pointer2, T2).

batch2(1, Branches, CFG) ->
    {_, Hash, _, [Stem], _} = hd(Branches),
    Stem2 = batch3(Stem, 1, Branches),
    Loc = stem:put(Stem2, CFG),
    {Hash, Loc};
batch2(N, Branches, CFG) ->
    %If the first N-1 nibbles of the path are the same, then they should be combined using batch3.
    NewBranches = branch2helper(N, Branches, CFG),
    %Store the nth thing in each branch onto the blockchain, update the pointer and hash etc
    batch2(N-1, NewBranches, CFG).
branch2helper(_, [], _) -> [];
branch2helper(N, Branches, CFG) ->
    {_, _, Path, [Stem|ST], _} = hd(Branches),
    if 
	length([Stem|ST]) == N ->
	    {M, _} = lists:split(N-1, Path),
	    {Combine, Rest} = batch4(Branches, M, N, []),
	    Stem2 = batch3(Stem, N, Combine),
	    Loc = stem:put(Stem2, CFG),
	    Hash = stem:hash(Stem2, CFG),
	    [{Loc, Hash, Path, ST, 1}|branch2helper(N, Rest, CFG)];
	length([Stem|ST]) < N ->
	    [hd(Branches)|branch2helper(N, tl(Branches), CFG)]
    end.
batch4([], _, _, Out) -> {lists:reverse(Out), []};
batch4([B|Branches], M, N, Out) ->
    {_, _, Path, _, _} = B,
    {M2, _} = lists:split(N-1, Path),
    case M2 of
	M -> batch4(Branches, M, N, [B|Out]);
	_ -> {lists:reverse(Out), [B|Branches]}
    end.
batch3(Stem, _, []) -> Stem;
batch3(Stem, N, [{Pointer, Hash, Path, _, Type}|T]) ->
    <<A:?nindex>> = lists:nth(N, Path),
    S2 = stem:add(Stem, A, Type, Pointer, Hash),
    batch3(S2, N, T).
    %we will look at pairs at the same time, and delete stuff from the older of the two. That way we still have everything when we move on to the next pair.
    %use stem:add(branch, direction, type, pointer, hash, cfg) to to add a child to a stem. Remember, you cannot know the pointer until the child stem is already added. The root of the trie is the last thing we can calculate.
    %So every time we iterate over the list of branches, some of the branches might combine, until eventually there is only 1 branch left, which is the root branch.

sort_by_path(L, CFG) ->
    lists:sort(
      fun(A, B) ->
              leaf:key(A) < leaf:key(B)
      end, L).

%sort_by_path([], _) -> [];
%sort_by_path([X], _) -> [X];
%sort_by_path([Pivot|List], CFG) ->
%    Key = leaf:path_maker(leaf:key(Pivot), CFG),
%    {Below, Above} = pivot_split(Key, List, [], [], CFG),
%    sort_by_path(Below, CFG) ++ 
%	[Pivot] ++ 
%	sort_by_path(Above, CFG).
%pivot_split(_, [], Below, Above, _) -> {Below, Above};
%pivot_split(PKey, [H|T], Below, Above, CFG) ->
%    Key = leaf:path_maker(leaf:key(H), CFG),
%    B = compare_keys(PKey, Key),
%    {C, D} = case B of
%		 true -> {[H|Below], Above};
%		 false -> {Below, [H|Above]}
%	     end,
%    pivot_split(PKey, T, C, D, CFG).
%compare_keys([<<A:?nindex>>|AT], [<<B:?nindex>>|BT]) ->
%    if
%	A > B -> true;
%	B > A -> false;
%	true -> compare_keys(AT, BT)
%    end.
branch2helper_ram(_, [], _, P, T, B) ->
     {B, P, T};
branch2helper_ram(N, Branches, CFG, P, T, B0) ->
    {_, _, Path, [Stem|ST], _} = hd(Branches),
    if 
        length([Stem|ST]) == N ->
            {M, _} = lists:split(N-1, Path),
            {Combine, Rest} = batch4(Branches, M, N, []),
            Stem2 = batch3(Stem, N, Combine),
             %Loc = stem:put(Stem2, CFG),
            Hash = stem:hash(Stem2),
            B1 = B0 ++ [{P, Hash, Path, ST, 1}],
            branch2helper_ram(N, Rest, CFG, P+1, [{P, Stem2}|T], B1);
        length([Stem|ST]) < N ->
            B1 = B0 ++ [hd(Branches)],
            branch2helper_ram(N, tl(Branches), CFG, P, T, B1)
    end.

store_batch_helper_ram([], _, X, _, _Pointer, L) ->
    
    %io:fwrite("store batch helper ram done\n"),
    {X, L};
store_batch_helper_ram([H|T], CFG, BD, Root, Pointer, L) ->
    %io:fwrite("sbhr 0\n"),
    Path = leaf:path(H, CFG),
    GB = get_branch(Path, 0, Root, [], CFG),
    %io:fwrite("sbhr 1\n"),
    case leaf:value(H) of
       empty ->
	       case GB of
		  {_, _, _} -> store_batch_helper_ram(T, CFG, BD, Root, Pointer, L); %if you are deleting something that doesn't exist, then you don't have to do anything.
		  Branch0 ->
                       X = cfg:hash_size(CFG)*8,
                       %EmptyHash = <<0:X>>,
                       store_batch_helper_ram(T, CFG, [{0, <<0:X>>, Path, Branch0, 0}|BD], Root, Pointer, L)
               end;
       _ ->
	       %NLP = leaf:put(H, CFG),
	       NLH = leaf:hash(H, CFG),
	       {Br, NewPointer, L2} = 
	       case GB of
		      {Leaf2, _LP1, Branch} ->%split leaf, add stem(s)
		      %LP2 = leaf:put(Leaf2, CFG),
		      %need to add 1 or more stems.
		       {A, N2} = path_match(Path, leaf:path(Leaf2, CFG)),
		       [Hp|Tp] = empty_stems(max(1, A-length(Branch)+1), CFG),
		       LH2 = leaf:hash(Leaf2, CFG),
		       H2 = stem:add(Hp, N2, 2, Pointer + 1, LH2),
		       {[H2|Tp]++Branch, Pointer + 2, [{Pointer + 1, Leaf2}|[{Pointer, H}|L]]};
		       AB -> %overwrite
		       {AB, Pointer + 1, [{Pointer, H}|L]}
			   end,
	    store_batch_helper_ram(T, CFG, [{Pointer, NLH, Path, Br, 2}|BD], Root, NewPointer, L2)
    end.
store_batch_helper([], _, X, _) -> X;
store_batch_helper([H|T], CFG, BD, Root) ->
    Path = leaf:path(H, CFG),
    GB = get_branch(Path, 0, Root, [], CFG),
    case leaf:value(H) of
	empty ->
	    case GB of
		{_, _, _} -> 
                    store_batch_helper(
                      T, CFG, BD, Root); %if you are deleting something that doesn't exist, then you don't have to do anything.
		Branch0 ->
		    X = cfg:hash_size(CFG)*8,
		    %EmptyHash = <<0:X>>,
		    store_batch_helper(T, CFG, [{0, <<0:X>>, Path, Branch0, 0}|BD], Root)
	    end;
	_ ->
	    NLP = leaf:put(H, CFG),
	    NLH = leaf:hash(H, CFG),
	    Br = 
                case GB of
                    {Leaf2, _LP1, Branch} ->%split leaf, add stem(s)
                        LP2 = leaf:put(Leaf2, CFG),
						%need to add 1 or more stems.
                        {A, N2} = 
                            path_match(
                              Path, leaf:path(
                                      Leaf2, CFG)),
                        [Hp|Tp] = 
                            empty_stems(
                              max(1, A-length(
                                         Branch)
                                  + 1), CFG),
                        LH2 = leaf:hash(
                                Leaf2, CFG),
                        H2 = stem:add(
                               Hp, N2, 2, 
                               LP2, LH2),
                        [H2|Tp]++Branch;
                    AB -> %overwrite
                        AB
		 end,
	    store_batch_helper(T, CFG, [{NLP, NLH, Path, Br, 2}|BD], Root)
    end.
get_branch(Path, N, Parent, Trail, CFG) ->
    %gather the branch as it currently looks.
    M = N+1,
    <<A:?nindex>> = lists:nth(M, Path), % TODO this could be turned into hd (head)
    R = stem:get(Parent, CFG),
    Pointer = stem:pointer(A+1, R),
    RP = [R|Trail],
    ST = stem:type(A+1, R),
    if
	ST == 0 -> RP;
	Pointer == 0 -> RP;
	ST == 1 -> get_branch(Path, M, Pointer, RP, CFG);
	ST == 2 ->
	    Leaf = leaf:get(Pointer, CFG),
	    case leaf:path(Leaf, CFG) of
		Path -> %overwrite
		    RP;
		_ -> %split leaf, add stem(s)
		    {Leaf, Pointer, RP}
	    end
    end.
path_match(P1, P2) -> path_match(P1, P2, 0).
path_match([<<A:?nindex>> | P1], [<<B:?nindex>> | P2], N) ->
    if
	A == B -> path_match(P1, P2, N+1);
	true -> {N, B}
    end.
empty_stems(0, _) -> [];
empty_stems(N, CFG) -> [stem:new_empty(CFG)|empty_stems(N-1, CFG)].
