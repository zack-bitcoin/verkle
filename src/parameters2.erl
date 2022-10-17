-module(parameters2).
-behaviour(gen_server).
-export([start_link/0,code_change/3,handle_call/3,handle_cast/2,handle_info/2,init/1,terminate/2]).
-export([read/0, div_e/1, div_e/0,
         multi_exp/0, multi_exp/1, multi_exp/2,
         domain/0, a/0, da/0,
         det_point/1]).


read_or_gen(File, Fun) ->
    case file:read_file(File) of
        {error, _} ->
            X = Fun(),
            file:write_file(
              File, term_to_binary(X)),
            X;
        {ok, Y} ->
            binary_to_term(Y)
    end.
   
-record(db, {
          g, h, q,%elliptic curve generator points for pedersen commitments
          a,%polynomial A(X) from this paper: https://dankradfeist.de/ethereum/2021/06/18/pcs-multiproofs.html
          da,%polynomial A'(X) from the same paper.
          domain,%domain over which we store values in the polynomial.
          dive,%precompute to make poly:div_e faster.
          me%precompute so that pedersen commits using g/h are faster. these are the commitments connecting stems of the verkle tree.
         }).


init(ok) -> 
    io:fwrite("parameters2 initiating\n"),
    Many = 256,
    {G, H, Q} = 
        read_or_gen(
          "precomputes/GHQ.db", 
          fun() -> make_ghq() end),
    Domain = calc_domain(Many),
    A = read_or_gen(
          "precomputes/A.db",
          fun() -> poly:calc_A(Domain) end),
    DA = read_or_gen(
          "precomputes/DA.db",
          fun() -> poly:c2e(
                     poly:calc_DA(Domain), 
                     Domain) 
          end),
    DivE = 
        read_or_gen(
          "precomputes/DivE.db",
          fun() -> poly:all_div_e_parameters(
                     Domain, DA) 
          end),

    %C is the config factor for the bucket algorithm. Higher means a bigger precompute, lower means more elliptic curve additions when operating over the verkle tree.
    C = 8,
    G2 = ed:affine2extended(G),
    ME = read_or_gen(
          "precomputes/ME.db",
          fun() -> precomputed_multi_exponent:parameters(C, G2) end),
    DB = #db{g = G2, h = H, q = Q, a = A, da = DA, 
             domain = Domain, dive = DivE, 
             me = ME},
    {ok, DB}.
start_link() -> gen_server:start_link({local, ?MODULE}, ?MODULE, ok, []).
code_change(_OldVsn, State, _Extra) -> {ok, State}.
terminate(_, _) -> io:format("died!"), ok.
handle_info(_, X) -> {noreply, X}.
handle_cast(_, X) -> {noreply, X}.
handle_call(multi_exp, _From, DB) -> 
    {reply, DB#db.me, DB};
handle_call({multi_exp, M}, _From, DB) -> 
    ME = DB#db.me,
    Y = element(M, ME),
    {reply, Y, DB};
handle_call({multi_exp, M, N}, _From, DB) ->
    Y = element(M, DB#db.me),
    Z = element(N, Y),
    {reply, Z, DB};
handle_call(div_e, _From, DB) -> 
    {reply, DB#db.dive, DB};
handle_call({div_e, M}, _From, DB) -> 
    Y = element(M, DB#db.dive),
    {reply, Y, DB};
handle_call(ghq, _From, 
            DB = #db{g = G, h = H, q = Q}
           ) -> 
    {reply, {G, H, Q}, DB};
handle_call(domain, _From, 
            DB = #db{domain = D}
           ) -> 
    {reply, D, DB};
handle_call(da, _From, 
            DB = #db{da = D}
           ) -> 
    {reply, D, DB};
handle_call(a, _From, 
            DB = #db{a = D}
           ) -> 
    {reply, D, DB};
handle_call(_, _From, X) -> {reply, X, X}.

a() ->
    gen_server:call(?MODULE, a).
da() ->
    gen_server:call(?MODULE, da).
domain() ->
    gen_server:call(?MODULE, domain).
read() ->
    gen_server:call(?MODULE, ghq).
div_e(M) ->
    gen_server:call(?MODULE, {div_e, M}).
div_e() ->
    gen_server:call(?MODULE, div_e).
multi_exp() ->
    gen_server:call(?MODULE, multi_exp).
multi_exp(G) ->
    gen_server:call(?MODULE, {multi_exp, G}).
multi_exp(G, R) ->
    gen_server:call(?MODULE, {multi_exp, G, R}).

range(X, X) -> [X];
range(X, Y) when X < Y -> 
    [X|range(X+1, Y)].

det_point(X) ->
    %deterministicly generated point.
    <<Y:256>> = hash:doit(<<X:256>>),
    %Z = Y rem fr:prime(),
    ed:gen_point(<<Y:256>>).
%    Z = Y rem fr:prime(),
%    fq:extended2extended_niels(
%      fq:gen_point(Z)).
   
calc_domain(Many) -> 
    lists:map(fun(X) -> fr:encode(X) end,
              range(1, Many)).
              %range(0, Many-1)).
    

make_ghq() ->
    ipa:basis(256).

make_ghq_old() ->
    %p{g, h, q, domain, a, da}
    Many = 256,
    %Many = 4,
    R = range(1, Many),
    io:fwrite("generating 256 G generator points\n"),
    G = lists:map(fun(X) ->
                          io:fwrite(integer_to_list(X)),
                          io:fwrite("\n"),
                          det_point(X)
                  end, R),
    io:fwrite("generating 256 H generator points\n"),
    H = lists:map(fun(X) ->
                          io:fwrite(integer_to_list(X)),
                          io:fwrite("\n"),
                          det_point(X+256)
                  end, R),
    io:fwrite("generating Q generator point"),
    Q = det_point(513),
    {G, H, Q}.
