-module(parameters).
-behaviour(gen_server).
-export([start_link/0,code_change/3,handle_call/3,handle_cast/2,handle_info/2,init/1,terminate/2]).
-export([read/0, div_e/1, div_e/0,
         multi_exp/0, multi_exp/1, multi_exp/2,
         domain/1]).
-include("parameters256.hrl").
%-record(p, {
%          g, h, q, %generator points for ipa.
%          domain, %domain to store polynomials
%          a, %poly:calc_A(domain)
%          da%poly:calc_DA(domain)
%         }).

init(ok) -> 
    P = ?p,
    X = poly:all_div_e_parameters(P),
    S = store:multi_exponent_parameters(8),
    {ok, {P, X, S}}.
start_link() -> gen_server:start_link({local, ?MODULE}, ?MODULE, ok, []).
code_change(_OldVsn, State, _Extra) -> {ok, State}.
terminate(_, _) -> io:format("died!"), ok.
handle_info(_, X) -> {noreply, X}.
handle_cast(_, X) -> {noreply, X}.
handle_call(multi_exp, _From, X = {_, _, S}) -> 
    {reply, S, X};
handle_call({multi_exp, M}, _From, 
            X = {_, _, S}) -> 
    Y = element(M, S),
    {reply, Y, X};
handle_call({multi_exp, M, N}, _From, 
            X = {_, _, S}) -> 
    Y = element(M, S),
    Z = element(N, Y),
    {reply, Z, X};
handle_call(div_e, _From, X = {_, D, _}) -> 
    {reply, D, X};
handle_call({div_e, M}, _From, X = {_, D, _}) -> 
    Y = element(M, D),
    {reply, Y, X};
handle_call(read, _From, X = {P, _, _}) -> 
    {reply, P, X};
handle_call(_, _From, X) -> {reply, X, X}.

read() ->
    gen_server:call(?MODULE, read).
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

get_fr(X) ->
    <<Y:256>> = hash:doit(<<X:256>>),
    Y rem fr:prime().
   
domain(Many) -> 
    lists:map(fun(X) -> fr:encode(X) end,
              range(1, Many)).

make_ghq() ->
    ipa:basis(256).

unused_make_ghq() ->
    %p{g, h, q, domain, a, da}
    Many = 256,
    %Many = 4,
    R = range(1, Many),
    G = lists:map(fun(X) ->
                          io:fwrite(integer_to_list(X)),
                          io:fwrite("\n"),
                          Y = get_fr(X),
                          %fq:gen_point(Y)
                          ed:gen_point(Y)
                  end, R),
    H = lists:map(fun(X) ->
                          io:fwrite(integer_to_list(X)),
                          io:fwrite("\n"),
                          Y = get_fr(X + Many),
                          %fq:gen_point(Y)
                          ed:gen_point(Y)
                  end, R),
    QN = get_fr(513),
    %Q = fq:gen_point(QN),
    Q = ed:gen_point(QN),
    {G, H, Q}.

