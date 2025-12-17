-module(cfg_verkle).
-compile(export_all).
-export_type([cfg/0,path/0,value/0,id/0,meta/0,hash_size/0]).
-record(cfg, { path
	     , value
	     , id
	     , meta
	     , hash_size
	     , mode
	     , empty_root
             , parameters
	     }).
-opaque cfg() :: #cfg{}.
-type path() :: pos_integer().
-type value() :: non_neg_integer().
-type id() :: atom().
-type meta() :: non_neg_integer().
-type hash_size() :: pos_integer().
empty(X) when is_record(X, cfg) -> 
    X#cfg.empty_root.
set_empty(X, E) -> X#cfg{empty_root = E}.
new(P, V, ID, M, H, X) -> 
    #cfg{path = P, value = V, 
         id = ID, meta = M,
         hash_size = H , mode = X}.
path(X) -> X#cfg.path. %how many bytes to store the path (defaul is 5)
mode(X) -> X#cfg.mode.
value(X) -> X#cfg.value.%how many bytes to store the value.
meta(X) -> X#cfg.meta. %how many bytes to store the meta data that isn't hashed into the merkle tree.
leaf(X) -> path(X) + value(X) + meta(X).
id(X) -> X#cfg.id.
hash_size(X) -> X#cfg.hash_size.
