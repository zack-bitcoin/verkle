-module(ids_verkle).
-export([main_id/1, leaf/1, main/1, stem/1, bits/1, ram/1, parameters/1]).


leaf(CFG) -> list_to_atom(atom_to_list(cfg_verkle:id(CFG)) ++ "_leaf").
stem(CFG) -> list_to_atom(atom_to_list(cfg_verkle:id(CFG)) ++ "_stem").
main(CFG) -> main_id(cfg_verkle:id(CFG)).
bits(CFG) -> list_to_atom(atom_to_list(cfg_verkle:id(CFG)) ++ "_bits").
main_id(ID) -> list_to_atom(atom_to_list(ID) ++ "_main").
ram(CFG) -> list_to_atom(atom_to_list(cfg_verkle:id(CFG)) ++ "_ram").
parameters(CFG) -> list_to_atom(atom_to_list(cfg_verkle:id(CFG)) ++ "_parameters").
