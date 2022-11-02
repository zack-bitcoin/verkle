-module(ids_verkle).
-export([main_id/1, leaf/1, main/1, stem/1, bits/1, ram/1, parameters/1]).


leaf(CFG) -> list_to_atom(atom_to_list(cfg_verkle:id(CFG)) ++ "_v_leaf").
stem(CFG) -> list_to_atom(atom_to_list(cfg_verkle:id(CFG)) ++ "_v_stem").
main(CFG) -> main_id(cfg_verkle:id(CFG)).
bits(CFG) -> list_to_atom(atom_to_list(cfg_verkle:id(CFG)) ++ "_v_bits").
main_id(ID) -> list_to_atom(atom_to_list(ID) ++ "_v_main").
ram(CFG) -> list_to_atom(atom_to_list(cfg_verkle:id(CFG)) ++ "_v_ram").
parameters(CFG) -> list_to_atom(atom_to_list(cfg_verkle:id(CFG)) ++ "_v_parameters").
