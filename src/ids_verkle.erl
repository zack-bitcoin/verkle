-module(ids_verkle).
-export([main_id/1, leaf/1, main/1, stem/1, parameters/1]).

leaf(ID) -> 
    list_to_atom(atom_to_list(ID) ++ "_verkle_leafs").
stem(ID) -> 
    list_to_atom(atom_to_list(ID) ++ "_verkle_stems").
main(ID) -> main_id(ID).
main_id(ID) -> 
    list_to_atom(atom_to_list(ID) ++ "_verkle_main").
parameters(ID) ->
    list_to_atom(atom_to_list(ID) ++ "_verkle_parameters").
