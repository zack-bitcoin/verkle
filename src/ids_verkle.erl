-module(ids_verkle).
-export([main_id/1, leaf/0, main/0, stem/0, parameters/0]).

leaf() -> verkle_leafs.
stem() -> verkle_stems.
main() -> main_id(ok).
main_id(_ID) -> verkle_main.
parameters() -> verkle_parameters.
