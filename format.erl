-module(format).
-export([endian/1]).

endian([]) -> [];
endian([A,B|T]) -> 
    [B,A|endian(T)].
    
