module Utils

%default total

public export
error : String -> a
error x = assert_total (idris_crash x)
