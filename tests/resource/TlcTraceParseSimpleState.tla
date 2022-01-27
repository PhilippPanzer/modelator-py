/\ one_indexed_sequential_map = <<42, 42, 42, 42, 42>>
/\ string_indexed_map = [two |-> 42, one |-> 42]
/\ record = [foo |-> 42, bar |-> 43]
/\ tuple = <<1, 2>>
/\ bool = FALSE
/\ set = {1, 2, 3}
/\ list = <<1, "two">>
/\ map = ( 0 :> 42 @@
  1 :> 42 @@
  2 :> 42 @@
  3 :> 42 @@
  4 :> 42 @@
  5 :> 42 @@
  6 :> "forty-two" @@
  8 :> "forty-two" @@
  13 :> "forty-two" )
/\ json_int = 123
/\ string_literal = "hello"
/\ zero_indexed_sequential_map = (0 :> 42 @@ 1 :> 42 @@ 2 :> 42 @@ 3 :> 42 @@ 4 :> 42 @@ 5 :> 42)