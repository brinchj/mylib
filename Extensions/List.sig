signature List =
sig
  include LIST

  val sort : ('a -> 'a -> order) -> 'a list -> 'a list
  val shuffle : 'a list -> 'a list
  val leftmost  : 'a option list -> 'a option
  val rightmost : 'a option list -> 'a option
  val allPairs : 'a list -> 'b list -> ('a * 'b) list
  val splitAt : 'a list * int -> 'a list * 'a list
  val allSplits : 'a list -> ('a list * 'a list) list
  val consAll : 'a * 'a list list -> 'a list list
  val concatMap : ('a -> 'b list) -> 'a list -> 'b list
end