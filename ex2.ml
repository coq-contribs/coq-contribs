
(*==========================================================*)
(*           Auxillary Functions                            *)
(*==========================================================*)

let rec  p2n = function 
  O -> 0
|(S n) -> (p2n n)+1

let rec  n2p n = if n=0 then O else S (n2p (n-1))

let part n = 
  let rec map = function
    Nil -> []
  | Cons(Pair (a,b),l) -> (p2n a, p2n b):: (map l) in
     map (make_partition (n2p n))

(*==========================================================*)
(*           Example: partition from 1...20                 *)
(*==========================================================*)

let _ = part 10
