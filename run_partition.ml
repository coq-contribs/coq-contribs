(*===============================================================*)
(*          Extracted code                                       *)
(*===============================================================*)
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type bool =
  | True
  | False

type nat =
  | O
  | S of nat

type 'a option =
  | Some of 'a
  | None

type ('a, 'b) prod =
  | Pair of 'a * 'b

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
  | Left
  | Right

(** val pred : nat -> nat **)

let pred = function
  | O -> O
  | S u -> u

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
    | O -> m
    | S p -> S (plus p m)

(** val mult : nat -> nat -> nat **)

let rec mult n m =
  match n with
    | O -> O
    | S p -> plus m (mult p m)

(** val minus : nat -> nat -> nat **)

let rec minus n m =
  match n with
    | O -> O
    | S k -> (match m with
                | O -> S k
                | S l -> minus k l)

(** val div2 : nat -> nat **)

let rec div2 = function
  | O -> O
  | S n0 -> (match n0 with
               | O -> O
               | S n' -> S (div2 n'))

(** val lt_wf_rec : nat -> (nat -> (nat -> __ -> 'a1) -> 'a1) -> 'a1 **)

let rec lt_wf_rec p f =
  f p (fun y _ -> lt_wf_rec y f)

(** val max_such : (nat -> sumbool) -> nat -> nat **)

let rec max_such p_dec n =
  match p_dec n with
    | Left -> n
    | Right -> (match n with
                  | O -> O
                  | S n1 -> max_such p_dec n1)

(** val ominus : nat -> nat -> nat option **)

let rec ominus m n =
  match m with
    | O -> (match n with
              | O -> Some m
              | S n0 -> None)
    | S m1 -> (match n with
                 | O -> Some m
                 | S n1 -> ominus m1 n1)

(** val pdiv_aux : nat -> nat -> nat -> (nat, nat) prod **)

let rec pdiv_aux m n p =
  match ominus m n with
    | Some m1 ->
        (match p with
           | O -> Pair (m, n)
           | S p1 -> let Pair (q, r) = pdiv_aux m1 n p1 in Pair ((S q), r))
    | None -> Pair (O, m)

(** val pdiv : nat -> nat -> (nat, nat) prod **)

let pdiv m n =
  pdiv_aux m n m

(** val divides1_dec : nat -> nat -> sumbool **)

let divides1_dec n m =
  match n with
    | O -> (match m with
              | O -> Left
              | S n1 -> Right)
    | S n1 ->
        let Pair (p, q) = pdiv m (S n1) in
        (match q with
           | O -> Left
           | S q1 -> Right)

(** val max_div : nat -> nat **)

let max_div n = match n with
  | O -> S O
  | S n0 ->
      (match n0 with
         | O -> S O
         | S n1 -> max_such (fun x -> divides1_dec x n) (S n1))

(** val primeb : nat -> bool **)

let primeb n = match n with
  | O -> False
  | S n0 ->
      (match n0 with
         | O -> False
         | S n1 ->
             (match max_div n with
                | O -> False
                | S n2 -> (match n2 with
                             | O -> True
                             | S n3 -> False)))

type 'a list =
  | Nil
  | Cons of 'a * 'a list

(** val le_lt_dec : nat -> nat -> sumbool **)

let rec le_lt_dec n m =
  match n with
    | O -> Left
    | S n1 -> (match m with
                 | O -> Right
                 | S m1 -> le_lt_dec n1 m1)

(** val bertrand_fun_aux : nat -> nat -> nat **)

let rec bertrand_fun_aux n m =
  match primeb n with
    | True -> n
    | False -> (match m with
                  | O -> O
                  | S m1 -> bertrand_fun_aux (S n) m1)

(** val bertrand_fun : nat -> nat sig0 **)

let bertrand_fun n =
  bertrand_fun_aux (S n) (pred (pred n))

(** val partition : nat -> (nat -> nat) sig0 **)

let partition n =
  lt_wf_rec n (fun n0 h ->
    match n0 with
      | O -> (fun x -> x)
      | S n1 ->
          let p = bertrand_fun (mult (S (S O)) (S n1)) in
          (fun x ->
          match le_lt_dec x (mult (S (S O)) (S n1)) with
            | Left ->
                (match le_lt_dec (minus p (mult (S (S O)) (S n1))) x with
                   | Left -> minus p x
                   | Right ->
                       h (div2 (pred (minus p (mult (S (S O)) (S n1))))) __ x)
            | Right -> O))

(** val make_partition_aux : (nat -> nat) -> nat -> (nat, nat) prod list **)

let rec make_partition_aux f n = match n with
  | O -> Nil
  | S n1 ->
      (match le_lt_dec (f n) n with
         | Left -> make_partition_aux f n1
         | Right -> Cons ((Pair (n, (f n))), (make_partition_aux f n1)))

(** val make_partition : nat -> (nat, nat) prod list **)

let make_partition n =
  make_partition_aux (partition n) (mult (S (S O)) n)


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
