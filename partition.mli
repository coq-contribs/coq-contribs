type __ = Obj.t

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

val pred : nat -> nat

val plus : nat -> nat -> nat

val mult : nat -> nat -> nat

val minus : nat -> nat -> nat

val div2 : nat -> nat

val lt_wf_rec : nat -> (nat -> (nat -> __ -> 'a1) -> 'a1) -> 'a1

val max_such : (nat -> sumbool) -> nat -> nat

val ominus : nat -> nat -> nat option

val pdiv_aux : nat -> nat -> nat -> (nat, nat) prod

val pdiv : nat -> nat -> (nat, nat) prod

val divides1_dec : nat -> nat -> sumbool

val max_div : nat -> nat

val primeb : nat -> bool

type 'a list =
  | Nil
  | Cons of 'a * 'a list

val le_lt_dec : nat -> nat -> sumbool

val bertrand_fun_aux : nat -> nat -> nat

val bertrand_fun : nat -> nat sig0

val partition : nat -> (nat -> nat) sig0

val make_partition_aux : (nat -> nat) -> nat -> (nat, nat) prod list

val make_partition : nat -> (nat, nat) prod list

