(***********************************************************************
    Proof of Bertrand's conjecture: Factorial.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)

Require Import Arith.

(**  	Factorial*)
 
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * factorial n'
  end.

Theorem lt_factorial_O : forall n : nat, 0 < factorial n.
intros n; elim n; simpl in |- *; auto with arith.
Qed.
Hint Resolve lt_factorial_O: arith.