(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(***********************************************************************
    Proof of Bertrand's conjecture: Binomial.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)
Require Import Arith.
Require Import ArithRing.
Require Import Wf_nat.
Require Export Factorial_bis.
Require Export Summation.
Require Export Power.

(**  	Binomial Coefficient defined using Pascal's triangle *)
Fixpoint binomial (a : nat) : nat -> nat :=
  fun b : nat =>
  match a, b with
  | _, O => 1
  | O, S b' => 0
  | S a', S b' => binomial a' (S b') + binomial a' b'
  end.

(** Basic properties of binomial coefficients *) 
Lemma binomial_def1 : forall n : nat, binomial n 0 = 1.
simple induction n; auto.
Qed.
 
Lemma binomial_def2 : forall n m : nat, n < m -> binomial n m = 0.
simple induction n; simpl in |- *; auto.
intros m; case m; simpl in |- *; auto.
intros H'; inversion H'; auto.
intros n0 H' m; case m; simpl in |- *; auto.
intros H'0; Contradict H'0; auto with arith.
intros n1 H'0; repeat rewrite H'; auto with arith.
Qed.
 
Lemma binomial_def3 : forall n : nat, binomial n n = 1.
simple induction n; intros; simpl in |- *; auto.
rewrite (binomial_def2 n0 (S n0)); auto.
Qed.
 
Lemma binomial_def4 :
 forall n k : nat, binomial (S n) (S k) = binomial n (S k) + binomial n k.
simpl in |- *; auto.
Qed.
 
Lemma binomial_fact :
 forall m n : nat,
 binomial (n + m) n * (factorial n * factorial m) = factorial (n + m).
intros m; elim m; clear m.
intros n; rewrite plus_comm; simpl in |- *; rewrite binomial_def3; ring.
intros m H' n; elim n; clear n.
simpl in |- *; ring.
intros n H'0.
replace (S n + S m) with (S (n + S m)); [ idtac | auto ].
rewrite binomial_def4.
apply
 trans_equal
  with (y := S m * factorial (S n + m) + S n * factorial (n + S m)).
rewrite <- H'0; rewrite <- H'.
replace (S n + m) with (n + S m); simpl in |- *; auto; ring.
replace (n + S m) with (S n + m); simpl in |- *; auto; ring.
Qed.

Theorem binomial_lt : forall n m : nat, 0 < n -> 0 < binomial (n + m) n.
intros n; elim n.
intros m H; inversion H.
intros n1; case n1.
intros H m; elim m; simpl in |- *; auto with arith.
intros n2 Rec m H1.
change (0 < binomial (S n2 + m) (S (S n2)) + binomial (S n2 + m) (S n2))
 in |- *; auto with arith.
apply lt_le_trans with (0 + binomial (S n2 + m) (S n2)); auto with arith.
apply (Rec m); auto with arith.
Qed.
 
Theorem binomial_comp :
 forall n m : nat, binomial (n + m) n = binomial (n + m) m.
intros n m.
apply simpl_mult_r with (n := factorial n); auto with arith.
apply simpl_mult_r with (n := factorial m); auto with arith.
repeat rewrite mult_assoc_reverse.
pattern (n + m) at 2 in |- *; rewrite plus_comm.
pattern (factorial n * factorial m) at 2 in |- *; rewrite mult_comm.
repeat rewrite binomial_fact; auto.
rewrite (plus_comm n); auto.
Qed.

Theorem binomial_mono_S :
 forall n m : nat, 2 * m < n -> binomial n m <= binomial n (S m).
intros n; elim n; simpl in |- *; auto with arith.
intros m; case m; simpl in |- *; auto with arith.
clear n; intros n Rec m; case m; clear m.
case n; simpl in |- *; auto with arith.
intros m; rewrite <- plus_n_O; rewrite <- plus_n_Sm; intros Hm.
case (le_lt_or_eq (S (S (m + m))) n); auto with arith; intros H1.
rewrite (plus_comm (binomial n (S m))).
apply plus_le_compat; auto.
apply le_trans with (binomial n (S m)); auto with arith.
apply Rec; rewrite <- plus_n_O; auto with arith.
apply lt_trans with (S m + m); auto with arith.
apply Rec; rewrite <- plus_n_O; rewrite <- plus_n_Sm; auto with arith.
replace n with (S (S m) + m).
rewrite binomial_comp with (n := S (S m)).
rewrite (plus_comm (binomial (S (S m) + m) (S m))); auto with arith.
Qed.
 
Theorem binomial_mono :
 forall n m p : nat, 2 * m < n -> binomial n (S m - p) <= binomial n (S m).
intros n m p H; elim p; auto.
intros p1 H1; apply le_trans with (2 := H1).
case (le_or_lt p1 m); intros H2.
rewrite <- (minus_Sn_m m p1); simpl in |- *; auto with arith.
apply binomial_mono_S.
apply le_lt_trans with (2 := H); auto with arith.
apply (fun m n p : nat => mult_le_compat_l p n m); apply minus_le; 	 
  auto with arith.
repeat rewrite minus_O; auto with arith.
Qed.


(**  Pascal theorem *)
Theorem exp_Pascal :
 forall a b n : nat,
 power (a + b) n =
 sum_nm 0 n (fun k : nat => binomial n k * (power a (n - k) * power b k)).
simple induction n; auto; clear n.
intros n; case n; clear n.
simpl in |- *; intros; ring.
intros n H'.
apply trans_equal with (y := (a + b) * power (a + b) (S n)).
simpl in |- *; auto.
rewrite H'; rewrite mult_plus_distr_r; repeat rewrite sum_nm_times.
rewrite sum_nm_i; rewrite binomial_def1.
replace (1 * (power a (S n - 0) * power b 0)) with (power a (S n));
 [ idtac | simpl in |- *; ring ]; auto.
rewrite sum_nm_f; rewrite binomial_def3.
replace (S n - (0 + S n)) with 0; [ idtac | simpl in |- *; apply minus_n_n ];
 auto.
replace (power a 0) with 1; auto.
replace (b * (1 * (1 * power b (0 + S n)))) with (b * power b (S n));
 [ idtac | simpl in |- *; ring ]; auto.
rewrite (t_sum_Svars 0 n).
replace
 (a * power a (S n) +
  sum_nm 1 n
    (fun z : nat => a * (binomial (S n) z * (power a (S n - z) * power b z))) +
  (sum_nm 1 n
     (fun x : nat =>
      b *
      (binomial (S n) (pred x) * (power a (S n - pred x) * power b (pred x)))) +
   b * power b (S n))) with
 (power a (S (S n)) +
  (sum_nm 1 n
     (fun x : nat =>
      binomial (S (S n)) x * (power a (S (S n) - x) * power b x)) +
   power b (S (S n)))).
rewrite (sum_nm_i (S n) 0).
rewrite (sum_nm_f 1 n).
rewrite binomial_def1; rewrite binomial_def3.
replace (S (S n) - 0) with (S (S n)); auto.
replace (S (S n) - (1 + S n)) with 0; auto with arith.
replace (power a 0) with 1; auto.
replace (power b 0) with 1; auto.
replace (1 * (power a (S (S n)) * 1)) with (power a (S (S n)));
 [ idtac | simpl in |- *; ring ]; auto.
replace (1 + S n) with (S (S n)); auto.
replace (1 * (1 * power b (S (S n)))) with (power b (S (S n)));
 [ idtac | simpl in |- *; ring ]; auto.
repeat rewrite plus_assoc_reverse; apply f_equal2 with (f := plus); auto.
repeat rewrite plus_assoc; apply f_equal2 with (f := plus); auto.
rewrite sum_nm_add.
apply sum_nm_ext.
intros x H'0.
replace (pred (1 + x)) with x; [ idtac | auto ].
replace (S (S n) - (1 + x)) with (S n - x); [ idtac | auto ].
replace (S n - (1 + x)) with (n - x); [ idtac | auto ].
replace (1 + x) with (S x); [ idtac | auto ].
rewrite (binomial_def4 (S n)); auto with arith.
rewrite <- minus_Sn_m; simpl in |- *; auto; try ring.
Qed.

(** Pascal theorem for a=b=1 *)
Theorem binomial2 :
 forall n : nat, power 2 n = sum_nm 0 n (fun x => binomial n x).
intros n; replace 2 with (1 + 1); auto with arith.
rewrite exp_Pascal.
apply sum_nm_ext.
intros x H; repeat rewrite SO_power || rewrite mult_1_r; auto.
Qed.

(** Upper bound for (binomial 2n+1 n) *)
 
Theorem binomial_odd :
 forall n : nat, binomial (2 * n + 1) (n + 1) <= power 2 (2 * n).
intros n.
case (le_lt_or_eq 0 n); auto with arith; intros H1.
apply mult_S_le_reg_l with (n := 1).
pattern 2 at 3 in |- *; rewrite <- (power_SO 2).
rewrite power_mult.
replace (1 + 2 * n) with (2 * n + 1) by apply plus_comm.
replace (2 * binomial (2 * n + 1) (n + 1)) with
 (binomial (2 * n + 1) n + binomial (2 * n + 1) (n + 1)).
rewrite binomial2.
rewrite sum_nm_split with (r := pred n).
replace (1 + (0 + pred n)) with n; auto with arith.
replace (2 * n + 1 - (1 + pred n)) with (n + 1); auto with arith.
apply
 le_trans with (sum_nm n (n + 1) (fun x : nat => binomial (2 * n + 1) x));
 auto with arith.
rewrite sum_nm_split with (r := 1).
apply le_trans with (sum_nm n 1 (fun x : nat => binomial (2 * n + 1) x));
 auto with arith.
replace (n + 1) with (S n); simpl in |- *; auto; rewrite plus_comm; auto.
replace 1 with (0 + 1); auto with arith.
simpl in |- *; rewrite <- (S_pred n 0); auto with arith.
apply plus_minus; auto with arith; ring.
simpl in |- *; rewrite <- (S_pred n 0); auto with arith.
apply le_lt_trans with n; auto with arith.
pattern n at 1 in |- *; replace n with (n + 0); auto with arith.
replace (2 * n + 1) with (n + (n + 1)); auto with arith.
simpl in |- *; ring.
replace (2 * n + 1) with (n + (n + 1)); auto with arith.
rewrite (binomial_comp n).
simpl in |- *; ring.
simpl in |- *; ring.
rewrite <- H1; simpl in |- *; auto with arith.
Qed.

(** Lower bound for (binomial 2n n) *)

Theorem binomial_even :
 forall n : nat, 0 < n -> power 2 (2 * n) <= 2 * n * binomial (2 * n) n.
intros n Hn.
cut (S (2 * n - 2) = 2 * n - 1);
 [ intros H1
 | generalize Hn; case n; simpl in |- *; auto;
    try (intros H1; inversion H1; fail);
    (intros n1; repeat rewrite <- plus_n_Sm; simpl in |- *;
      rewrite <- minus_n_O) ]; auto.
cut (2 * n - 2 < 2 * n - 1); [ intros H2 | rewrite <- H1; auto with arith ].
cut (S (2 * n - 1) = 2 * n);
 [ intros H3
 | generalize Hn; case n; simpl in |- *; auto;
    try (intros H3; inversion H3; fail); intros n1;
    repeat rewrite <- plus_n_Sm; simpl in |- * ]; auto.
rewrite binomial2.
rewrite sum_nm_split with (r := 0); auto with arith.
repeat rewrite <- plus_n_O.
rewrite sum_nm_split with (p := 1) (r := 2 * n - 2); auto with arith.
replace (1 + (1 + (2 * n - 2))) with (2 * n);
 [ idtac | generalize H1 H3; simpl in |- *; intros H4; rewrite H4; auto ].
replace (2 * n - 1 - (1 + (2 * n - 2))) with 0;
 [ idtac | rewrite <- H1; apply minus_n_n ].
apply le_trans with (1 + (S (2 * n - 2) * binomial (2 * n) n + 1)).
repeat apply plus_le_compat; auto with arith.
case n; simpl in |- *; auto.
rewrite <- sum_nm_c with (c := binomial (2 * n) n) (p := 1).
apply sum_nm_le.
intros x Hx H4.
generalize (S_pred _ _ Hn); intros H5; pattern n at 3 in |- *; rewrite H5.
case (le_or_lt x n); intros H6.
replace x with (S (pred n) - (S (pred n) - x)).
apply binomial_mono.
rewrite H5; auto with arith.
rewrite <- H5; auto with arith.
apply sym_equal; apply plus_minus; auto with arith.
rewrite plus_comm; apply le_plus_minus; auto with arith.
pattern (2 * n) at 1 in |- *; rewrite (le_plus_minus x (2 * n));
 auto with arith.
rewrite binomial_comp with (n := x).
rewrite <- (le_plus_minus x (2 * n)); auto with arith.
replace (2 * n - x) with (S (pred n) - (x - n)).
apply binomial_mono.
rewrite H5; auto with arith.
rewrite <- H5; auto with arith.
apply sym_equal; apply plus_minus; auto with arith.
rewrite <- minus_plus_le.
replace (x + 2 * n) with (n + x + n); auto with arith; ring.
apply lt_le_weak; auto.
apply le_trans with (1 := H4).
pattern (2 * n) at 2; rewrite <- H3; rewrite <- H1; auto with arith.
apply le_trans with (1 := H4).
pattern (2 * n) at 2; rewrite <- H3; rewrite <- H1; auto with arith.
apply le_trans with (1 := H4).
pattern (2 * n) at 2; rewrite <- H3; rewrite <- H1; auto with arith.
simpl in |- *; rewrite binomial_def3; auto with arith.
replace (1 + (S (2 * n - 2) * binomial (2 * n) n + 1)) with
 (2 + S (2 * n - 2) * binomial (2 * n) n); [ idtac | ring ].
rewrite H1.
replace (2 * n * binomial (2 * n) n) with
 (binomial (2 * n) n + (2 * n - 1) * binomial (2 * n) n).
apply plus_le_compat; auto with arith.
generalize Hn; elim n; auto with arith.
intros n1; case n1; auto with arith.
intros n0 H Hn0; replace (2 * S (S n0)) with (S (S (2 * S n0)));
 auto with arith.
2: simpl in |- *; repeat rewrite <- plus_n_Sm; auto.
repeat rewrite binomial_def4; auto with arith.
apply le_plus_trans; rewrite plus_comm; auto with arith.
pattern (2 * n) at 4 in |- *; rewrite <- H3; auto.
Qed.
 
