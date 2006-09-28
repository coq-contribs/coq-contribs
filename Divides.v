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
    Proof of Bertrand's conjecture: Divides.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)

Require Import Arith.
Require Import ArithRing.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Wf_nat.
Require Export Misc.
Require Export Euclid.
Require Export Power.
(** Division as a predicate *)
 
Definition is_div (a b q r : nat) : Prop := r < b /\ a = q * b + r.
 
Definition ex_div (a b : nat) : Prop :=
  exists q : nat, (exists r : nat, is_div a b q r).
 
Lemma div_x_nO : forall x y q r : nat, is_div x y q r -> y <> 0.
intros x y q r; case y; auto.
intros (H1, H2); Contradict H1; auto with arith.
Qed.
 
Lemma div_x_O_r : forall x q r : nat, is_div 0 x q r -> r = 0.
intros x q r (H1, H2).
apply plus_eqO with (y := q * x); rewrite H2; auto with arith.
Qed.
 
Lemma div_x_O_q : forall x q r : nat, is_div 0 x q r -> q = 0.
intros x q r H'.
rewrite (div_x_O_r x q r) in H'; auto; case H'; intros H1 H2.
case (mult_eqO q x); auto.
rewrite H2; auto with arith.
intros H'1; Contradict H1; auto; rewrite H'1; auto with arith.
Qed.
 
Lemma div_pred :
 forall x y q : nat,
 0 < x -> is_div x y q 0 -> is_div (pred x) y (pred q) (pred y).
intros x y q H' (H'1, H'2); split; auto.
generalize H'1; case y; simpl in |- *; auto with arith.
rewrite H'2; auto.
rewrite <- plus_n_O; auto.
generalize H'2; case q; simpl in |- *; auto.
intros H'3; Contradict H'; auto with arith.
rewrite H'3; auto with arith.
intros n H'3; generalize H'1; case y; simpl in |- *; auto with arith.
intros H'4; Contradict H'4; auto with arith.
Qed.
 
Lemma div_SxS :
 forall x y q r : nat,
 0 < r -> is_div x y q r -> is_div (pred x) y q (pred r).
intros x y q r H' (H'1, H'2); split; auto.
apply le_lt_trans with (2 := H'1); auto with arith.
rewrite H'2; generalize H'; case r; simpl in |- *; auto.
intros H'3; Contradict H'3; auto with arith.
intros r'; rewrite <- plus_n_Sm; auto.
Qed.
 
Lemma div_unic_q :
 forall a b q1 q2 r1 r2 : nat,
 is_div a b q1 r1 -> is_div a b q2 r2 -> q1 = q2.
intros a b q1 q2 r1 r2 (H0, H1) (H2, H3).
case (le_or_lt q1 q2); intros H4.
case (le_lt_or_eq _ _ H4); auto; clear H4; intros H4.
Contradict H0; auto; apply le_not_lt.
apply (fun p n m : nat => plus_le_reg_l n m p) with (q1 * b).
rewrite <- H1; rewrite H3; auto with arith.
apply le_trans with (q2 * b + 0); auto with arith.
replace (q1 * b + b) with (S q1 * b);
 [ repeat rewrite (fun x => mult_comm x b) | simpl in |- * ]; 
 auto with arith.
Contradict H2; auto; apply le_not_lt.
apply (fun p n m : nat => plus_le_reg_l n m p) with (q2 * b).
rewrite <- H3; rewrite H1; auto with arith.
apply le_trans with (q1 * b + 0); auto with arith.
replace (q2 * b + b) with (S q2 * b);
 [ repeat rewrite (fun x => mult_comm x b) | simpl in |- * ]; 
 auto with arith.
Qed.
 
Lemma div_unic_r :
 forall a b q1 q2 r1 r2 : nat,
 is_div a b q1 r1 -> is_div a b q2 r2 -> r1 = r2.
intros a b q1 q2 r1 r2 (H0, H1) (H2, H3).
apply plus_reg_l with (q1 * b).
rewrite <- H1; rewrite H3; rewrite (div_unic_q a b q1 q2 r1 r2); try split;
 auto with arith.
Qed.
 
Lemma quot_eq :
 forall a b c q1 r1 q2 r2 : nat,
 a = b -> is_div a c q1 r1 -> is_div b c q2 r2 -> q1 = q2.
intros a b c q1 r1 q2 r2 H H0 H1; apply div_unic_q with (1 := H0) (r2 := r2).
rewrite H; auto.
Qed.
 
Lemma mult_div_r : forall x y q r : nat, is_div (x * y) y q r -> r = 0.
intros x y q r (H1, H2).
apply div_unic_r with (a := x * y) (b := y) (q1 := q) (q2 := x); split;
 auto with arith.
apply le_lt_trans with (m := r); auto with arith.
Qed.
 
Lemma mult_div_q : forall x y q r : nat, is_div (x * y) y q r -> q = x.
intros x y q r (H1, H2).
apply div_unic_q with (a := x * y) (b := y) (r1 := r) (r2 := 0); split; auto.
apply le_lt_trans with (m := r); auto with arith.
Qed.
 
Lemma diveucl_divex :
 forall a b : nat,
 diveucl a b -> exists q : _, (exists r : _, is_div a b q r).
intros a b H; case H.
intros q r H' H'0; exists q; exists r; split; auto.
Qed.
 
Lemma div_ex :
 forall a b : nat, b <> 0 -> exists q : _, (exists r : _, is_div a b q r).
intros a b H; apply diveucl_divex.
apply eucl_dev.
generalize H; case b; auto with arith.
Qed.
(*****************************************************************************
  * Divides 
  * * b divides a -> [(divides a b)] *)
 
Definition divides (a b : nat) : Prop := exists q : nat, b = q * a.
 
Lemma div_ref : forall a : nat, divides a a.
intros a; exists 1; auto with arith.
Qed.
 
Lemma div_divides :
 forall x y : nat, (exists q : _, is_div x y q 0) -> divides y x.
intros x y (q, (H1, H2)); exists q; rewrite H2; auto with arith.
Qed.
 
Lemma divides_div :
 forall x y : nat, 0 < y -> divides y x -> exists q : _, is_div x y q 0.
intros x y H'1 (q, H'2); exists q; split; try rewrite H'2; auto with arith.
Qed.
 
Lemma divides_dec' :
 forall x y : nat,
 {(exists q : _, is_div x y q 0)} + {~ (exists q : _, is_div x y q 0)}.
intros x y; case y; auto.
right; red in |- *; intros (q, (H1, H2)); Contradict H1; auto with arith.
intros y'; case (eucl_dev (S y') (gt_Sn_O y') x).
intros q r; case r; auto.
intros H' H'0; left; exists q; split; try rewrite H'0; auto with arith.
intros n H' H'0; right; red in |- *; intros (q1, (H1, H2)); absurd (0 = S n);
 auto with arith.
apply div_unic_r with (a := x) (b := S y') (q1 := q1) (q2 := q); split;
 auto with arith.
Qed.
 
Lemma divides_dec : forall x y : nat, {divides x y} + {~ divides x y}.
intros x y; case x; case y; auto.
left; exists 0; auto.
intros n; right; red in |- *; intros (q, H').
rewrite (mult_comm q 0) in H'; discriminate.
intros n; left; exists 0; auto.
intros x' y'; case (divides_dec' (S x') (S y')); auto.
intros H'; left; apply div_divides; auto.
intros H'; right; red in |- *; intros (q1, H1); case H'; auto.
exists q1; split; try rewrite H1; auto with arith.
Qed.
 
Lemma all_divides_O : forall n : nat, divides n 0.
intros n; exists 0; auto.
Qed.
 
Lemma SO_divides_all : forall n : nat, divides 1 n.
intros n; exists n; auto with arith.
Qed.
 
Lemma divides_plus1 :
 forall a b c : nat, divides a b -> divides a c -> divides a (b + c).
intros a b c (q1, H1) (q2, H2); exists (q1 + q2); rewrite H1; rewrite H2;
 auto with arith.
Qed.
 
Lemma divides_plus2 :
 forall a b c : nat, divides a b -> divides a (b + c) -> divides a c.
intros a b c (q1, H1) (q2, H2); exists (q2 - q1).
rewrite mult_minus_distr_r.
rewrite <- H1; rewrite <- H2.
rewrite minus_plus; auto.
Qed.
 
Theorem divides_le : forall a b : nat, b <> 0 -> divides a b -> a <= b.
intros a b; case b.
intros H'; case H'; auto.
intros n H (q1, H1).
generalize H; rewrite H1; case q1; simpl in |- *; auto with arith.
intros H2; case H2; auto.
Qed.
 
Lemma divides_antisym : forall a b : nat, divides a b -> divides b a -> a = b.
intros a b; case a; case b; auto.
intros b' (q1, H1) H2; rewrite H1; auto with arith.
intros a' H1 (q2, H2); rewrite H2; auto with arith.
intros b' a' H' H'0; apply le_antisym; apply divides_le; auto.
Qed.
 
Lemma not_lt_div : forall a b : nat, 0 < b -> b < a -> ~ divides a b.
intros a b H'1 H'2; red in |- *; intros H'3; Contradict H'2; auto with arith.
apply le_not_lt; apply divides_le; auto.
apply sym_not_eq; auto with arith.
Qed.
 
Theorem divides_mult :
 forall a b c d : nat, divides a c -> divides b d -> divides (a * b) (c * d).
intros a b c d (q1, H) (q2, H0); exists (q1 * q2); rewrite H; rewrite H0;
 ring.
Qed.
 
Theorem divides_mult1 :
 forall a b c : nat, divides a b -> divides (c * a) (c * b).
intros a b c (r, H); exists r; rewrite H; ring.
Qed.
 
Theorem divides_mult2 :
 forall a b c : nat, 0 < c -> divides (c * a) (c * b) -> divides a b.
intros a b c H (r, H1); exists r.
apply eq_mult with c; auto with arith.
apply sym_not_eq; apply lt_O_neq; auto.
rewrite H1; ring.
Qed.
 
Theorem divides_trans :
 forall a b c : nat, divides a b -> divides b c -> divides a c.
intros a b c (q1, H1) (q2, H2); exists (q1 * q2); rewrite H2; rewrite H1;
 ring.
Qed.
 
Theorem divides_power :
 forall a b c : nat, a <= b -> divides (power c a) (power c b).
intros a b c; exists (power c (b - a)).
rewrite power_mult.
rewrite plus_comm; rewrite <- le_plus_minus; auto with arith.
Qed.
Hint Resolve divides_power: arith.
