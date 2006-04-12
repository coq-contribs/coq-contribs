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
    Proof of Bertrand's conjecture: PowerDiv.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)
Require Export Div.
Require Import ArithRing.
Require Export Gcd.
Require Export Factorial_bis.
Require Export DivDirac.
Require Export Summation.

(** Auxillary function that tries to find the maximal exponent of q that
   divides p*)
 
Fixpoint power_div_aux (p q n : nat) {struct n} : nat :=
  match pdiv p q with
  | (p1, O) => match n with
               | O => 0
               | S n1 => S (power_div_aux p1 q n1)
               end
  | (p1, _) => 0
  end.
 
Theorem power_div_aux_def :
 forall p q n : nat,
 0 < p ->
 1 < q ->
 p < power q n ->
 divides (power q (power_div_aux p q n)) p /\
 ~ divides (power q (1 + power_div_aux p q n)) p.
intros p q n; generalize p q; clear p q; elim n.
intros p q H H0 H1; Contradict H1; auto with arith.
intros n1 Rec p q H1 H2 H3.
unfold power_div_aux in |- *.
generalize (pdiv_def p q); case (pdiv p q); fold power_div_aux in |- *.
intros q1 r1; case r1.
intros H4; case H4.
apply lt_trans with (2 := H2); auto with arith.
rewrite <- plus_n_O; intros H5 H6; rewrite H5.
case (Rec q1 q); auto with arith.
apply lt_mult_right_anti with q; auto with arith.
repeat rewrite (mult_comm q); simpl in |- *; rewrite <- H5; auto.
apply lt_mult_right_anti with q; auto with arith.
replace (q * q1) with p; auto with arith.
repeat rewrite (mult_comm q); auto.
simpl in |- *; repeat rewrite (mult_comm q1).
intros H7 H8; split.
apply divides_mult1; auto.
red in |- *; intros H9; case H8; apply divides_mult2 with (2 := H9); auto.
intros r2 H4; case H4; simpl in |- *.
apply lt_trans with (2 := H2); auto with arith.
intros H5 H6; split.
apply SO_divides_all.
red in |- *; intros (q2, H7); absurd (S r2 = 0); auto with arith.
apply (div_unic_r p q q1 q2); split; auto.
apply lt_trans with (2 := H2); auto with arith.
rewrite H7; ring.
Qed.

(** Power_div: 
 (power_div p q): find the maximal power of q that divides p *)

Definition power_div (p q : nat) := power_div_aux p q p.
 
Theorem power_div_id : forall n : nat, 0 < n -> power_div n n = 1.
intros n; case n; unfold power_div in |- *; simpl in |- *; auto with arith.
intros n1; unfold pdiv in |- *; simpl in |- *.
rewrite ominus_id; case n1; simpl in |- *; auto with arith.
Qed.
 
Theorem power_div_divides :
 forall p q : nat, 0 < p -> 1 < q -> divides (power q (power_div p q)) p.
intros p q H1 H2; case (power_div_aux_def p q p); auto with arith.
apply power_id_lt; auto.
Qed.
 
Theorem power_div_not_divides :
 forall p q : nat,
 0 < p -> 1 < q -> ~ divides (power q (1 + power_div p q)) p.
intros p q H1 H2; case (power_div_aux_def p q p); auto with arith.
apply power_id_lt; auto.
Qed.
 
Theorem power_div_inv :
 forall p q r : nat,
 0 < p ->
 1 < q ->
 divides (power q r) p -> ~ divides (power q (1 + r)) p -> r = power_div p q.
intros p q r H H0 H1 H2.
case (le_or_lt r (power_div p q)); intros H3.
case (le_lt_or_eq _ _ H3); intros H4; auto.
case H2.
apply divides_trans with (power q (power_div p q)).
exists (power q (power_div p q - (1 + r))).
rewrite power_mult.
rewrite plus_comm; rewrite <- le_plus_minus; auto with arith.
apply power_div_divides; auto.
absurd (divides (power q (1 + power_div p q)) p).
apply power_div_not_divides; auto.
apply divides_trans with (2 := H1).
exists (power q (r - (1 + power_div p q))).
rewrite power_mult.
rewrite plus_comm; rewrite <- le_plus_minus; auto with arith.
Qed.
 
Theorem power_div_mult_prime :
 forall p q r : nat,
 0 < q ->
 0 < r -> prime p -> power_div (q * r) p = power_div q p + power_div r p.
intros p q r Hq Hr H; cut (1 < p); [ intros Hp | apply lt_prime; auto ].
apply sym_equal; apply power_div_inv; auto with arith.
rewrite <- power_mult; apply divides_mult.
apply power_div_divides; auto with arith.
apply power_div_divides; auto with arith.
red in |- *; intros (q1, H0);
 case
  (L_Euclides2 p (div q (power p (power_div q p)))
     (div r (power p (power_div r p)))); auto.
exists q1.
apply eq_mult with (power p (power_div q p + power_div r p)).
apply sym_not_eq; apply lt_O_neq.
rewrite <- power_mult; apply lt_O_mult; auto with arith.
apply power_lt_O; apply lt_trans with 1; auto with arith.
apply power_lt_O; apply lt_trans with 1; auto with arith.
replace (power p (power_div q p + power_div r p) * (q1 * p)) with (q * r).
rewrite <- power_mult; auto with arith.
apply sym_equal; pattern q at 1 in |- *;
 rewrite (divides_div (power p (power_div q p)) q); 
 auto with arith.
pattern r at 1 in |- *; rewrite (divides_div (power p (power_div r p)) r).
ring.
apply power_lt_O; apply lt_trans with 1; auto with arith.
apply power_div_divides; auto with arith.
apply power_lt_O; apply lt_trans with 1; auto with arith.
apply power_div_divides; auto with arith.
rewrite H0; simpl in |- *; ring.
intros (q2, H2); case (power_div_not_divides q p); auto with arith.
exists q2.
pattern q at 1 in |- *; rewrite (divides_div (power p (power_div q p)) q);
 auto with arith.
rewrite H2; simpl in |- *; ring.
apply power_lt_O; apply lt_trans with 1; auto with arith.
apply power_div_divides; auto with arith.
intros (q2, H2); case (power_div_not_divides r p); auto with arith.
exists q2.
pattern r at 1 in |- *; rewrite (divides_div (power p (power_div r p)) r);
 auto with arith.
rewrite H2; simpl in |- *; ring.
apply power_lt_O; apply lt_trans with 1; auto with arith.
apply power_div_divides; auto with arith.
Qed.
(**)
 
Theorem power_div_fact_prime :
 forall p n : nat,
 0 < n ->
 prime p ->
 power_div (factorial n) p = sum_nm 1 (pred n) (fun x => power_div x p).
intros p n; elim n.
intros H1; inversion H1.
intros n1; case n1.
simpl in |- *; auto.
intros n2 Rec Hn2 H.
replace (factorial (S (S n2))) with (S (S n2) * factorial (S n2));
 auto with arith.
rewrite power_div_mult_prime; auto with arith.
rewrite Rec; auto with arith.
replace (pred (S (S n2))) with (S (pred (S n2))); auto with arith.
rewrite sum_nm_f; simpl in |- *; ring.
Qed.
 
Theorem div_dirac_power_div :
 forall p q r : nat,
 0 < p ->
 1 < q ->
 ~ divides (power q (2 + r)) p ->
 power_div p q = sum_nm 1 r (fun x => div_dirac p (power q x)).
intros p q r H H0 Hr.
case (gt_O_eq (power_div p q)); intros H1.
case (le_lt_or_eq (pred (power_div p q)) r).
apply le_S_n.
rewrite <- (fun x => S_pred x 0); auto with arith.
case (le_or_lt (power_div p q) (S r)); auto.
intros H2; case Hr; apply divides_trans with (b := power q (power_div p q));
 auto with arith.
apply power_div_divides; auto with arith.
intros Hr1.
rewrite sum_nm_split with (r := pred (power_div p q)); auto.
rewrite
 sum_nm_ext
            with
            (n := 1)
           (f := fun x : nat => div_dirac p (power q x))
           (g := fun x : nat => 1).
rewrite
 sum_nm_ext
            with
            (f := fun x : nat => div_dirac p (power q x))
           (g := fun x : nat => 0).
repeat rewrite sum_nm_c.
rewrite <- mult_n_O; rewrite mult_1_r; rewrite <- plus_n_O; auto with arith.
apply (S_pred (power_div p q) 0); auto with arith.
intros x H2; replace (1 + pred (power_div p q)) with (power_div p q).
apply div_dirac_prop2; auto with arith.
apply power_lt_O; auto with arith.
red in |- *; intros H3; absurd (divides (power q (1 + power_div p q)) p).
apply power_div_not_divides; auto with arith.
apply divides_trans with (2 := H3).
exists (power q x); rewrite power_mult; auto with arith.
simpl in |- *; apply (S_pred (power_div p q) 0); auto with arith.
intros x H2; apply div_dirac_prop1; auto with arith.
apply power_lt_O; auto with arith.
apply divides_trans with (power q (power_div p q)).
exists (power q (power_div p q - (1 + x))); rewrite power_mult;
 auto with arith.
rewrite (fun x y z => plus_comm x (y + z)); rewrite <- le_plus_minus;
 auto with arith.
rewrite (S_pred (power_div p q) 0); simpl in |- *; auto with arith.
apply power_div_divides; auto with arith.
intros Hr1; rewrite <- Hr1.
rewrite
 sum_nm_ext
            with
            (n := 1)
           (f := fun x : nat => div_dirac p (power q x))
           (g := fun x : nat => 1).
repeat rewrite sum_nm_c.
rewrite (S_pred (power_div p q) 0); auto with arith.
intros x H2; apply div_dirac_prop1; auto with arith.
apply power_lt_O; auto with arith.
apply divides_trans with (power q (power_div p q)).
exists (power q (power_div p q - (1 + x))); rewrite power_mult;
 auto with arith.
rewrite (fun x y z => plus_comm x (y + z)); rewrite <- le_plus_minus;
 auto with arith.
rewrite (S_pred (power_div p q) 0); simpl in |- *; auto with arith.
apply power_div_divides; auto with arith.
rewrite
 sum_nm_ext
            with
            (f := fun x : nat => div_dirac p (power q x))
           (g := fun x : nat => 0).
repeat rewrite sum_nm_c.
rewrite <- H1; ring.
intros x H2.
apply div_dirac_prop2; auto with arith.
apply power_lt_O; auto with arith.
red in |- *; intros H3; case (power_div_not_divides p q); auto with arith.
rewrite <- H1; apply divides_trans with (2 := H3); auto with arith.
Qed.


(** Relate the power_div of the factorial using quotient *)
 
Theorem power_div_fact_prime_div :
 forall p n r : nat,
 0 < n ->
 n < power p (2 + r) ->
 prime p ->
 power_div (factorial n) p = sum_nm 1 r (fun x => div n (power p x)).
intros p n r Hn Hr Hp.
apply trans_equal with (sum_nm 1 n (fun x : nat => div n (power p x))).
rewrite
 sum_nm_ext
            with
            (g := 
              fun x : nat =>
              sum_nm 1 (pred n) (fun y => div_dirac y (power p x))).
rewrite sum_nm_com with (f := fun x y => div_dirac y (power p x)).
rewrite power_div_fact_prime; auto with arith.
apply sum_nm_ext.
intros x H1; apply div_dirac_power_div; auto with arith.
apply lt_prime; auto.
red in |- *; intros H2; Contradict H1; auto with arith.
apply lt_not_le; apply lt_S_n; rewrite <- (S_pred n 0); auto with arith.
apply lt_le_trans with (power p n).
apply power_id_lt; auto with arith.
apply lt_prime; auto.
apply divides_le; auto with arith.
apply divides_trans with (2 := H2); auto with arith.
intros; apply div_dirac_div; auto with arith.
apply power_lt_O; apply lt_trans with 1; auto with arith.
apply lt_prime; auto.
case (le_or_lt n r); intros H1.
case (le_lt_or_eq _ _ H1); clear H1; intros H1.
rewrite sum_nm_split with (q := r) (r := n); auto.
rewrite sum_nm_ext with (n := 1 + (1 + n)) (g := fun x : nat => 0); auto.
rewrite sum_nm_c with (c := 0); ring.
intros x H.
apply lt_div_O.
apply lt_le_trans with (power p n); auto with arith.
apply power_id_lt; auto with arith.
apply lt_prime; auto.
apply power_le_mono; auto with arith.
apply lt_trans with 1; auto with arith.
apply lt_prime; auto.
rewrite H1; auto.
rewrite sum_nm_split with (q := n) (r := r); auto.
rewrite sum_nm_ext with (n := 1 + (1 + r)) (g := fun x : nat => 0); auto.
rewrite sum_nm_c with (c := 0); ring.
intros x H.
apply lt_div_O.
apply lt_le_trans with (1 := Hr); auto with arith.
apply power_le_mono; auto with arith.
apply lt_trans with 1; auto with arith.
apply lt_prime; auto.
Qed.
