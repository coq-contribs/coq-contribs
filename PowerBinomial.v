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
    Proof of Bertrand's conjecture: PowerBinomial.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)
Require Export PrimeDirac.
Require Import Wf_nat.
Require Import ArithRing.

(** Exact expression for the maximal exponent of binomial 2n n.  *)
 
Theorem power_div_binomial :
 forall n p r : nat,
 prime p ->
 0 < n ->
 2 * n < power p (2 + r) ->
 power_div (binomial (2 * n) n) p =
 sum_nm 1 r (fun x => div (2 * n) (power p x) - 2 * div n (power p x)).
intros n p r H H0 H1.
cut (0 < p); [ intros Hp | apply lt_trans with (2 := lt_prime _ H) ];
 auto with arith.
rewrite <-
 sum_nm_minus
              with
              (f := fun x => div (2 * n) (power p x))
             (g := fun x => 2 * div n (power p x)).
apply plus_minus.
rewrite <- sum_nm_times with (f := fun x : nat => div n (power p x)).
repeat rewrite <- power_div_fact_prime_div; auto with arith.
replace (2 * power_div (factorial n) p) with
 (power_div (factorial n) p + power_div (factorial n) p);
 [ idtac | simpl in |- *; ring ].
repeat rewrite <- power_div_mult_prime; auto with arith.
apply f_equal2 with (f := power_div); auto with arith.
apply sym_equal; replace (2 * n) with (n + n);
 [ rewrite <- binomial_fact | simpl in |- * ]; ring.
replace (2 * n) with (n + n); try apply binomial_lt; auto with arith; ring.
apply le_lt_trans with (2 := H1).
simpl in |- *; auto with arith.
intros x H2 H3.
apply div_mult_le; auto with arith.
apply power_lt_O; auto with arith.
Qed.

(**  Upper bound for p^maxExp(binomial 2n n,p) *)
 
Theorem power_div_binomial1 :
 forall n p : nat,
 prime p -> 0 < n -> power p (power_div (binomial (2 * n) n) p) <= 2 * n.
intros n p H H0.
cut (1 < p); [ intros Hp | apply lt_prime ]; auto.
cut (0 < p); [ intros Hp1 | apply lt_trans with (2 := Hp) ]; auto.
case
 (max_such_prop (fun x : nat => power p x <= 2 * n)
    (fun x => le_dec (power p x) (2 * n)) (2 * n)).
exists 0; simpl in |- *; split; auto with arith.
case
 (max_such (fun x : nat => power p x <= 2 * n)
    (fun x : nat => le_dec (power p x) (2 * n)) (2 * n)); 
 auto.
intros H'2 (H1, H2); apply le_trans with (2 := H1).
apply power_le_mono; auto with arith.
rewrite power_div_binomial with (r := 0); auto with arith.
change (div (2 * n) (power p 1) - 2 * div n (power p 1) <= 0) in |- *.
replace (div (2 * n) (power p 1)) with 0; auto with arith.
apply sym_equal; apply lt_div_O.
apply not_le_lt; apply H2; auto with arith.
apply not_le_lt; apply H2; auto with arith.
replace (2 + 0) with (2 * 1); auto with arith.
intros n1 H'1 (H1, H2); apply le_trans with (2 := H1).
replace (S n1) with (S n1 * 1); auto with arith.
rewrite <- sum_nm_c with (p := 1) (c := 1).
rewrite power_div_binomial with (r := n1); auto with arith.
apply power_le_mono; auto with arith.
apply sum_nm_le; auto with arith.
intros x H3 H4; apply minus_le.
rewrite plus_comm; apply div_mult_lt2; auto with arith.
apply power_lt_O; auto with arith.
case (le_or_lt (2 + n1) (2 * n)); intros Hl.
apply not_le_lt; apply H2; auto with arith.
apply lt_trans with (1 := Hl).
apply power_id_lt; auto with arith.
Qed.

(**  Upper bound for the maximal exponent of (binomial 2n n) 
     in a special case *)
 
Theorem power_div_binomial2 :
 forall n p : nat,
 prime p ->
 0 < n -> 2 * n < power p 2 -> power_div (binomial (2 * n) n) p <= 1.
intros n p H H0 H1; generalize (power_div_binomial1 n p H H0).
case (power_div (binomial (2 * n) n) p); auto with arith.
intros n1; case n1; auto with arith.
intros n2 H2; Contradict H2; auto with arith.
apply lt_not_le; apply lt_le_trans with (power p 2); auto with arith.
apply power_le_mono; auto with arith.
apply lt_trans with 1; auto with arith; apply lt_prime; auto with arith.
Qed.

(**  Exact value of the maximal exponent of (binomial 2n n) 
     in a special case *)
 
Theorem power_div_binomial3 :
 forall n p : nat,
 prime p ->
 2 < n -> 2 * n < 3 * p -> p <= n -> power_div (binomial (2 * n) n) p = 0.
intros n p Hp Hn Hp1 Hp2.
cut (1 < p); [ intros Hp3 | apply lt_prime ]; auto.
cut (0 < p); [ intros Hp4 | apply lt_trans with (2 := Hp3) ]; auto.
rewrite power_div_binomial with (r := 0); auto with arith.
change (div (2 * n) (power p 1) - 2 * div n (power p 1) = 0) in |- *.
repeat rewrite power_SO.
replace (div (2 * n) p) with 2.
replace (div n p) with 1; auto with arith.
apply div_unique; auto with arith.
rewrite mult_1_r; auto.
apply plus_lt_reg_l with (p := p).
apply le_lt_trans with (n + n); auto with arith.
replace (n + n) with (2 * n); auto with arith.
replace (p + p * (1 + 1)) with (3 * p); auto with arith.
rewrite (mult_comm p); simpl in |- *; ring.
simpl in |- *; ring.
apply div_unique; auto with arith.
rewrite (mult_comm p); auto with arith.
replace (p * (1 + 2)) with (3 * p); auto with arith.
apply lt_trans with (2 := Hn); auto.
apply lt_le_trans with (1 := Hp1).
replace (power p (2 + 0)) with (p * p).
case (prime_2_or_more p); auto with arith.
intros H1; Contradict Hp1; auto with arith.
apply le_not_lt.
rewrite (fun x => mult_comm x p); rewrite H1; auto with arith.
repeat rewrite (fun x => mult_comm x p); auto with arith.
simpl in |- *; rewrite mult_1_r; auto.
Qed.

