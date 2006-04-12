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
    Proof of Bertrand's conjecture: PrimeDirac.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)
Require Export PowerDiv.
Require Export Binomial.
Require Import ArithRing.
Require Export Product.
Require Import Wf_nat.
 
Theorem prime_div_factorial_le :
 forall n p : nat, prime p -> divides p (factorial n) -> p <= n.
intros n p H; elim n; auto.
intros (x, H1); Contradict H; auto.
replace p with 1; auto with arith.
generalize H1; case x; case p; simpl in |- *; auto;
 try (intros; discriminate).
intros n1 H2; rewrite H2; auto.
intros n1 n2; case n2; simpl in |- *;
 repeat (rewrite <- plus_n_Sm || rewrite <- plus_n_O; simpl in |- *);
 auto with arith.
intros n3; repeat rewrite <- plus_n_Sm; intros; discriminate.
intros n0 H0 H1; case (L_Euclides2 p (S n0) (factorial n0)); auto with arith.
intros H2; apply divides_le; auto.
Qed.

(** (prime_dirac n) is n if n is prime 1 otherwise *)
 
Definition prime_dirac (n : nat) :=
  match primeb n with
  | true => n
  | false => 1
  end.
 
Theorem prod_prime_dirac_div :
 forall n m p : nat,
 (forall x : nat, n <= x -> x <= n + m -> divides (prime_dirac x) p) ->
 divides (prod_nm n m (fun x => prime_dirac x)) p.
intros n m; elim m; auto.
simpl in |- *; auto with arith.
intros m1 H p H0.
rewrite prod_nm_f.
cut (divides (prime_dirac (n + S m1)) p); auto with arith.
unfold prime_dirac in |- *; generalize (primeb_correct (n + S m1));
 case (primeb (n + S m1)); fold prime_dirac in |- *; 
 intros H1 (x, H2); rewrite H2.
apply divides_mult; auto with arith.
apply H; auto with arith.
intros x1 H3 H4.
cut (divides (prime_dirac x1) p); auto with arith.
unfold prime_dirac in |- *; generalize (primeb_correct x1); case (primeb x1);
 fold prime_dirac in |- *; intros H5 H6.
apply L_Euclides1 with (a := n + S m1); auto with arith.
rewrite mult_comm; rewrite <- H2; auto.
red in |- *; intros H7; absurd (x1 = n + S m1).
red in |- *; intros H8; Contradict H4; auto.
rewrite H8; auto with arith.
case H1; intros H8 H9; apply sym_equal; apply H9; auto with arith.
red in |- *; intros H10; Contradict H5; auto; rewrite H10; auto with arith.
apply SO_divides_all.
apply H0; auto with arith.
apply le_trans with (1 := H4); auto with arith.
repeat rewrite mult_1_r.
apply H; auto with arith.
intros x1 H3 H4.
rewrite mult_1_r in H2; rewrite <- H2; auto with arith.
apply H0; auto with arith.
apply le_trans with (1 := H4); auto with arith.
Qed.
 
Theorem prime_dirac_divides_binomial :
 forall n m p : nat,
 n < p -> m < p -> p <= n + m -> divides (prime_dirac p) (binomial (n + m) n).
intros n m p H H0 H1.
unfold prime_dirac in |- *; generalize (primeb_correct p); case (primeb p);
 auto.
intros H2.
apply L_Euclides1 with (a := factorial m); auto with arith.
apply L_Euclides1 with (a := factorial n); auto with arith.
rewrite <- mult_assoc_reverse.
rewrite (fun x y z => mult_comm (x * y) z).
rewrite binomial_fact.
generalize H1; elim m; simpl in |- *; auto with arith.
rewrite <- plus_n_O; intros H3; Contradict H; auto with arith.
intros m1; repeat rewrite <- plus_n_Sm.
intros H3 H4; inversion H4; auto.
exists (factorial (n + m1)); rewrite mult_comm; simpl in |- *; auto.
apply divides_trans with (1 := H3 H6).
exists (S (n + m1)); auto.
red in |- *; intros H3; Contradict H; auto with arith.
apply le_not_lt; apply prime_div_factorial_le; auto.
red in |- *; intros H3; Contradict H0; auto with arith.
apply le_not_lt; apply prime_div_factorial_le; auto.
Qed.
 
Theorem prime_prime_dirac : forall p : nat, prime p -> prime_dirac p = p.
intros p; unfold prime_dirac in |- *; generalize (primeb_correct p);
 case (primeb p); auto with arith.
intros H H0; case H; auto.
Qed.
 
Theorem not_prime_prime_dirac :
 forall p : nat, ~ prime p -> prime_dirac p = 1.
intros p; unfold prime_dirac in |- *; generalize (primeb_correct p);
 case (primeb p); auto with arith.
intros H H0; case H0; auto.
Qed.
 
Theorem prod_power_div_aux :
 forall n p q : nat,
 0 < n ->
 p <= q ->
 (forall x : nat, p < x -> prime x -> ~ divides x n) ->
 prod_nm 0 p (fun x : nat => power (prime_dirac x) (power_div n x)) =
 prod_nm 0 q (fun x : nat => power (prime_dirac x) (power_div n x)).
intros n p q Hn H H0; case (le_lt_or_eq _ _ H); intros H1;
 [ idtac | rewrite H1 ]; auto.
rewrite prod_nm_split with (r := p) (q := q); auto.
replace
 (prod_nm (1 + (0 + p)) (q - (1 + p))
    (fun x : nat => power (prime_dirac x) (power_div n x))) with 1;
 auto with arith.
pattern 1 at 1 in |- *; rewrite <- (SO_power (S (q - (1 + p))));
 apply sym_equal.
rewrite <- prod_nm_c with (p := 1 + (0 + p)) (c := 1).
apply prod_nm_ext.
intros x H2.
unfold prime_dirac in |- *; generalize (primeb_correct (1 + (0 + p) + x));
 case (primeb (1 + (0 + p) + x)).
intros H3; generalize (power_div_divides n (1 + (0 + p) + x)).
case (power_div n (1 + (0 + p) + x)); auto.
intros n0 H4; case (H0 (1 + (0 + p) + x)); auto with arith.
rewrite <- (power_SO (1 + (0 + p) + x)); auto with arith.
apply divides_trans with (power (1 + (0 + p) + x) (S n0)); auto with arith.
apply H4; auto with arith.
case (prime_2_or_more _ H3); auto with arith.
intros H5; rewrite H5; auto with arith.
intros H3; apply SO_power; auto with arith.
Qed.
 
Theorem prod_power_div :
 forall n p q : nat,
 0 < n ->
 (forall x : nat, p < x -> prime x -> ~ divides x n) ->
 (forall x : nat, q < x -> prime x -> ~ divides x n) ->
 prod_nm 0 p (fun x : nat => power (prime_dirac x) (power_div n x)) =
 prod_nm 0 q (fun x : nat => power (prime_dirac x) (power_div n x)).
intros n p q H H0 H1; case (le_or_lt p q); intros H2.
apply prod_power_div_aux; auto.
apply sym_equal; apply prod_power_div_aux; auto with arith.
Qed.
 
Theorem prod_power_div_mult :
 forall n m p q r : nat,
 0 < n ->
 0 < m ->
 (forall x : nat, p < x -> prime x -> ~ divides x n) ->
 (forall x : nat, q < x -> prime x -> ~ divides x m) ->
 (forall x : nat, r < x -> prime x -> ~ divides x (n * m)) ->
 prod_nm 0 r (fun x : nat => power (prime_dirac x) (power_div (n * m) x)) =
 prod_nm 0 p (fun x : nat => power (prime_dirac x) (power_div n x)) *
 prod_nm 0 q (fun x : nat => power (prime_dirac x) (power_div m x)).
intros n m p q r H H0 H1 H2 H3.
rewrite prod_power_div with (p := p) (q := r); auto with arith.
rewrite prod_power_div with (p := q) (q := r); auto with arith.
rewrite prod_nm_mult; auto with arith.
apply prod_nm_ext; auto with arith.
intros x H4; simpl in |- *.
unfold prime_dirac in |- *; generalize (primeb_correct x); case (primeb x).
intros H5; rewrite power_div_mult_prime; auto with arith.
apply sym_equal; apply power_mult.
repeat rewrite SO_power; auto.
intros x H4 H'4; red in |- *; intros H5; case (H3 x); auto with arith.
apply divides_trans with (1 := H5); auto with arith.
exists n; auto with arith.
intros x H4 H'4; red in |- *; intros H5; case (H3 x); auto with arith.
apply divides_trans with (1 := H5); auto with arith.
exists m; auto with arith.
Qed.
 
Theorem prime_dirac_le_1 : forall n : nat, 1 <= prime_dirac n.
intros n; generalize (prime_2_or_more n); unfold prime_dirac in |- *;
 generalize (primeb_correct n); case (primeb n); auto with arith.
intros H1 H2; case (H2 H1); auto with arith; intros H3;
 rewrite H3 || apply lt_le_weak; auto with arith.
Qed.
 
Theorem prod_prime_dirac_le_1 :
 forall n : nat, 1 <= prod_nm 0 n (fun x => prime_dirac x).
intros n; elim n; auto.
intros n0 H; rewrite prod_nm_f.
apply le_trans with (prod_nm 0 n0 (fun x : nat => prime_dirac x) * 1);
 auto with arith.
apply (fun m n p : nat => mult_le_compat_l p n m).
apply prime_dirac_le_1.
Qed.
 
Theorem prime_not_prime_S : forall n : nat, 2 < n -> prime n -> ~ prime (S n).
intros n H (H1, H3); case (odd_or_even n); intros (n1, H2).
absurd (n = 2).
Contradict H; rewrite H; auto with arith.
apply H3; auto with arith; exists n1; rewrite mult_comm; auto.
red in |- *; intros (H4, H5); absurd (S n = 2).
Contradict H; rewrite <- H; auto with arith.
apply H5; auto with arith; exists (S n1); rewrite H2.
rewrite (S_to_plus_one n1); rewrite (fun x y => S_to_plus_one (x + y)); ring.
Qed.
 
Theorem div_plus : forall n m : nat, 0 < n -> div (n + m) n = 1 + div m n.
intros n m H; apply sym_equal; apply div_unique; auto.
replace (n * (1 + div m n)) with (n + n * div m n);
 [ apply plus_le_compat_l; apply div_le | ring ]; auto with arith.
replace (n * (1 + (1 + div m n))) with (n + n * (1 + div m n));
 [ apply plus_lt_compat_l; apply div_lt | ring ]; auto with arith.
Qed.
 
Theorem prod_prime_le_aux :
 forall (c n : nat) (f : nat -> nat),
 0 < c ->
 (forall x : nat, x <= n + power 2 4 -> prime x -> f x <= c) ->
 (forall x : nat, x <= n + power 2 4 -> ~ prime x -> f x = 1) ->
 prod_nm 0 (n + power 2 4) (fun x => f x) <=
 power c (div (n + power 2 4) 2 - 1).
intros c n.
generalize (primeb_correct 0); intros P1; simpl in P1.
generalize (primeb_correct 1); intros P2; simpl in P2.
generalize (primeb_correct 2); intros P3; simpl in P3.
generalize (primeb_correct 3); intros P4; simpl in P4.
generalize (primeb_correct 4); intros P5; simpl in P5.
generalize (primeb_correct 5); intros P6; simpl in P6.
generalize (primeb_correct 6); intros P7; simpl in P7.
generalize (primeb_correct 7); intros P8; simpl in P8.
generalize (primeb_correct 8); intros P9; simpl in P9.
generalize (primeb_correct 9); intros P10; simpl in P10.
generalize (primeb_correct 10); intros P11; simpl in P11.
generalize (primeb_correct 11); intros P12; simpl in P12.
generalize (primeb_correct 12); intros P13; simpl in P13.
generalize (primeb_correct 13); intros P14; simpl in P14.
generalize (primeb_correct 14); intros P15; simpl in P15.
generalize (primeb_correct 15); intros P16; simpl in P16.
generalize (primeb_correct 16); intros P17; simpl in P17.
generalize (primeb_correct 17); intros P18; simpl in P18.
pattern n in |- *; apply lt_wf_ind; clear n.
intros n; case n.
simpl in |- *.
intros Rec f H H0 H1.
rewrite (H1 0); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 1); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 4); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 6); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 8); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 9); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 10); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 12); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 14); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 15); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 16); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
apply le_trans with (power c 6).
simpl in |- *; repeat rewrite mult_1_r; repeat apply le_mult; auto; apply H0;
 repeat apply le_n_S; auto with arith.
change (power c 6 <= power c 7) in |- *; apply power_le_mono; auto.
clear n; intros n; case n.
simpl in |- *.
intros Rec f H H0 H1; try assumption.
rewrite (H1 0); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 1); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 4); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 6); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 8); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 9); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 10); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 12); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 14); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 15); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
rewrite (H1 16); try rewrite mult_1_l; repeat apply le_n_S; auto with arith.
simpl in |- *; repeat rewrite mult_1_r; repeat apply le_mult; auto; apply H0;
 repeat apply le_n_S; auto with arith.
intros n0 Rec f H H0 H1.
cut (1 <= div (n0 + power 2 4) 2); [ intros Hle | idtac ].
repeat (rewrite plus_Snm_nSm; rewrite <- plus_n_Sm); repeat rewrite prod_nm_f.
case (prime_dec (0 + S (n0 + power 2 4))); intros H4.
rewrite (H1 (0 + S (S (n0 + power 2 4)))); auto with arith.
rewrite mult_1_r.
replace (div (S (S (n0 + power 2 4))) 2) with (div (2 + (n0 + power 2 4)) 2);
 [ rewrite div_plus | simpl in |- * ]; auto with arith.
replace (power c (1 + div (n0 + power 2 4) 2 - 1)) with
 (power c (div (n0 + power 2 4) 2 - 1) * c).
apply le_mult; auto with arith.
apply Rec; auto with arith.
intros x H5 H6; apply H0; auto with arith.
apply le_trans with (1 := H5); auto with arith.
intros x H5 H6; apply H1; auto with arith.
apply le_trans with (1 := H5); auto with arith.
pattern c at 2 in |- *; rewrite <- (power_SO c); rewrite power_mult.
rewrite plus_minus_assoc; auto with arith.
rewrite <- plus_n_Sm; auto with arith.
apply prime_not_prime_S; auto with arith.
simpl in |- *; rewrite <- plus_n_Sm; rewrite <- plus_n_Sm; auto with arith.
rewrite H1; try rewrite mult_1_r; auto with arith.
replace (div (S (S (n0 + power 2 4))) 2) with (div (2 + (n0 + power 2 4)) 2);
 [ rewrite div_plus | simpl in |- * ]; auto with arith.
replace (power c (1 + div (n0 + power 2 4) 2 - 1)) with
 (power c (div (n0 + power 2 4) 2 - 1) * c).
apply le_mult; auto with arith.
apply Rec; auto with arith.
intros x H5 H6; apply H0; auto with arith.
apply le_trans with (1 := H5); auto with arith.
intros x H5 H6; apply H1; auto with arith.
apply le_trans with (1 := H5); auto with arith.
case (prime_dec (0 + S (S (n0 + power 2 4)))); intros Hp'.
simpl in |- *; auto with arith.
rewrite H1; auto with arith.
pattern c at 2 in |- *; rewrite <- (power_SO c); rewrite power_mult.
rewrite plus_minus_assoc; auto with arith.
simpl in |- *; rewrite <- plus_n_Sm; rewrite <- plus_n_Sm;
 rewrite (fun x y => S_to_plus_one (S (x + y))); rewrite <- plus_Snm_nSm;
 rewrite div_plus; auto with arith.
Qed.
 
Theorem prod_prime_le :
 forall (c n : nat) (f : nat -> nat),
 power 2 4 <= n ->
 0 < c ->
 (forall x : nat, x <= n -> prime x -> f x <= c) ->
 (forall x : nat, x <= n -> ~ prime x -> f x = 1) ->
 prod_nm 0 n (fun x => f x) <= power c (div n 2 - 1).
intros c n f H H0 H1 H2.
rewrite (le_plus_minus (power 2 4) n); auto; rewrite plus_comm;
 apply prod_prime_le_aux; auto with arith.
intros x; rewrite plus_comm; rewrite <- (le_plus_minus (power 2 4) n);
 auto with arith.
intros x; rewrite plus_comm; rewrite <- (le_plus_minus (power 2 4) n);
 auto with arith.
Qed.


(** Majoration of the product of primes *)
 
Theorem prod_prime_lt :
 forall n : nat, 1 < n -> prod_nm 0 n (fun x => prime_dirac x) < power 4 n.
intros n; pattern n in |- *; apply lt_wf_ind; clear n; intros n.
case (odd_or_even n).
intros (x, H2); rewrite H2.
case x.
intros Rec H1; inversion H1.
intros x1; case x1.
simpl in |- *; auto with arith.
intros x2 Rec H1.
cut (2 * S (S x2) = S (S x2 + S (S x2))); [ intros H3 | auto with arith ].
rewrite H3; rewrite prod_nm_f.
replace (prime_dirac (0 + S (S x2 + S (S x2)))) with 1.
rewrite mult_1_r; auto.
apply lt_trans with (power 4 (S x2 + S (S x2))); auto with arith.
apply Rec; auto with arith.
rewrite H3; auto with arith.
rewrite <- plus_n_Sm; auto with arith.
apply power_lt_mono; auto with arith.
simpl in |- *; unfold prime_dirac in |- *.
generalize (primeb_correct (S (S (x2 + S (S x2)))));
 case (primeb (S (S (x2 + S (S x2))))); auto.
intros (H4, H5); absurd (S (S (x2 + S (S x2))) = 2); auto with arith.
rewrite <- plus_n_Sm; red in |- *; intros H6; discriminate.
apply H5; auto.
exists (S (S x2)); auto with arith.
rewrite mult_comm; rewrite H3; auto with arith.
simpl in |- *; repeat rewrite <- plus_n_Sm; rewrite <- plus_n_O;
 auto with arith.
intros (x1, H1); rewrite H1; intros Rec H2.
cut (1 <= x1);
 [ intros Hx1 | generalize H2; case x1; simpl in |- *; auto with arith ].
rewrite prod_nm_split with (r := x1 + 1); auto with arith.
2: replace (x1 + 1) with (x1 + 1 + 0); auto with arith;
    replace (2 * x1 + 1) with (x1 + 1 + x1); auto with arith; 
    ring.
apply
 le_lt_trans
  with
    (prod_nm 0 (x1 + 1) (fun x : nat => prime_dirac x) *
     binomial (2 * x1 + 1) (x1 + 1)).
apply (fun m n p : nat => mult_le_compat_l p n m).
apply divides_le; auto with arith.
apply sym_not_equal; apply lt_O_neq; auto with arith.
replace (2 * x1 + 1) with (x1 + 1 + x1); auto with arith.
apply binomial_lt; auto with arith.
simpl in |- *; ring.
replace (1 + (0 + (x1 + 1))) with (x1 + 2); [ idtac | ring ].
replace (2 * x1 + 1 - (1 + (x1 + 1))) with (x1 - 1); [ idtac | idtac ].
apply prod_prime_dirac_div.
intros x H H0.
replace (2 * x1 + 1) with (x1 + 1 + x1); [ idtac | ring ].
apply prime_dirac_divides_binomial; auto with arith.
apply lt_le_trans with (2 := H); auto with arith.
apply lt_le_trans with (2 := H); auto with arith.
rewrite plus_comm; auto with arith.
replace (x1 + 1 + x1) with (x1 + 2 + (x1 - 1)); auto.
pattern x1 at 4 in |- *;
 (rewrite le_plus_minus with (n := 1); [ ring | auto ]).
apply plus_minus.
repeat rewrite plus_assoc_reverse.
rewrite <- le_plus_minus; [ ring | auto ].
apply
 le_lt_trans
  with (prod_nm 0 (x1 + 1) (fun x : nat => prime_dirac x) * power 2 (2 * x1)).
apply (fun m n p : nat => mult_le_compat_l p n m).
apply binomial_odd.
replace (power 4 (2 * x1 + 1)) with (power 4 (x1 + 1) * power 2 (2 * x1)).
repeat rewrite (fun x y => mult_comm x (power 2 y)).
apply mult_lt_bis; auto with arith.
apply power_lt_O; auto with arith.
apply Rec; auto with arith.
replace (x1 + 1) with (x1 + 1 + 0); auto with arith;
 replace (2 * x1 + 1) with (x1 + 1 + x1); auto with arith; 
 ring.
change (0 + 1 < x1 + 1) in |- *; auto with arith.
rewrite <- power_power.
simpl in |- *; rewrite power_mult.
repeat rewrite <- plus_n_Sm; repeat rewrite <- plus_n_O; auto with arith.
Qed.

(** Factorisation theorem *)
Theorem factorization :
 forall n p : nat,
 0 < n ->
 (forall x : nat, p < x -> prime x -> ~ divides x n) ->
 n = prod_nm 0 p (fun x : nat => power (prime_dirac x) (power_div n x)).
intros n; pattern n in |- *; apply lt_wf_ind; clear n.
intros n H p H0 H1.
cut
 (forall p : nat, 0 < p -> forall x : nat, p < x -> prime x -> ~ divides x p);
 [ intros Hp | idtac ].
generalize (max_div_prop1 n); generalize (max_div_prop2 n);
 generalize (max_div_prop3 n); case (max_div n).
intros H2 H3 (x, H4); Contradict H0; auto; rewrite H4; rewrite <- mult_n_O;
 auto with arith.
intros m1; case m1.
intros H2 H3 H4.
2: intros n0 H2 H3 (x, H4); rewrite H4.
2: cut (0 < x);
    [ intros Hx
    | generalize H0; rewrite H4; case x; simpl in |- *; auto with arith ].
2: pattern x at 1 in |- *; rewrite H with (m := x) (p := x); auto with arith.
2: pattern (S (S n0)) at 1 in |- *;
    rewrite H with (m := S (S n0)) (p := S (S n0)); 
    auto with arith.
2: apply sym_equal; apply prod_power_div_mult; auto with arith.
2: rewrite <- H4; auto.
2: apply H2; rewrite H4; inversion Hx; simpl in |- *; auto with arith.
2: rewrite H4; rewrite mult_comm; inversion Hx; simpl in |- *;
    try rewrite <- plus_n_Sm; auto with arith.
2: intros p0 H2 x H3 H4; red in |- *; intros H5; Contradict H3;
    auto with arith.
2: apply le_not_lt; apply divides_le; auto with arith.
2: apply sym_not_equal; auto with arith.
cut (prime n \/ n = 1); [ intros H5; case H5; intros H6 | idtac ].
rewrite prod_power_div with (q := n); auto with arith.
pattern n at 2 in |- *; rewrite (S_pred n 0); auto with arith.
rewrite prod_nm_f; auto with arith.
rewrite <- (S_pred n 0); auto with arith.
replace
 (prod_nm 0 (pred n) (fun x : nat => power (prime_dirac x) (power_div n x)))
 with (power 1 (S (pred n))).
rewrite SO_power; simpl in |- *; rewrite <- plus_n_O.
rewrite prime_prime_dirac; try rewrite power_div_id; simpl in |- *;
 auto with arith.
rewrite <- prod_nm_c with (p := 0).
apply prod_nm_ext.
intros x H7; simpl in |- *.
generalize (power_div_divides n x H0); generalize (H3 x); generalize H7.
case x.
rewrite not_prime_prime_dirac; try rewrite SO_power; auto with arith.
intros x1; case x1.
rewrite not_prime_prime_dirac; try rewrite SO_power; auto with arith.
intros x2; case (power_div n (S (S x2))).
simpl in |- *; auto.
intros n0 H8 H9 H10; absurd (divides (S (S x2)) n); auto.
apply H9; auto with arith.
apply le_lt_trans with (1 := H8); auto with arith.
rewrite <- (fun x => power_SO (S (S x)));
 apply divides_trans with (power (S (S x2)) (S n0)); 
 auto with arith.
rewrite prod_power_div with (q := 1); auto with arith.
simpl in |- *; auto with arith.
rewrite H6; repeat rewrite not_prime_prime_dirac; auto with arith.
rewrite H6.
intros x H7 H8; apply not_lt_div; auto with arith.
generalize H3; inversion H0; auto.
case m; auto.
intros n0 H7; left; split; auto with arith.
intros b H8 H9; apply le_antisym.
case (le_or_lt (S (S n0)) b); auto; intros H10.
case (H7 b); auto with arith.
generalize H8 H9; case b; simpl in |- *; auto with arith.
intros (x, H11); rewrite mult_comm in H11; discriminate.
intros x; case x; auto with arith.
intros H11 H12; case H12; auto.
apply divides_le; auto.
Qed.