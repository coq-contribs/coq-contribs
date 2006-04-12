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
    Proof of Bertrand's conjecture: Bertrand.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)
Require Import Wf_nat.
Require Import ArithRing.
Require Export PowerBinomial.
Require Export Check128.
Require Export RIneq.
Require Import Ranalysis.
Require Import Rtrigo.
Require Export PrimeDirac.
Require Export Raux.

(** Upper Bound for (binonial 2n n) *)

Theorem upper_bound :
 forall n : nat,
 power 2 7 <= n ->
 (forall p : nat, n < p -> p < 2 * n -> ~ prime p) ->
 binomial (2 * n) n <
 power (2 * n) (div (sqr (2 * n)) 2 - 1) * power 4 (div (2 * n) 3).
intros n H H0.
cut (0 < n); [ intros Hn | apply lt_le_trans with (2 := H); simpl in |- * ];
 auto with arith.
cut (0 < binomial (2 * n) n);
 [ intros Hc
 | replace (2 * n) with (n + n); try apply binomial_lt; auto with arith; ring ].
cut (sqr (2 * n) < div (2 * n) 3); [ intros Hd | idtac ].
rewrite (fun x y : nat => factorization (binomial x y) (div (2 * n) 3));
 auto with arith.
rewrite prod_nm_split with (r := sqr (2 * n)); auto with arith.
apply
 lt_le_trans
  with
    (prod_nm 0 (sqr (2 * n))
       (fun x : nat =>
        power (prime_dirac x) (power_div (binomial (2 * n) n) x)) *
     power 4 (div (2 * n) 3)).
apply mult_lt_bis.
apply lt_le_trans with (power 1 (S (sqr (2 * n)))); auto with arith.
rewrite SO_power; auto with arith.
rewrite <- prod_nm_c with (p := 0); apply prod_nm_le; auto with arith.
intros x H1 H2.
apply lt_le_S; auto with arith.
apply power_lt_O.
case (prime_dec x); intros Hx;
 [ rewrite prime_prime_dirac | rewrite not_prime_prime_dirac ];
 auto with arith.
generalize Hx; case x; auto with arith; intros Hx1; Contradict Hx1;
 auto with arith.
rewrite <- (fun x y f => mult_1_l (prod_nm x y f)).
pattern 1 at 1 in |- *; rewrite <- (SO_power (S (sqr (2 * n)))).
apply
 le_lt_trans with (prod_nm 0 (div (2 * n) 3) (fun x : nat => prime_dirac x));
 auto with arith.
rewrite prod_nm_split with (p := 0) (r := sqr (2 * n)); auto with arith.
apply le_mult.
rewrite <- prod_nm_c with (p := 0).
apply prod_nm_le.
intros x H7 H8; unfold prime_dirac in |- *; generalize (primeb_correct x);
 case (primeb x); auto with arith.
case x; auto with arith.
intros H9; Contradict H9; auto with arith.
apply prod_nm_le.
intros x H7 H8.
unfold prime_dirac in |- *; generalize (primeb_correct x); case (primeb x);
 intros Hx.
pattern x at 3 in |- *; rewrite <- power_SO.
apply power_le_mono.
generalize Hx; case x; auto with arith.
intros H9; Contradict H9; auto with arith.
apply power_div_binomial2; auto with arith.
apply lt_le_trans with (1 := sqr_lt (2 * n)).
replace (power x 2) with (x * x); [ apply le_mult | simpl in |- *; ring ];
 auto with arith.
rewrite SO_power; auto with arith.
apply prod_prime_lt; auto with arith.
apply lt_le_trans with (2 := Hd).
apply le_lt_n_Sm; auto with arith.
apply (sqr_mono 1).
apply le_trans with (2 * power 2 7); auto with arith; simpl in |- *;
 auto with arith.
apply le_mult.
apply
 prod_prime_le
  with
    (f := fun x : nat =>
          power (prime_dirac x) (power_div (binomial (2 * n) n) x));
 auto with arith.
replace (power 2 4) with (sqr (2 * power 2 7)); [ idtac | auto ].
apply sqr_mono; auto with arith.
intros x H7 H8.
rewrite prime_prime_dirac; auto; apply power_div_binomial1; auto.
intros x H7 H8.
rewrite not_prime_prime_dirac; auto; apply SO_power; auto.
auto with arith.
intros x H7 H8.
case (le_or_lt x (2 * n)); intros Hp1.
case (le_or_lt x n); intros Hp2.
replace x with (power x (1 + power_div (binomial (2 * n) n) x)).
apply power_div_not_divides; auto with arith.
generalize H8; case x; auto with arith.
intros Ht; Contradict Ht; auto with arith.
intros x1; case x1; auto with arith.
intros Ht; Contradict Ht; auto with arith.
rewrite power_div_binomial3; auto with arith.
simpl in |- *; ring.
apply lt_le_trans with (2 := H); simpl in |- *; auto with arith.
apply lt_le_trans with (3 * (1 + div (2 * n) 3)); auto with arith.
apply div_lt; auto with arith.
case (le_lt_or_eq _ _ Hp1); intros Hp3; auto with arith.
Contradict H8; auto with arith.
Contradict H8; auto with arith.
rewrite Hp3.
red in |- *; intros (H9, H10).
absurd (2 * n = 2).
red in |- *; intros H11; Contradict H.
apply lt_not_le.
apply lt_mult_right_anti with (z := 2); rewrite H11; simpl in |- *;
 auto with arith.
apply H10; auto with arith.
exists n; auto with arith.
red in |- *; intros H9;
 absurd
  (divides (power x (power_div (binomial (2 * n) n) x)) (binomial (2 * n) n)).
red in |- *; intros H10;
 absurd (power x (power_div (binomial (2 * n) n) x) <= 2 * n).
apply lt_not_le; apply lt_le_trans with (1 := Hp1).
generalize (power_div_not_divides (binomial (2 * n) n) x).
case (power_div (binomial (2 * n) n) x); auto with arith.
intros H11; case H11; auto with arith.
generalize H8; case x; auto with arith.
intros Ht; Contradict Ht; auto with arith.
intros x1; case x1; auto with arith.
intros Ht; Contradict Ht; auto with arith.
rewrite <- plus_n_O; rewrite power_SO; auto.
intros n0 H11; pattern x at 1 in |- *; rewrite <- power_SO; auto with arith.
apply power_le_mono; auto with arith.
apply lt_trans with (2 := H7); auto with arith.
apply le_lt_trans with (2 := Hd); auto with arith.
apply power_div_binomial1; auto with arith.
apply power_div_divides; auto with arith.
apply lt_trans with (2 := H7); auto with arith.
apply le_lt_trans with (2 := Hd); auto with arith.
change (sqr 1 <= sqr (2 * n)) in |- *.
apply sqr_mono.
apply le_trans with (2 * power 2 7); auto with arith; simpl in |- *;
 auto with arith.
apply mult_id_lt_inv.
apply le_lt_trans with (2 * n).
apply sqr_le.
apply lt_le_trans with (3 * (1 + div (2 * n) 3)); auto with arith.
apply div_lt.
auto with arith.
cut (4 <= div (2 * n) 3); [ intros H1 | idtac ].
apply le_trans with (4 * div (2 * n) 3); auto with arith.
replace 4 with (1 + 3); auto with arith.
rewrite mult_plus_distr_l; rewrite mult_plus_distr_r.
apply plus_le_compat; auto with arith.
apply le_trans with 4; auto with arith.
rewrite mult_1_l; auto.
apply le_mult; auto with arith.
apply lt_n_Sm_le.
apply lt_mult_right_anti with (z := 3).
apply le_lt_trans with (2 * n); auto with arith.
apply le_trans with (2 * power 2 7); auto with arith.
apply le_trans with (2 * power 2 3).
simpl in |- *; auto with arith.
apply le_mult; auto with arith.
apply power_le_mono; auto with arith.
apply (div_lt (2 * n) 3); auto with arith.
Qed.

(** If there is no prime number this inequality should hold *) 
Theorem no_prime_imp_spec_inegality :
 forall n : nat,
 power 2 7 <= n ->
 (forall p : nat, n < p -> p < 2 * n -> ~ prime p) ->
 power 4 n < power (2 * n) (div (sqr (2 * n)) 2) * power 4 (div (2 * n) 3).
intros n H H0.
apply le_lt_trans with (2 * n * binomial (2 * n) n).
replace 4 with (power 2 2); auto with arith.
rewrite power_power; apply binomial_even; auto with arith.
apply lt_le_trans with (2 := H); auto with arith; simpl in |- *;
 auto with arith.
rewrite (le_plus_minus 1 (div (sqr (2 * n)) 2)).
rewrite <- power_mult; rewrite power_SO.
rewrite (mult_assoc_reverse (2 * n)).
apply mult_lt_bis; auto with arith.
apply lt_le_trans with (2 * power 2 7); auto with arith; simpl in |- *;
 auto with arith.
apply upper_bound; auto with arith.
apply lt_n_Sm_le.
apply lt_mult_right_anti with (z := 2).
apply lt_trans with (sqr (2 * n)).
apply lt_S_n; apply mult_id_lt_inv; auto with arith.
apply le_lt_trans with (2 * n).
apply le_trans with (2 * power 2 3); auto with arith.
simpl in |- *; repeat apply le_n_S; auto with arith.
apply le_trans with (2 * power 2 7); auto with arith.
apply le_mult; auto with arith.
apply power_le_mono; auto with arith.
apply sqr_lt.
rewrite (fun x y => S_to_plus_one (div x y)); apply div_lt; auto with arith.
Qed.

(** The oppositive inequality holds for x > 128 *) 
Theorem spec_fun_bound :
 forall x : R,
 (Rpower 2 (1 + (1 + (1 + (1 + 3)))) <= x)%R ->
 (Rpower (2 * x) (sqrt (2 * x) / 2) < Rpower (1 + 3) (x / 3))%R.
intros x H.
cut (0 < x)%R;
 [ intros Hx
 | apply Rlt_le_trans with (2 := H); unfold Rpower in |- *; auto with real ].
apply ln_lt_inv.
unfold Rpower in |- *; auto with real.
unfold Rpower in |- *; auto with real.
unfold Rdiv in |- *; auto with real.
unfold Rpower in |- *.
repeat rewrite ln_exp.
cut (0 < sqrt (2 * x))%R;
 [ intros Hs
 | apply sqrt_lt_R0; auto with real; apply Rmult_lt_0_compat; auto with real ].
apply Rmult_lt_reg_l with (r := (/ sqrt (2 * x))%R); auto with real.
repeat rewrite <- Rmult_assoc.
rewrite Rinv_l; auto with real.
rewrite Rmult_1_l.
pattern x at 3 in |- *; rewrite <- (sqrt_square x); auto with real.
repeat rewrite sqrt_mult; auto with real.
replace (/ (sqrt 2 * sqrt x) * (sqrt x * sqrt x) * / 3 * ln (1 + 3))%R with
 (ln (1 + 3) / (sqrt 2 * 3) * sqrt x)%R; [ idtac | field ].
2: apply Compare.not_eq_sym; auto with real.
2: apply Rlt_not_eq; auto with real.
2: repeat apply Rmult_lt_0_compat; auto with real.
2: repeat apply Rplus_le_lt_0_compat; auto with real.
2: repeat apply Rplus_le_lt_0_compat; auto with real.
apply Rminus_lt; apply Ropp_lt_cancel; rewrite Ropp_minus_distr;
 rewrite Ropp_0.
apply
 Rlt_increasing
  with
    (a := Rpower 2 (1 + (1 + (1 + (1 + 3)))))
    (f := fun x => (ln (1 + 3) / (sqrt 2 * 3) * sqrt x - / 2 * ln (2 * x))%R)
    (f' := fun x : R =>
           (ln (1 + 3) / (sqrt 2 * 3) * / (2 * sqrt x) -
            / 2 * (2 * / (2 * x)))%R); auto.
intros y Hy Hy1.
cut (0 < y)%R;
 [ intros Hyy
 | apply Rlt_le_trans with (2 := Hy); unfold Rpower in |- *; auto with real ].
apply
 derivable_pt_lim_minus
  with
    (f1 := fun x0 : R => (ln (1 + 3) / (sqrt 2 * 3) * sqrt x0)%R)
    (f2 := fun x0 : R => (/ 2 * ln (2 * x0))%R).
apply
 derivable_pt_lim_scal with (f := sqrt) (a := (ln (1 + 3) / (sqrt 2 * 3))%R).
apply derivable_pt_lim_sqrt; auto.
apply
 derivable_pt_lim_scal with (f := fun x0 : R => ln (2 * x0)) (a := (/ 2)%R).
rewrite (fun x y => Rmult_comm x (/ y)).
apply derivable_pt_lim_comp with (f1 := fun x0 : R => (2 * x0)%R) (f2 := ln).
pattern 2%R at 2 in |- *; rewrite <- (Rmult_1_r 2).
apply derivable_pt_lim_scal with (f := id) (a := 2%R).
apply derivable_pt_lim_id.
apply derivable_pt_lim_ln.
apply Rmult_lt_0_compat; auto with real.
intros z H1 H2; apply Rlt_le.
cut (0 < z)%R; [ intros Hz | idtac ].
apply Rlt_Rminus_ZERO.
repeat rewrite <- Rmult_assoc; rewrite Rinv_l; auto with real.
rewrite Rmult_1_l.
apply Rmult_lt_reg_l with (r := (2 * z)%R); auto with real.
rewrite Rinv_r; auto with real.
replace (ln (1 + 3)) with (2 * ln 2)%R.
pattern z at 1 in |- *; rewrite <- sqrt_square; auto with real.
rewrite sqrt_mult; auto with real.
replace
 (2 * (sqrt z * sqrt z) * (2 * ln 2 / (sqrt 2 * 3) * / (2 * sqrt z)))%R with
 (2 * sqrt z * (ln 2 / (sqrt 2 * 3)))%R.
apply
 Rlt_le_trans
  with
    (2 * sqrt (Rpower 2 (1 + (1 + (1 + (1 + 3))))) * (ln 2 / (sqrt 2 * 3)))%R.
rewrite Rpower_plus.
rewrite Rpower_1; auto with real.
rewrite sqrt_mult; auto with real.
rewrite <- (fun x y => Rpower_sqrt (Rpower x y)); auto with real.
rewrite Rpower_mult; auto with real.
replace ((1 + (1 + (1 + 3))) * / 2)%R with 3%R; [ idtac | field ].
replace (2 * (sqrt 2 * Rpower 2 3) * (ln 2 / (sqrt 2 * 3)))%R with
 (2 * Rpower 2 3 * (ln 2 / 3))%R.
pattern 2%R at 1 in |- *; rewrite <- (Rpower_1 2); auto with real.
rewrite <- Rpower_plus.
apply Rmult_lt_reg_l with (r := 3%R); auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
rewrite Rmult_1_r.
apply Rlt_trans with (3 * (Rpower 2 (1 + 3) * (/ 2 / 3)))%R.
repeat rewrite Rpower_plus; repeat rewrite Rpower_1.
replace (3 * (16 * (/ 2 / 3)))%R with 8%R; [ idtac | field ].
repeat rewrite Rmult_plus_distr_r; repeat rewrite Rmult_plus_distr_l;
 repeat rewrite Rmult_1_l.
repeat rewrite Rplus_assoc; auto with real.
repeat apply Rplus_lt_compat_l; auto with real.
pattern 1%R at 1 in |- *; replace 1%R with (1 + 0)%R;
 [ apply Rplus_lt_compat_l; repeat apply Rplus_lt_0_compat | ring ];
 auto with real.
apply Compare.not_eq_sym; apply Rlt_not_eq; auto with real.
apply Rmult_lt_0_compat; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
apply Rmult_lt_compat_l; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
apply Rmult_lt_compat_l; auto with real.
unfold Rpower in |- *; auto with real.
unfold Rdiv in |- *; apply Rmult_lt_compat_r; auto with real.
apply Rinv_0_lt_compat; repeat apply Rplus_lt_0_compat; auto with real.
apply ln_lt_2.
cut
 (forall x y z : R,
  (0 < z)%R -> (2 * x * (y / 3))%R = (2 * (z * x) * (y / (z * 3)))%R);
 [ intros Htmp; apply Htmp | intros; field ]; auto with real.
apply Compare.not_eq_sym; apply Rlt_not_eq; auto with real.
apply Rmult_lt_0_compat; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
apply Rmult_lt_0_compat; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
apply Compare.not_eq_sym; apply Rlt_not_eq; auto with real.
unfold Rpower in |- *; auto with real.
unfold Rpower in |- *; auto with real.
unfold Rdiv in |- *.
repeat apply Rmult_le_compat; auto with real.
repeat apply Rmult_le_pos; auto with real.
apply sqrt_positivity; auto with real.
unfold Rpower in |- *; auto with real.
repeat apply Rmult_le_pos; auto with real.
rewrite <- ln_1; auto with real.
apply Rlt_le; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
apply sqrt_positivity; auto with real.
unfold Rpower in |- *; auto with real.
apply sqrt_le_1; auto with real.
unfold Rpower in |- *; auto with real.
rewrite <- ln_1; auto with real.
apply Rlt_le; apply Rinv_0_lt_compat; apply Rmult_lt_0_compat; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
field; auto with real.
apply Compare.not_eq_sym; apply Rlt_not_eq; auto with real.
repeat apply Rmult_lt_0_compat; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
apply exp_inv.
rewrite exp_ln.
change (Rpower 2 2 = (1 + 3)%R) in |- *.
repeat rewrite Rpower_plus; repeat rewrite Rpower_1; try ring.
repeat apply Rplus_lt_0_compat; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
apply Compare.not_eq_sym; apply Rlt_not_eq; auto with real.
apply Compare.not_eq_sym; apply Rlt_not_eq; auto with real.
apply Rlt_le_trans with (2 := H1).
unfold Rpower in |- *; auto with real.
pattern (Rpower 2 (1 + (1 + (1 + (1 + 3))))) at 1 in |- *;
 rewrite Rpower_plus; rewrite Rpower_1; auto with real.
rewrite sqrt_mult; auto with real.
2: unfold Rpower in |- *; auto with real.
rewrite ln_mult.
pattern (sqrt (Rpower 2 (1 + (1 + (1 + 3))))) at 1 in |- *;
 rewrite <- Rpower_sqrt.
rewrite Rpower_mult.
replace ((1 + (1 + (1 + 3))) * / 2)%R with 3%R; [ idtac | field ].
replace (ln (1 + 3)) with (2 * ln 2)%R.
pattern (ln (Rpower 2 (1 + (1 + (1 + (1 + 3)))))) at 1 in |- *;
 unfold Rpower in |- *; rewrite ln_exp; auto with real.
replace (2 * ln 2 / (sqrt 2 * 3) * (sqrt 2 * exp (3 * ln 2)))%R with
 (2 * ln 2 * (/ 3 * Rpower 2 3))%R.
2: cut
    (forall x y z : R,
     (0 < y)%R -> (2 * x * (/ 3 * z))%R = (2 * x / (y * 3) * (y * z))%R);
    [ intros Htmp; fold Rpower in |- *; apply Htmp | intros; field ];
    auto with real.
apply Rlt_Rminus_ZERO.
pattern (ln 2) at 1 in |- *; rewrite <- Rmult_1_l.
rewrite <- Rmult_plus_distr_r.
replace (/ 2 * ((1 + (1 + (1 + (1 + (1 + 3))))) * ln 2))%R with
 (2 * ln 2 * 2)%R.
apply Rmult_lt_compat_l; auto with real.
repeat apply Rmult_lt_0_compat; auto with real.
rewrite <- ln_1; auto with real.
apply Rmult_lt_reg_l with (r := 3%R); auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
repeat rewrite <- Rmult_assoc; rewrite Rinv_r; auto with arith.
rewrite Rmult_1_l.
repeat rewrite Rpower_plus; repeat rewrite Rpower_1; try ring.
repeat rewrite Rmult_plus_distr_r; repeat rewrite Rmult_plus_distr_l;
 repeat rewrite Rmult_1_l.
repeat rewrite Rplus_assoc; auto with real.
repeat apply Rplus_lt_compat_l; auto with real.
pattern 1%R at 1 in |- *; replace 1%R with (1 + 0)%R;
 [ apply Rplus_lt_compat_l; repeat apply Rplus_lt_0_compat | ring ];
 auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
apply Compare.not_eq_sym; apply Rlt_not_eq; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
field; auto with real.
apply Compare.not_eq_sym; apply Rlt_not_eq; auto with real.
unfold Rpower in |- *.
apply Compare.not_eq_sym; apply Rlt_not_eq; auto with real.
repeat apply Rmult_lt_0_compat; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
apply exp_inv.
rewrite exp_ln.
change (Rpower 2 2 = (1 + 3)%R) in |- *.
repeat rewrite Rpower_plus; repeat rewrite Rpower_1; try ring.
repeat apply Rplus_lt_0_compat; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
apply Compare.not_eq_sym; apply Rlt_not_eq; auto with real.
unfold Rpower in |- *; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
unfold Rpower in |- *; auto with real.
Qed.

(** Main result: there is always a prime between n and 2n *)
 
Theorem Bertrand :
 forall n : nat, 2 <= n -> exists p : nat, prime p /\ n < p /\ p < 2 * n.
intros n H.
case (le_or_lt n (power 2 7)); intros H1.
apply postulate_correct_128; auto.
case (postulate_dec n); auto.
intros n0;
 absurd
  (power 4 n < power (2 * n) (div (sqr (2 * n)) 2) * power 4 (div (2 * n) 3)).
2: apply no_prime_imp_spec_inegality; auto.
2: apply lt_le_weak; auto.
apply le_not_lt.
apply INR_le.
repeat rewrite INR_power; rewrite mult_INR; repeat rewrite INR_power.
repeat rewrite <- Rpower_pow.
apply
 Rle_trans
  with
    (Rpower (INR (2 * n)) (sqrt (INR (2 * n)) / INR 2) *
     Rpower (INR 4) (INR (2 * n) / INR 3))%R.
apply Rmult_le_compat; auto with real.
unfold Rpower in |- *; apply Rlt_le; auto with real.
unfold Rpower in |- *; apply Rlt_le; auto with real.
apply Rle_Rpower; simpl in |- *; auto with real.
replace 1%R with (INR 1); auto with real arith.
apply Rle_trans with (INR (sqr (n + (n + 0))) / 2)%R.
apply div_Rdiv with (m := 2); auto with real arith.
unfold Rdiv in |- *; apply Rmult_le_compat; auto with real arith.
apply sqr_Rsqrt.
apply Rle_Rpower; auto with real.
apply div_Rdiv; auto with real arith.
rewrite Rmult_comm.
apply Rmult_le_reg_l with (r := (/ Rpower (INR 4) (INR (2 * n) / INR 3))%R);
 auto with real.
apply Rinv_0_lt_compat; unfold Rpower in |- *; auto with real.
rewrite <- Rmult_assoc; rewrite Rinv_l.
rewrite Rmult_1_l.
rewrite <- Rpower_Ropp.
rewrite <- Rpower_plus.
replace (- (INR (2 * n) / INR 3) + INR n)%R with (INR n / INR 3)%R.
repeat rewrite mult_INR.
simpl in |- *.
repeat rewrite Rplus_assoc.
apply Rlt_le.
apply spec_fun_bound.
replace (1 + (1 + (1 + (1 + 3))))%R with (INR 7); [ idtac | simpl in |- * ];
 auto.
replace 2%R with (INR 2); [ idtac | simpl in |- * ]; auto.
rewrite Rpower_pow.
rewrite <- INR_power; auto with real.
replace 0%R with (INR 0); auto with real arith.
ring.
rewrite mult_INR; simpl in |- *; field.
rewrite Rplus_assoc; apply Compare.not_eq_sym; auto with real.
apply Rlt_not_eq; auto with real.
repeat apply Rplus_lt_0_compat; auto with real.
unfold Rpower in |- *; apply Compare.not_eq_sym; auto with real.
replace 0%R with (INR 0); auto with real arith.
replace 0%R with (INR 0); auto with real arith.
replace 0%R with (INR 0); auto with real arith.
Qed.