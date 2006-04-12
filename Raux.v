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
    Proof of Bertrand's conjecture: Raux.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)
Require Export Misc.
Require Export Arith.
Require Export Div.
Require Import ZArith.
Require Import Classical_Prop.
Require Import Rbase.
Require Import Rfunctions.
Require Import Ranalysis.
Require Export Rpower.
Require Import Rtrigo.

Hint Resolve exp_pos: real.
Hint Resolve exp_increasing: real.
Hint Resolve ln_increasing: real.
Hint Resolve sqrt_lt_R0: real.
Hint Resolve Rmult_lt_0_compat: real.
Hint Resolve Rplus_lt_compat_l: real.
Hint Resolve Rinv_0_lt_compat: real.
Hint Resolve Rlt_not_eq: real.

(** Axuillary properties of reals functions *)
 
Theorem Rlt_Rminus_ZERO : forall r1 r2 : R, (r2 < r1)%R -> (0 < r1 - r2)%R.
intros r1 r2 H; replace 0%R with (r1 - r1)%R; unfold Rminus in |- *;
 auto with real.
Qed.
Hint Resolve Rlt_Rminus_ZERO: real.
 
Theorem P_Rmin : forall (P : R -> Prop) (x y : R), P x -> P y -> P (Rmin x y).
intros P x y H1 H2; unfold Rmin in |- *; case (Rle_dec x y); auto.
Qed.
 
Theorem Rle_pow :
 forall (e : R) (n m : nat), (1 < e)%R -> n <= m -> (e ^ n <= e ^ m)%R.
intros e n m H H0; case (le_lt_or_eq _ _ H0); auto with real.
intros H1; rewrite H1; auto with real.
Qed.
 
Theorem Rle_square :
 forall x y : R, (0 <= x)%R -> (0 <= y)%R -> (x * x <= y * y)%R -> (x <= y)%R.
intros x y H H0 H1; case (Rle_or_lt x y); auto.
intros H2; Contradict H1; apply Rlt_not_le.
apply Rle_lt_trans with (x * y)%R; auto with real.
apply Rmult_lt_compat_l; auto with arith.
apply Rle_lt_trans with (1 := H0); auto.
Qed.
 
Theorem sqr_Rsqrt : forall n : nat, (INR (sqr n) <= sqrt (INR n))%R.
intros n; apply Rle_square; auto with real.
apply sqrt_positivity; replace 0%R with (INR 0); auto with real arith.
rewrite <- sqrt_mult; try rewrite sqrt_square; auto with real.
rewrite <- mult_INR; apply le_INR.
apply sqr_le.
Qed.
 
Theorem div_Rdiv :
 forall n m : nat, 0 < m -> (INR (div n m) <= INR n / INR m)%R.
intros n m H; apply Rmult_le_reg_l with (r := INR m); auto with real.
replace (INR m * (INR n / INR m))%R with (INR n).
rewrite <- mult_INR; apply le_INR; auto with arith.
apply div_le; auto.
unfold Rdiv in |- *.
replace (INR m * (INR n * / INR m))%R with (INR n * (INR m * / INR m))%R;
 [ rewrite Rinv_r | ring ]; auto with real.
Qed.

Theorem Rpower_pow :
 forall (n : nat) (x : R), (0 < x)%R -> Rpower x (INR n) = (x ^ n)%R.
intros n; elim n; simpl in |- *; auto; fold INR in |- *.
intros x H; apply Rpower_O; auto.
intros n1; case n1.
intros H x H0; simpl in |- *; rewrite Rmult_1_r; apply Rpower_1; auto.
intros n0 H x H0; rewrite Rpower_plus; rewrite H; try rewrite Rpower_1;
 auto with real.
Qed.
 
Theorem INR_power : forall n m : nat, INR (power n m) = (INR n ^ m)%R.
intros n m; elim m; simpl in |- *; auto with real.
intros m1 H; rewrite mult_INR; rewrite H; auto.
Qed.
 
Theorem Rlt_increasing :
 forall (f f' : R -> R) (a b : R),
 (a <= b)%R ->
 (forall x : R, (a <= x)%R -> (x <= b)%R -> derivable_pt_lim f x (f' x)) ->
 (forall x : R, (a <= x)%R -> (x <= b)%R -> (0 <= f' x)%R) ->
 (0 < f a)%R -> (0 < f b)%R.
intros f f' a b H H0 H1 H2.
case (Rtotal_order a b); intros H'2.
case (MVT_cor2 f f' a b); auto.
intros c (H3, H4); auto.
intros c (H3, (H4, H5)).
replace (f b) with (f a + (f b - f a))%R; [ rewrite H3 | ring ].
apply Rplus_lt_le_0_compat; auto with real.
apply Rmult_le_pos; auto with real.
case H'2; intros H'3.
rewrite <- H'3; auto.
Contradict H'3; auto with real.
unfold Rgt in |- *; apply Rle_not_lt; auto.
Qed.

