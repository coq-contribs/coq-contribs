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
    Proof of Bertrand's conjecture: Gcd.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)

Require Import Arith.
Require Import ArithRing.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Wf_nat.
Require Export Prime.
Require Export Power.
(*********************************************************************
  * Gcd as a predicate *)

(** (is_gcd a b c) means c is the gcd of a and b *) 
Definition is_gcd (a b c : nat) : Prop :=
  divides c a /\
  divides c b /\ (forall d : nat, divides d a -> divides d b -> divides d c).
Hint Resolve div_ref all_divides_O.
 
Lemma is_gcd_unic :
 forall a b c d : nat, is_gcd a b c -> is_gcd a b d -> c = d.
intros a b c d (H1, (H2, H3)) (H5, (H6, H7)).
apply divides_antisym; auto.
Qed.
 
Lemma is_gcd_ref : forall x : nat, is_gcd x x x.
intros x; repeat split; auto with arith.
Qed.
 
Lemma is_gcd_sym : forall a b c : nat, is_gcd a b c -> is_gcd b a c.
intros a b c (H1, (H2, H3)); split; auto.
Qed.
 
Lemma is_gcd_O' : forall a r : nat, is_gcd a 0 r -> a = r.
intros a r (H1, (H2, H3)); apply divides_antisym; auto.
Qed.
 
Lemma is_gcd_Ol : forall a : nat, is_gcd a 0 a.
intros a; split; auto.
Qed.
 
Lemma is_gcd_Or : forall a : nat, is_gcd 0 a a.
intros a; split; auto.
Qed.
 
Lemma prime_gcd : forall p n : nat, prime p -> ~ divides p n -> is_gcd n p 1.
intros p n H' H'0; split; auto; split; auto.
intros d H'1 H'2.
case H'; intros H'3 H'4.
case (eq_nat_dec d 1); intros H'5; auto.
rewrite H'5; auto.
case (eq_nat_dec p d); intros H'6; auto.
case H'0; try rewrite H'6; auto.
case H'6; auto.
Qed.
 
Lemma gcd_rec :
 forall P : nat -> nat -> Set,
 (forall x : nat, P 0 x) ->
 (forall x : nat, P x 0) ->
 (forall a b : nat, P a b -> P a (b + a)) ->
 (forall a b : nat, P a b -> P (a + b) b) -> forall a b : nat, P a b.
intros P H H0 H1 H2 a; pattern a in |- *; apply lt_wf_rec.
intros a' H' b; pattern b in |- *; apply lt_wf_rec.
intros b' H'0.
case (zerop a'); intros lta'; [ rewrite lta'; auto | idtac ].
case (zerop b'); intros ltb'; [ rewrite ltb'; auto | idtac ].
case (lt_eq_lt_dec a' b'); intros Ca'b';
 [ case Ca'b'; clear Ca'b'; intros Ca'b' | idtac ].
replace b' with (b' - a' + a'); auto with arith; rewrite plus_comm;
 auto with arith.
replace b' with (0 + b'); [ rewrite Ca'b' | idtac ]; auto with arith.
replace a' with (a' - b' + b'); auto with arith; rewrite plus_comm;
 auto with arith.
Qed.
 
Lemma gcd_ind :
 forall P : nat -> nat -> Prop,
 (forall x : nat, P 0 x) ->
 (forall x : nat, P x 0) ->
 (forall a b : nat, P a b -> P a (b + a)) ->
 (forall a b : nat, P a b -> P (a + b) b) -> forall a b : nat, P a b.
intros P H H0 H1 H2 a; pattern a in |- *; apply lt_wf_ind.
intros a' H' b; pattern b in |- *; apply lt_wf_ind.
intros b' H'0.
case (zerop a'); intros lta'; [ rewrite lta'; auto | idtac ].
case (zerop b'); intros ltb'; [ rewrite ltb'; auto | idtac ].
case (lt_eq_lt_dec a' b'); intros Ca'b';
 [ case Ca'b'; clear Ca'b'; intros Ca'b' | idtac ].
replace b' with (b' - a' + a'); auto with arith; rewrite plus_comm;
 auto with arith.
replace b' with (0 + b'); [ rewrite Ca'b' | idtac ]; auto with arith.
replace a' with (a' - b' + b'); auto with arith; rewrite plus_comm;
 auto with arith.
Qed.
 
Inductive gcd_spec : nat -> nat -> nat -> Prop :=
  | gcd_spec_ex0 : forall a : nat, gcd_spec a 0 a
  | gcd_spec_ex1 : forall b : nat, gcd_spec 0 b b
  | gcd_spec_ex2 :
      forall a b c : nat, a < b -> gcd_spec a (b - a) c -> gcd_spec a b c
  | gcd_spec_ex3 :
      forall a b c : nat, b <= a -> gcd_spec (a - b) b c -> gcd_spec a b c.
Hint Resolve gcd_spec_ex0 gcd_spec_ex1.
 
Theorem gcd_inv_Or_aux : forall a b c : nat, gcd_spec a b c -> b = 0 -> a = c.
intros a b c H'; elim H'; auto.
intros a0 b0 c0 H'0 H'1 H'2 H'3.
apply H'2; auto.
rewrite H'3; auto.
intros a0 b0 c0 H'0 H'1 H'2 H'3.
replace a0 with (a0 - b0); auto.
rewrite H'3; auto with arith.
Qed.
 
Theorem gcd_inv_Or : forall a b : nat, gcd_spec a 0 b -> a = b.
intros a b H'.
apply gcd_inv_Or_aux with (b := 0); auto.
Qed.
 
Theorem gcd_inv_Ol_aux : forall a b c : nat, gcd_spec a b c -> a = 0 -> b = c.
intros a b c H'; elim H'; auto.
intros a0 b0 c0 H'0 H'1 H'2 H'3.
replace b0 with (b0 - a0); auto.
rewrite H'3; auto with arith.
intros a0 b0 c0 H'0 H'1 H'2 H'3.
apply H'2; auto.
rewrite H'3; auto.
Qed.
 
Theorem gcd_inv_Ol : forall a b : nat, gcd_spec 0 a b -> a = b.
intros a b H'.
apply gcd_inv_Ol_aux with (a := 0); auto.
Qed.
 
Definition gcd' :=
  gcd_rec (fun _ _ : nat => nat) (fun x : nat => x) 
    (fun x : nat => x) (fun x y r : nat => r) (fun x y r : nat => r).
 
Lemma gcd_ex : forall a b : nat, {r : nat | gcd_spec a b r}.
intros a b; pattern b, a in |- *; apply gcd_rec; clear a b.
intros a; exists a; auto.
intros b; exists b; auto.
intros a b Rr; case Rr; intros r Hr; exists r.
apply gcd_spec_ex3; auto with arith.
rewrite plus_comm; rewrite minus_plus; auto; rewrite <- minus_n_n; auto.
intros a b Rr; case Rr; intros r Hr; exists r.
case (zerop a); intros lta.
rewrite lta; simpl in |- *.
rewrite <- (gcd_inv_Or b r); auto.
apply gcd_spec_ex3; auto with arith.
rewrite <- minus_n_n; auto.
rewrite <- lta; auto.
apply gcd_spec_ex2; auto with arith.
pattern b at 1 in |- *; replace b with (0 + b); auto with arith.
rewrite plus_comm; rewrite minus_plus; auto; rewrite <- minus_n_n; auto.
Qed.

(** gcd as a function *) 
Definition gcd (a b : nat) := proj1_sig (gcd_ex a b).
 
Lemma gcd_correct : forall a b : nat, gcd_spec a b (gcd a b).
intros a b; unfold gcd in |- *; case (gcd_ex a b); simpl in |- *; auto.
Qed.
Hint Resolve gcd_correct.
 
Lemma gcd_spec_uniq :
 forall a b r1 r2 : nat, gcd_spec a b r1 -> gcd_spec a b r2 -> r1 = r2.
intros a b r1 r2 H'; generalize r2; elim H'; clear H' a b r1 r2.
exact gcd_inv_Or.
exact gcd_inv_Ol.
intros a b c H' H'0 H'1 r2 H'2; inversion H'2; auto.
apply H'1; auto.
rewrite <- H0; simpl in |- *; rewrite H1; auto.
apply H'1; auto.
rewrite <- H; simpl in |- *; rewrite <- minus_n_O; rewrite H1; auto.
Contradict H; auto with arith.
intros a b c H' H'0 H'1 r2 H'2; inversion H'2; auto.
apply H'1; auto.
rewrite <- H0; simpl in |- *; rewrite H1; rewrite <- minus_n_O; auto.
apply H'1; auto.
rewrite <- H; simpl in |- *; rewrite H1; auto.
Contradict H; auto with arith.
Qed.
 
Lemma gcd_correct2 : forall a b r : nat, gcd_spec a b r -> gcd a b = r.
intros a b r H'.
apply gcd_spec_uniq with (a := a) (b := b); auto.
Qed.
 
Lemma gcd_def0l : forall x : nat, gcd 0 x = x.
intros x; apply gcd_spec_uniq with (a := 0) (b := x); auto.
Qed.
 
Lemma gcd_def0r : forall x : nat, gcd x 0 = x.
intros x; apply gcd_spec_uniq with (a := x) (b := 0); auto.
Qed.
 
Lemma gcd_def1 : forall x : nat, gcd x x = x.
intros x; apply gcd_spec_uniq with (a := x) (b := x); auto.
apply gcd_spec_ex3; auto.
rewrite <- minus_n_n; auto.
Qed.
 
Lemma gcd_def2 : forall a b : nat, gcd a b = gcd a (b + a).
intros a b; apply gcd_spec_uniq with (a := a) (b := b + a); auto.
case (zerop b); intros ltb.
rewrite ltb; simpl in |- *; rewrite gcd_def0r; auto.
apply gcd_spec_ex3; auto.
rewrite <- minus_n_n; auto.
apply gcd_spec_ex2; auto with arith.
replace a with (0 + a); auto with arith.
rewrite plus_comm; rewrite minus_plus.
apply gcd_correct; auto.
Qed.
 
Lemma gcd_def3 : forall a b : nat, gcd a b = gcd (a + b) b.
intros a b; apply gcd_spec_uniq with (a := a + b) (b := b); auto.
case (zerop a); intros lta.
rewrite lta; simpl in |- *; rewrite gcd_def0l; auto.
apply gcd_spec_ex3; auto with arith.
rewrite <- minus_n_n; auto.
apply gcd_spec_ex3; auto with arith.
rewrite plus_comm; rewrite minus_plus.
apply gcd_correct; auto.
Qed.
 
Lemma gcd_is_gcd : forall a b : nat, is_gcd a b (gcd a b).
intros; pattern a, b in |- *; apply gcd_ind; clear a b.
intros x; rewrite gcd_def0l; auto.
apply is_gcd_Or; auto.
intros x; rewrite gcd_def0r; auto.
apply is_gcd_Ol; auto.
intros a b (H1, (H2, H3)); rewrite <- gcd_def2; split; auto; split; auto.
apply divides_plus1; auto.
intros d H' H'0.
apply H3; auto.
apply divides_plus2 with (b := a); auto.
rewrite plus_comm; auto.
intros a b (H1, (H2, H3)); rewrite <- gcd_def3; split; auto.
apply divides_plus1; auto.
split; auto.
intros d H' H'0.
apply H3; auto.
apply divides_plus2 with (b := b); auto.
rewrite plus_comm; auto.
Qed.
 
Theorem is_gcd_inv : forall a b c : nat, is_gcd a (a + b) c -> is_gcd a b c.
intros a b c (H1, (H2, H3)); split; auto; split; auto.
apply divides_plus2 with (2 := H2); auto.
intros d H4 H5; apply H3; auto.
apply divides_plus1; auto.
Qed.
 
Lemma preEuclid :
 forall a b c m : nat,
 divides c (m * a) -> divides c (m * b) -> divides c (m * gcd a b).
intros a b; pattern a, b in |- *; apply gcd_ind; clear a b.
intros x c m H' H'0; rewrite gcd_def0l; auto.
intros x c m H' H'0; rewrite gcd_def0r; auto.
intros a b H' c m H'0 H'1; rewrite <- gcd_def2.
apply H'; auto.
apply divides_plus2 with (m * a); auto.
replace (m * a + m * b) with (m * (b + a)); auto with arith; ring.
intros a b H' c m H'0 H'1; rewrite <- gcd_def3.
apply H'; auto.
apply divides_plus2 with (m * b); auto.
replace (m * b + m * a) with (m * (a + b)); auto with arith; ring.
Qed.
 
Theorem L_Euclides :
 forall x a b : nat, is_gcd x a 1 -> divides x (a * b) -> divides x b.
intros x a b H' H'0; replace b with (b * gcd x a).
apply preEuclid; auto with arith.
exists b; auto with arith.
rewrite mult_comm; auto.
rewrite (is_gcd_unic x a (gcd x a) 1); auto with arith.
apply gcd_is_gcd; auto.
Qed.
 
Lemma L_Euclides1 :
 forall p a b : nat,
 prime p -> divides p (a * b) -> ~ divides p a -> divides p b.
intros; apply L_Euclides with a; auto.
apply is_gcd_sym.
apply prime_gcd; auto.
Qed.
 
Lemma L_Euclides2 :
 forall p a b : nat,
 prime p -> divides p (a * b) -> divides p a \/ divides p b.
intros.
elim (divides_dec p a); [ left | right ]; auto.
apply L_Euclides1 with a; auto.
Qed.
 
Theorem div_power_prime :
 forall p w n : nat, prime p -> divides p (power w n) -> divides p w.
intros p w n; elim n; simpl in |- *; auto.
intros H' (q, H'0).
generalize H' H'0; case q; case p; simpl in |- *; intros; try discriminate.
Contradict H'1; auto with arith.
generalize H'2; case n0; simpl in |- *; auto.
intros n2 H'3; Contradict H'3; auto with arith.
intros n0 H' H'0 H'1.
case (divides_dec p (power w n0)); intros H; auto.
apply L_Euclides1 with (a := power w n0); auto.
rewrite mult_comm; auto.
Qed.
