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
    Proof of Bertrand's conjecture: Div.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)
Require Export Power.
Require Import ArithRing.
Require Export Arith.
Require Export Divides.
Require Import Misc.
(** Auxillary function to compute the quotient and rest of a division *)
 
Fixpoint pdiv_aux (m n p : nat) {struct p} : nat * nat :=
  match ominus m n with
  | None => (0, m)
  | Some m1 =>
      match p with
      | O => (m, n)
      | S p1 => match pdiv_aux m1 n p1 with
                | (q, r) => (S q, r)
                end
      end
  end.
 
Theorem ominus_id : forall n : nat, ominus n n = Some 0.
simple induction n; auto.
Qed.
 
Theorem pdiv_aux_def :
 forall m n p : nat,
 m <= p ->
 0 < n -> match pdiv_aux m n p with
          | (q, r) => m = q * n + r /\ r < n
          end.
intros m n p; generalize m n; clear m n; elim p; clear p; simpl in |- *.
intros m n H; inversion H; simpl in |- *; case n; simpl in |- *;
 auto with arith.
intros p1 Rec m n H1 H2.
generalize (ominus_def m n); case (ominus m n); auto with arith.
intros s Hs; generalize (Rec s n); case (pdiv_aux s n p1).
intros q r H3; case H3; auto with arith.
apply lt_n_Sm_le.
apply lt_le_trans with (2 := H1).
rewrite Hs.
pattern s at 1 in |- *; replace s with (0 + s); auto with arith.
intros H4 H5; split; auto.
rewrite Hs; rewrite H4; simpl in |- *; auto with arith.
Qed.
(** Function that computes quotient and rest of a division *)
 
Definition pdiv (m n : nat) := pdiv_aux m n m.
 
Theorem pdiv_def :
 forall m n : nat,
 0 < n -> match pdiv m n with
          | (q, r) => m = q * n + r /\ r < n
          end.
intros m n H; unfold pdiv in |- *; apply pdiv_aux_def with (p := m);
 auto with arith.
Qed.
(* Division : returns the quotient *)
 
Definition div (m n : nat) := fst (pdiv m n).
 
Theorem div_le : forall m n : nat, 0 < n -> n * div m n <= m.
intros m n H; unfold div in |- *; generalize (pdiv_def m n H);
 case (pdiv m n); simpl in |- *.
intros q r (H1, H2); rewrite H1; auto with arith.
rewrite (mult_comm n); auto with arith.
Qed.
 
Theorem div_lt : forall m n : nat, 0 < n -> m < n * (1 + div m n).
intros m n H; unfold div in |- *; generalize (pdiv_def m n H);
 case (pdiv m n); simpl in |- *.
intros q r (H1, H2); rewrite H1; auto with arith.
rewrite (mult_comm n); simpl in |- *; auto with arith.
rewrite (plus_comm n); simpl in |- *; auto with arith.
Qed.
 
Theorem div_unique :
 forall m n p : nat, 0 < n -> n * p <= m -> m < n * (1 + p) -> p = div m n.
intros m n p H H0 H1.
case (le_or_lt p (div m n)); intros H2.
case (le_lt_or_eq _ _ H2); intros H3; auto.
absurd (n * div m n <= m).
apply lt_not_le; apply lt_le_trans with (1 := H1); auto with arith.
apply div_le; auto.
absurd (m < n * (1 + div m n)).
apply le_not_lt; apply le_trans with (2 := H0); auto with arith.
apply div_lt; auto.
Qed.
 
Theorem div_mult_le :
 forall m n p : nat, 0 < n -> p * div m n <= div (p * m) n.
intros m n p H1.
apply lt_n_Sm_le; change (p * div m n < 1 + div (p * m) n) in |- *.
apply lt_mult_right_anti with (z := n).
apply le_lt_trans with (p * m).
replace (n * (p * div m n)) with (p * (n * div m n));
 [ idtac | repeat rewrite mult_assoc; rewrite (mult_comm p); auto ].
apply (fun m n p : nat => mult_le_compat_l p n m).
apply div_le; auto.
apply div_lt; auto.
Qed.
 
Theorem div_mult_lt :
 forall m n p : nat, 0 < n -> 0 < p -> div (p * m) n < p * (1 + div m n).
intros m n p H H1; apply lt_mult_right_anti with (z := n).
apply le_lt_trans with (p * m).
apply div_le; auto.
replace (n * (p * (1 + div m n))) with (p * (n * (1 + div m n)));
 [ idtac | repeat rewrite mult_assoc; rewrite (mult_comm p); auto ].
apply mult_lt_bis; try apply div_lt; auto.
Qed.
(* Correspond to Proposition 1 of page 1 *)
 
Theorem div_mult_lt2 :
 forall m n p : nat, 0 < n -> div (2 * m) n <= 2 * div m n + 1.
intros m n p H.
apply lt_n_Sm_le.
replace (S (2 * div m n + 1)) with (2 * (1 + div m n));
 [ apply div_mult_lt
 | repeat (rewrite <- plus_n_O || rewrite <- plus_n_Sm; simpl in |- *) ];
 auto.
Qed.
 
Theorem div_divides_S :
 forall p q : nat, 0 < q -> divides q (S p) -> div (S p) q = S (div p q).
intros p q H (qr, H1); apply sym_equal; auto.
apply trans_equal with qr.
generalize (pdiv_def p q H); unfold div in |- *; case (pdiv p q);
 simpl in |- *.
intros q1 r1 (H2, H3).
apply eq_mult with q; auto with arith.
apply sym_not_equal; auto with arith.
repeat rewrite (mult_comm q); auto with arith.
rewrite <- H1; rewrite H2.
cut (S r1 = q); [ intros H4 | idtac ].
rewrite plus_n_Sm; rewrite H4; simpl in |- *; ring.
apply le_antisym; auto with arith.
apply divides_le; auto with arith.
apply divides_plus2 with (b := q1 * q).
exists q1; auto with arith.
rewrite <- plus_n_Sm; rewrite <- H2; auto.
rewrite H1; exists qr; auto.
apply div_unique; auto with arith.
rewrite H1; rewrite (mult_comm q); auto with arith.
rewrite H1; repeat rewrite (mult_comm qr); auto with arith.
Qed.
 
Theorem div_not_divides_S :
 forall p q : nat, 0 < q -> ~ divides q (S p) -> div (S p) q = div p q.
intros p q H H1; apply sym_equal; apply div_unique; auto.
apply le_trans with p; auto with arith.
apply div_le; auto with arith.
generalize (pdiv_def p q H); unfold div in |- *; case (pdiv p q);
 simpl in |- *.
intros q1 r1 (H2, H3).
rewrite H2.
rewrite plus_n_Sm; auto.
rewrite <- mult_n_Sm; auto.
repeat rewrite (mult_comm q); auto with arith.
apply plus_lt_compat_l; auto with arith.
case (le_lt_or_eq (S r1) q); auto.
intros H4; case H1; exists (S q1).
rewrite H2.
rewrite plus_n_Sm; auto.
rewrite H4; simpl in |- *; ring.
Qed.
 
Theorem divides_pdiv :
 forall p q : nat, 0 < q -> divides q p -> snd (pdiv p q) = 0.
intros p q H (q1, H1); generalize (pdiv_def p q H); case (pdiv p q);
 simpl in |- *.
intros q2 r2 (H2, H3).
apply (div_unic_r p q q2 q1); split; auto.
rewrite H1; ring.
Qed.
 
Theorem not_divides_pdiv :
 forall p q : nat, 0 < q -> ~ divides q p -> snd (pdiv p q) <> 0.
intros p q H; generalize (pdiv_def p q H); case (pdiv p q); simpl in |- *.
intros q1 r1 (H1, H2) H3; red in |- *; intros H4; case H3; exists q1;
 rewrite H1; rewrite H4; ring.
Qed.
 
Theorem pdiv_divides :
 forall n m : nat, 0 < m -> snd (pdiv n m) = 0 -> divides m n.
intros n m H; generalize (pdiv_def n m H); case (pdiv n m); simpl in |- *.
intros n1 m1 (H1, H2) H3; exists n1; rewrite H1; rewrite H3;
 rewrite <- plus_n_O; auto.
Qed.
 
Theorem pdiv_not_divides :
 forall n m : nat, 0 < m -> snd (pdiv n m) <> 0 -> ~ divides m n.
intros n m H H0; red in |- *; intros H1; case H0; apply divides_pdiv; auto.
Qed.
(* Divisibility is decidable *)
 
Definition divides1_dec : forall n m : nat, {divides n m} + {~ divides n m}.
intros n m; case n.
case m.
left; exists 0; auto.
intros n1; right; red in |- *; intros (x, H1); rewrite mult_comm in H1;
 discriminate.
intros n1; generalize (pdiv_divides m (S n1));
 generalize (pdiv_not_divides m (S n1)); case (pdiv m (S n1)); 
 simpl in |- *.
intros p q; case q.
intros H1 H2; left; auto with arith.
intros q1 H1 H2; right; auto with arith.
Defined.
 
Theorem divides_div :
 forall p q : nat, 0 < p -> divides p q -> q = div q p * p.
intros p q Hp (x, H); rewrite H.
apply f_equal2 with (f := mult); auto with arith.
apply div_unique; auto with arith.
rewrite (mult_comm x); auto with arith.
rewrite (mult_comm x); auto with arith.
Qed.
 
Theorem lt_div_O : forall p q : nat, p < q -> div p q = 0.
intros p q H.
generalize (pdiv_def p q); unfold div in |- *; case (pdiv p q); simpl in |- *.
intros q1 r1; case q1; simpl in |- *; auto with arith.
intros n H0; (absurd (q <= p); auto with arith).
case H0; auto with arith.
apply le_lt_trans with (2 := H); auto with arith.
intros H1 H2; rewrite H1; auto with arith.
Qed.
