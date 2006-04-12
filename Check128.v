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
    Proof of Bertrand's conjecture: Check128.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)

Require Export Prime.
Require Export Misc.
Require Import Arith.

(** Check if there is a prime between n and n+m *)

Fixpoint prime_between (n m : nat) {struct m} : bool :=
  if primeb n
  then true
  else match m with
       | O => false
       | S m1 => prime_between (S n) m1
       end.
 
Theorem prime_between_correct :
 forall n m : nat,
 if prime_between n m
 then exists p : nat, prime p /\ n <= p /\ p <= n + m
 else forall p : nat, n <= p -> p <= n + m -> ~ prime p.

intros n m; generalize n; clear n; elim m; clear m; simpl in |- *; auto.
intros n; generalize (primeb_correct n); case (primeb n); auto.
intros H; exists n; repeat (split; auto with arith).
rewrite <- plus_n_O; auto with arith.
intros H p H0 H1; replace p with n; auto with arith.
intros m Rec n; generalize (primeb_correct n); case (primeb n); auto.
intros H; exists n; repeat (split; auto with arith).
intros H; generalize (Rec (S n)); case (prime_between (S n) m);
 auto with arith.
simpl in |- *; rewrite <- plus_n_Sm; intros (p, (H1, (H2, H3))); exists p;
 repeat (split; auto with arith).
simpl in |- *; rewrite <- plus_n_Sm; intros H1 p H2; inversion H2;
 auto with arith.
rewrite <- H0; auto.
Qed.
 

(** Bertrand's postulat is decidable *)

Theorem postulate_dec :
 forall n : nat,
 {(exists p : nat, prime p /\ n < p /\ p < 2 * n)} +
 {(forall p : nat, n < p -> p < 2 * n -> ~ prime p)}.
intros n; case n.
right; simpl in |- *; intros p H1 H2; inversion H2.
intros n1; case n1.
right; simpl in |- *; intros p H1; inversion H1; auto with arith.
intros H2; Contradict H2; auto with arith.
intros H2; inversion H2; auto with arith.
inversion H4; auto.
inversion H6.
intros n2; generalize (prime_between_correct (S (S (S n2))) n2);
 case (prime_between (S (S (S n2))) n2).
intros H0; left; case H0; intros p (H1, (H2, H3)); exists p;
 repeat (split; auto with arith).
simpl in |- *; repeat rewrite <- plus_n_Sm || rewrite <- plus_n_O;
 auto with arith.
intros H0; right; intros p H1 H2; apply H0; auto with arith.
generalize H2; simpl in |- *;
 repeat rewrite <- plus_n_Sm || rewrite <- plus_n_O; 
 auto with arith.
Qed.
 
(** Check the postulate from 2 to n *)

Fixpoint check_postulate (n : nat) : bool :=
  match n with
  | O => true
  | S n1 =>
      match n1 with
      | O => true
      | S n2 =>
          match prime_between (S n) n2 with
          | true => check_postulate n1
          | false => false
          end
      end
  end.
 
Theorem check_postulate_correct :
 forall m : nat,
 check_postulate m = true ->
 forall n : nat,
 2 <= n -> n <= m -> exists p : nat, prime p /\ n < p /\ p < 2 * n.
intros m; elim m; simpl in |- *; auto.
intros H n H0 H1; generalize H0; inversion H1; auto.
intros H3; inversion H3.
clear m; intros m; case m; clear m.
intros H H0 n; case n; auto with arith.
intros n1; case n1; auto with arith.
intros n0 H1 H2; inversion H2.
inversion H4.
intros n H;
 (generalize (prime_between_correct (S (S (S n))) n);
   case (prime_between (S (S (S n))) n)).
intros H0 H1 n0 H2 H3; inversion H3; auto with arith.
case H0; auto; intros p1 (H5, (H6, H7));
 (exists p1; repeat (split; auto with arith)).
repeat rewrite <- plus_n_Sm || rewrite <- plus_n_O; auto with arith.
intros; discriminate.
Qed.

(** Check the postulate from 1 to 128 *)
 
Theorem postulate_correct_128 :
 forall n : nat,
 2 <= n -> n <= power 2 7 -> exists p : nat, prime p /\ n < p /\ p < 2 * n.
apply check_postulate_correct.
vm_compute;reflexivity.
Qed.
