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
    Proof of Bertrand's conjecture: DivDirac.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)
Require Import ArithRing.
Require Export Div.
Require Import Summation.

(** Define a function that returns 1 if the second argument divides the 
    first one, 0 otherwise*)
 
Definition div_dirac (p q : nat) :=
  match snd (pdiv p q) with
  | O => 1
  | _ => 0
  end.
 
Theorem div_dirac_prop1 :
 forall p q : nat, 0 < q -> divides q p -> div_dirac p q = 1.
intros p q H H1; unfold div_dirac in |- *; rewrite divides_pdiv; auto.
Qed.
 
Theorem div_dirac_prop2 :
 forall p q : nat, 0 < q -> ~ divides q p -> div_dirac p q = 0.
intros p q H H1; unfold div_dirac in |- *;
 generalize (not_divides_pdiv p q H H1); case (snd (pdiv p q));
 auto with arith.
intros H2; case H2; auto.
Qed.
 
Theorem div_dirac_div :
 forall p q : nat,
 0 < p -> 0 < q -> div p q = sum_nm 1 (pred p) (fun x => div_dirac x q).
intros p q H H0; generalize H; clear H.
elim p; auto with arith.
intros H1; inversion H1.
intros n1; case n1.
2: intros n H H1.
2: replace (pred (S (S n))) with (S (pred (S n))); auto with arith.
2: rewrite sum_nm_f.
2: case (divides_dec q (S (S n))); intros H2.
2: rewrite div_divides_S; auto with arith.
2: rewrite H; auto with arith.
2: rewrite div_dirac_prop1; auto with arith.
2: ring.
2: rewrite div_not_divides_S; auto with arith.
2: rewrite H; auto with arith.
2: rewrite div_dirac_prop2; auto with arith.
simpl in |- *.
generalize H0; case q; simpl in |- *.
intros H1; inversion H1.
intros n2; case n2.
unfold div in |- *; unfold div_dirac in |- *; simpl in |- *; auto.
unfold div in |- *; unfold div_dirac in |- *; simpl in |- *; auto.
Qed.
