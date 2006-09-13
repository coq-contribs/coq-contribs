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
    Proof of Bertrand's conjecture: Summation.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)

Require Import Arith.
Require Import ArithRing.
Require Export Misc.

(**  	Iterated Sum: 
         (sum_nm n m) = f(n)+f(n+1)+...+f(n+m+1) 
*)
 
Fixpoint sum_nm (n m : nat) {struct m} : (nat -> nat) -> nat :=
  fun f : nat -> nat =>
  match m with
  | O => f n
  | S m' => f n + sum_nm (S n) m' f
  end.
 
Lemma sum_nm_i :
 forall (m n : nat) (f : nat -> nat),
 sum_nm n (S m) f = f n + sum_nm (S n) m f.
auto.
Qed.
 
Lemma sum_nm_f :
 forall (n m : nat) (f : nat -> nat),
 sum_nm n (S m) f = sum_nm n m f + f (n + S m).
intros n m; generalize n; clear n; elim m; simpl in |- *; auto with arith.
intros n f; repeat rewrite (fun x y => plus_comm x (S y)); simpl in |- *;
 auto.
intros n Rec m' f.
rewrite Rec; repeat (rewrite (plus_comm m'); simpl in |- *); auto with arith.
Qed.
 
Lemma sum_nm_ext :
 forall (n m : nat) (f g : nat -> nat),
 (forall x : nat, x <= m -> f (n + x) = g (n + x)) ->
 sum_nm n m f = sum_nm n m g.
intros n m; generalize n; clear n; elim m; simpl in |- *; auto.
intros n f g H0; generalize (H0 0); rewrite plus_comm; simpl in |- *;
 auto with arith.
intros m' Rec n f g H0.
rewrite (Rec (S n) f g).
generalize (H0 0); rewrite plus_comm; simpl in |- *; intros tmp;
 auto with arith.
intros x H'; simpl in |- *; rewrite plus_n_Sm; auto with arith.
Qed.
 
Lemma sum_nm_add :
 forall (n m : nat) (f g : nat -> nat),
 sum_nm n m f + sum_nm n m g = sum_nm n m (fun i : nat => f i + g i).
intros n m f g; generalize n; clear n; elim m; simpl in |- *; auto.
intros m' Rec n.
rewrite <- Rec.
ring.
Qed.
 
Lemma sum_nm_times :
 forall (n m x : nat) (f : nat -> nat),
 x * sum_nm n m f = sum_nm n m (fun i : nat => x * f i).
intros n m x f; generalize n; clear n; elim m; simpl in |- *; auto.
intros m' Rec n.
rewrite <- Rec; auto with arith.
ring.
Qed.
 
Lemma inv_sum_nm :
 forall (P : nat -> Prop) (n i : nat) (f : nat -> nat),
 (forall a b : nat, P a -> P b -> P (a + b)) ->
 (forall x : nat, x <= i -> P (f (n + x))) -> P (sum_nm n i f).
intros P n i f; generalize n; clear n; elim i; simpl in |- *; auto.
intros n H H0; generalize (H0 0); rewrite plus_comm; simpl in |- *;
 auto with arith.
intros i' Rec n Pi Hx.
apply Pi; auto.
generalize (Hx 0); rewrite plus_comm; simpl in |- *; intros tmp;
 auto with arith.
apply Rec; auto.
intros x H'; simpl in |- *; rewrite plus_n_Sm; auto with arith.
Qed.
 
Lemma t_sum_Svars :
 forall (n m : nat) (f : nat -> nat),
 sum_nm n m f = sum_nm (S n) m (fun i : nat => f (pred i)).
intros n m f; generalize n; clear n; elim m; simpl in |- *; auto.
Qed.

Theorem sum_nm_split :
 forall (f : nat -> nat) (p q r : nat),
 r < q -> sum_nm p q f = sum_nm p r f + sum_nm (1 + (p + r)) (q - (1 + r)) f.
intros f p q; elim q.
intros r H; inversion H; simpl in |- *.
intros n H r H0; inversion H0.
rewrite sum_nm_f.
rewrite <- minus_n_n; rewrite <- plus_n_Sm; simpl in |- *; auto.
rewrite sum_nm_f; rewrite (H r); auto with arith.
rewrite <- minus_Sn_m; auto with arith.
rewrite sum_nm_f; auto with arith.
replace (1 + (p + r) + S (n - (1 + r))) with (p + S n); auto with arith.
rewrite minus_Sn_m; auto with arith.
replace (1 + (p + r) + (S n - (1 + r))) with (p + (1 + r + (S n - (1 + r))));
 [ idtac | ring ].
rewrite <- le_plus_minus; auto with arith.
Qed.
 
Theorem sum_nm_c : forall c p q : nat, sum_nm p q (fun x => c) = S q * c.
intros c p q; generalize p; elim q; clear p q; simpl in |- *; auto.
Qed.

Theorem sum_nm_sum_nm_f :
 forall (i j k l : nat) (f : nat -> nat -> nat),
 sum_nm i j (fun x => sum_nm k (S l) (fun y => f x y)) =
 sum_nm i j (fun x => sum_nm k l (fun y => f x y) + f x (k + S l)).
intros; apply sum_nm_ext; intros; rewrite sum_nm_f; auto.
Qed.
 
Theorem sum_nm_com :
 forall (i j k l : nat) (f : nat -> nat -> nat),
 sum_nm i j (fun x => sum_nm k l (fun y => f x y)) =
 sum_nm k l (fun y => sum_nm i j (fun x => f x y)).
intros i j; elim j.
simpl in |- *; auto.
intros j1 Rec; intros k l; case l.
simpl in |- *; auto.
intros l1 f; repeat rewrite sum_nm_f || rewrite sum_nm_sum_nm_f.
rewrite <-
 sum_nm_add
            with
            (f := fun x => sum_nm k l1 (fun y : nat => f x y))
           (g := fun x => f x (k + S l1)).
rewrite (Rec k l1).
(* pre V8.1 only: rewrite sum_nm_sum_nm_f with (f := fun x y => f y x). *)
rewrite <-
 sum_nm_add
            with
            (f := fun x => sum_nm i j1 (fun y : nat => f y x))
           (g := fun x => f (i + S j1) x).
replace
 (sum_nm k l1 (fun y : nat => sum_nm i j1 (fun x : nat => f x y)) +
  sum_nm i j1 (fun x : nat => f x (k + S l1)) +
  (sum_nm k l1 (fun y : nat => f (i + S j1) y) + f (i + S j1) (k + S l1)))
 with
 (sum_nm k l1 (fun y : nat => sum_nm i j1 (fun x : nat => f x y)) +
  sum_nm k l1 (fun y : nat => f (i + S j1) y) +
  (sum_nm i j1 (fun x : nat => f x (k + S l1)) + f (i + S j1) (k + S l1))).
auto.
ring; auto.
Qed.

 
Theorem sum_nm_le :
 forall (n m : nat) (f g : nat -> nat),
 (forall x : nat, n <= x -> x <= n + m -> f x <= g x) ->
 sum_nm n m f <= sum_nm n m g.
intros n m f g; generalize n; elim m; clear n m.
simpl in |- *; auto with arith.
intros m H n H0; repeat rewrite sum_nm_f; auto with arith.
apply plus_le_compat; auto with arith.
apply H; auto with arith.
intros x H1 H2; apply H0; auto with arith.
apply le_trans with (1 := H2); auto with arith.
Qed.

Theorem sum_nm_minus :
 forall (n m : nat) (f g : nat -> nat),
 (forall x : nat, n <= x -> x <= n + m -> g x <= f x) ->
 sum_nm n m f - sum_nm n m g = sum_nm n m (fun x => f x - g x).
intros n m f g; generalize n; elim m; clear n m.
simpl in |- *; auto.
intros m H n H0; try assumption.
repeat rewrite sum_nm_f.
rewrite minus_plus_le; auto with arith.
rewrite H; auto.
intros x H1 H2; apply H0; auto with arith.
apply le_trans with (1 := H2); auto with arith.
apply sum_nm_le; auto.
intros x H1 H2; apply H0; auto with arith.
apply le_trans with (1 := H2); auto with arith.
Qed.
