Require Export Relation_Operators.
Require Export Lexicographic_Product.
Require Export Prime.
Require Export Div.
Require Export ZArith.
Require Export Zwf.

(** ZxZ *)
 
Definition prodZZ := {x_ : Z &  Z}.
(** Pair *)
 
Definition pairZ (x y : Z) : prodZZ := existS (fun _ : Z => Z) x y.
(** Lexicographic of pair of elements of Z *)
 
Definition lexZ := lexprod Z (fun _ : Z => Z) (Zwf 0) (fun _ : Z => Zwf 0).
(* Prime for Z *)
 
Definition Zprime (z : Z) := (0 < z)%Z /\ prime (Zabs_nat z).
(* Odd for Z *)
 
Definition Zodd (z : Z) := exists x : Z, z = (2 * x + 1)%Z.
(* Division *)
 
Definition Zdivides (z1 z2 : Z) := divides (Zabs_nat z1) (Zabs_nat z2).
(* Square root *)
 
Definition sqr (z : Z) := Z_of_nat (sqr (Zabs_nat z)).
(* One *)
 
Definition one (b : bool) := match b with
                             | true => 1%Z
                             | false => 0%Z
                             end.
(* * Modulo*)
 
Definition mod_ (z1 z2 : Z) :=
  Z_of_nat (snd (pdiv (Zabs_nat z1) (Zabs_nat z2))).
 
Definition eq_bool := eq (A:=bool).
 
Theorem INV_inv_eq : forall p : nat, Z_of_nat p = 0%Z -> p = 0.
intros p; case p; simpl in |- *; auto; intros; discriminate.
Qed.
 
Theorem Zlt_inv_mult :
 forall p q r : Z, (0 <= p)%Z -> (p * q < p * r)%Z -> (q < r)%Z.
intros p q r H H1; case (Zle_or_lt r q); auto with zarith.
intros H2; Contradict H1; auto with zarith.
apply Zle_not_lt; apply Zmult_le_compat_l; auto with zarith.
Qed.
 
Theorem Zlt_inv_square :
 forall p q : Z, (0 <= p)%Z -> (0 <= q)%Z -> (p * p < q * q)%Z -> (p < q)%Z.
intros p q H H1 H2; case (Zle_or_lt q p); auto with zarith.
intros H3; Contradict H2; auto with zarith.
apply Zle_not_lt; apply Zle_trans with (p * q)%Z; auto with zarith.
Qed.
 
Theorem Zle_inv_square :
 forall p q : Z, (0 <= p)%Z -> (0 <= q)%Z -> (p * p <= q * q)%Z -> (p <= q)%Z.
intros p q H H1 H2; case (Zle_or_lt p q); auto with zarith.
intros H3; Contradict H2; auto with zarith.
apply Zlt_not_le; apply Zle_lt_trans with (q * p)%Z; auto with zarith.
apply Zmult_gt_0_lt_compat_r; auto with zarith.
Qed.
 
Theorem convert_not_O : forall p : positive, nat_of_P p <> 0.
intros p; elim p.
intros p0 H'; unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6.
generalize H'; case (nat_of_P p0); auto.
intros p0 H'; unfold nat_of_P in |- *; simpl in |- *; rewrite ZL6.
generalize H'; case (nat_of_P p0); simpl in |- *; auto.
unfold nat_of_P in |- *; simpl in |- *; auto with arith.
Qed.
 
Theorem inj_abs : forall x : Z, (0 <= x)%Z -> Z_of_nat (Zabs_nat x) = x.
intros x; elim x; auto.
unfold Zabs_nat in |- *.
intros p.
pattern p at 1 3 in |- *;
 rewrite <- (pred_o_P_of_succ_nat_o_nat_of_P_eq_id p).
generalize (convert_not_O p); case (nat_of_P p); simpl in |- *;
 auto with arith.
intros H'; case H'; auto.
intros n H' H'0; rewrite Ppred_succ; auto.
intros p H'; Contradict H'; auto.
Qed.
 
Theorem le_Zle_inv : forall n m : nat, (Z_of_nat n <= Z_of_nat m)%Z -> n <= m.
intros n m H'; case (le_or_lt n m); auto.
intros H'0; Contradict H'; auto with arith.
apply Zlt_not_le; auto with arith.
apply Znat.inj_lt; auto with zarith.
Qed.
 
Theorem lt_Zlt_inv : forall n m : nat, (Z_of_nat n < Z_of_nat m)%Z -> n < m.
intros n m H'; case (le_or_lt m n); auto.
intros H'0; Contradict H'; auto with arith.
apply Zle_not_lt; auto with arith.
apply Znat.inj_le; auto with zarith.
Qed.
 
Theorem inject_nat_eq : forall x y : nat, Z_of_nat x = Z_of_nat y -> x = y.
intros x y H'; apply le_antisym; apply le_Zle_inv; rewrite H';
 auto with zarith.
Qed.
 
Theorem absolu_INR : forall n : nat, Zabs_nat (Z_of_nat n) = n.
intros n; case n; simpl in |- *; auto with arith.
intros n0; rewrite nat_of_P_o_P_of_succ_nat_eq_succ; auto with arith.
Qed.
 
Theorem absolu_comp_mult :
 forall p q : Z, Zabs_nat (p * q) = Zabs_nat p * Zabs_nat q.
intros p q; case p; case q; simpl in |- *; auto; intros p0 p1;
 apply
  ((fun (x y : positive) (_ : positive -> positive) =>
    nat_of_P_mult_morphism x y) p1 p0 (fun x => x)).
Qed.