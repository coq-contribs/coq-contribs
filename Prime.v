(***********************************************************************
    Proof of Bertrand's conjecture: Prime.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)
Require Export Divides.
Require Import Arith.
Require Import ArithRing.
Require Import Wf_nat.
Require Import Div.

(** Definition of the prime predicate *)
Definition prime (a : nat) : Prop :=
  a <> 1 /\ (forall b : nat, divides b a -> b <> 1 -> a = b).
 
Lemma not_prime_O : ~ prime 0.
red in |- *; intros (H1, H2).
absurd (0 = 2); auto with arith.
apply H2; auto.
apply all_divides_O.
Qed.
 
Lemma not_prime_1 : ~ prime 1.
red in |- *; intros (H1, H2); auto.
Qed.
Hint Resolve div_ref all_divides_O SO_divides_all not_prime_O not_prime_1.
 
Lemma lt_prime : forall p : nat, prime p -> 1 < p.
intros p; case p.
intros H1; Contradict H1; auto.
intros n; case n; auto with arith.
intros H1; Contradict H1; auto.
Qed.
 
Lemma prime_2_or_more : forall p : nat, prime p -> p = 2 \/ 2 < p.
intros p H; case (lt_prime p H); auto with arith.
Qed.
 
(** Find the maximal divisor of n *)
Definition max_div (n : nat) :=
  match n with
  | O => 1
  | S O => 1
  | S (S n1) =>
      max_such (fun x => divides x n) (fun x => divides1_dec x n) (S n1)
  end.
 
Theorem max_div_prop1 : forall n : nat, divides (max_div n) n.
intros n; case n.
exists 0; ring.
intros n1; case n1.
exists 1; ring.
intros n2; unfold max_div in |- *;
 case
  (max_such_prop (fun x : nat => divides x (S (S n2)))
     (fun x : nat => divides1_dec x (S (S n2))) (S n2)); 
 auto.
exists 1; split; auto with arith.
intros H (H0, H1); auto.
Qed.
 
Theorem max_div_prop2 :
 forall n p : nat, max_div n < p -> p < n -> ~ divides p n.
intros n; case n.
intros p H1 H2; inversion H2.
intros n1; case n1.
intros p H1 H2; inversion H2.
red in |- *; intros (x, H3).
rewrite mult_comm in H3; discriminate.
inversion H0.
intros n2; unfold max_div in |- *;
 case
  (max_such_prop (fun x : nat => divides x (S (S n2)))
     (fun x : nat => divides1_dec x (S (S n2))) (S n2)); 
 auto.
exists 1; split; auto with arith.
intros H (H0, H'0) p H1 H2; apply H'0; auto with arith.
Qed.
 
Theorem max_div_prop3 : forall n : nat, 1 < n -> max_div n < n.
intros n; case n.
intros H1; inversion H1.
intros n1; case n1.
simpl in |- *; auto with arith.
intros n2; unfold max_div in |- *;
 case
  (max_such_prop (fun x : nat => divides x (S (S n2)))
     (fun x : nat => divides1_dec x (S (S n2))) (S n2)); 
 auto.
exists 1; split; auto with arith.
intros H H0 H1; auto with arith.
Qed.
 
(** Check if a number is prime *)

Definition primeb (n : nat) : bool :=
  match n with
  | O => false
  | S O => false
  | S (S n1) => match max_div n with
                | S O => true
                | _ => false
                end
  end.
 
Theorem primeb_correct :
 forall n : nat, if primeb n then prime n else ~ prime n.
intros n; case n; auto with arith.
simpl in |- *; auto with arith.
intros n1; case n1; auto with arith.
simpl in |- *; auto with arith.
intros n2; generalize (max_div_prop1 (S (S n2)));
 generalize (max_div_prop2 (S (S n2))); generalize (max_div_prop3 (S (S n2)));
 unfold primeb in |- *; case (max_div (S (S n2))).
intros H' H (x, H0); rewrite mult_comm in H0; discriminate.
intros n3; case n3.
intros H' H H0; split; auto with arith.
intros b; case b.
intros (x, H1); rewrite mult_comm in H1; discriminate.
intros n0 H1 H2; case (le_lt_or_eq (S n0) (S (S n2))); auto.
apply divides_le; auto with arith.
intros H3; case (H (S n0)); auto with arith.
generalize H2; case n0; simpl in |- *; auto with arith.
intros H4; case H4; auto.
intros n0 H H0 H1; red in |- *; intros (H2, H4).
absurd (S (S n2) <= S (S n0)); auto with arith.
rewrite (H4 (S (S n0))); auto.
Qed.
 
Definition prime_dec : forall n : nat, {prime n} + {~ prime n}.
intros n; generalize (primeb_correct n); case (primeb n).
intros H1; left; auto.
intros H1; right; auto.
Defined.
 
Theorem divides_prime_divides :
 forall n : nat, 1 < n -> exists p : nat, prime p /\ divides p n.
intros n; pattern n in |- *; apply lt_wf_ind.
clear n; intros n Rec H1.
case (le_or_lt (max_div n) 1); intros H2.
exists n; split; auto with arith.
split; auto with arith.
Contradict H1; rewrite H1; auto with arith.
intros b H H0.
cut (0 <> b); [ intros H4 | idtac ].
case (le_lt_or_eq b n); auto with arith.
apply divides_le; auto with arith.
Contradict H1; rewrite H1; auto with arith.
intros H3; Contradict H.
apply max_div_prop2; auto with arith.
apply le_lt_trans with (1 := H2); auto with arith.
generalize H0 H4; case b; auto with arith.
intros HH1 HH2; case HH2; auto.
intros n1; case n1; auto with arith.
intros HH1; case HH1; auto with arith.
Contradict H1; case H; intros x H3; rewrite H3; rewrite <- H1;
 rewrite mult_comm; auto with arith.
case (Rec (max_div n)); auto with arith.
apply max_div_prop3; auto with arith.
intros x (H3, H4); exists x; split; auto.
apply divides_trans with (1 := H4).
apply max_div_prop1; auto with arith.
Qed.
 
Theorem prime_def1 :
 forall n : nat,
 1 < n -> (forall p : nat, prime p -> p * p <= n -> ~ divides p n) -> prime n.
intros n H H0; split; auto with arith.
Contradict H; rewrite H; auto with arith.
intros b (x, H1) H2.
case (le_or_lt x b); intros H3.
case (le_or_lt x 1); intros H4.
case (le_lt_or_eq _ _ H4); intros H5.
case (le_lt_or_eq x 0); auto with arith; intros H6.
inversion H6.
Contradict H; rewrite H1; rewrite H6; auto with arith.
rewrite H1; rewrite H5; auto with arith.
case (divides_prime_divides x); auto with arith.
intros y (H5, H6); case (H0 y); auto with arith.
cut (y <= x); [ intros H7 | apply divides_le ]; auto.
apply le_trans with (x * y); auto with arith.
apply le_mult; auto with arith.
rewrite H1; auto with arith.
apply le_mult; auto with arith.
apply le_trans with (1 := H7); auto.
Contradict H4; rewrite H4; auto with arith.
apply divides_trans with (1 := H6); exists b; auto with arith.
rewrite mult_comm; auto.
case (divides_prime_divides b); auto with arith.
generalize H2 H; rewrite H1; case b; auto with arith.
intros H4; rewrite mult_comm; intros H5; Contradict H5; auto with arith.
intros n1; case n1; auto with arith.
intros H4; case H4; auto with arith.
intros y (H5, H6); case (H0 y); auto with arith.
cut (y <= b); [ intros H7 | apply divides_le ]; auto.
apply le_trans with (x * y); auto with arith.
apply le_mult; auto with arith.
apply le_trans with (1 := H7); auto with arith.
rewrite H1; auto with arith.
Contradict H; rewrite H1; rewrite H; rewrite mult_comm; auto with arith.
apply divides_trans with (1 := H6).
exists x; auto with arith.
Qed.

Theorem prime_div_prime :
 forall p n : nat, p < n -> prime p -> divides p n -> ~ prime n.
intros p n H1 H2 H3; red in |- *; intros (H4, H5).
Contradict H1; rewrite (H5 p); auto with arith.
Contradict H2; rewrite H2; auto with arith.
Qed.