(***********************************************************************
    Proof of Bertrand's conjecture: PowerBinomial.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)
Require Export PrimeDirac.
Require Import Wf_nat.
Require Import ArithRing.

(** Exact expression for the maximal exponent of binomial 2n n.  *)
 
Theorem power_div_binomial :
 forall n p r : nat,
 prime p ->
 0 < n ->
 2 * n < power p (2 + r) ->
 power_div (binomial (2 * n) n) p =
 sum_nm 1 r (fun x => div (2 * n) (power p x) - 2 * div n (power p x)).
intros n p r H H0 H1.
cut (0 < p); [ intros Hp | apply lt_trans with (2 := lt_prime _ H) ];
 auto with arith.
rewrite <-
 sum_nm_minus
              with
              (f := fun x => div (2 * n) (power p x))
             (g := fun x => 2 * div n (power p x)).
apply plus_minus.
rewrite <- sum_nm_times with (f := fun x : nat => div n (power p x)).
repeat rewrite <- power_div_fact_prime_div; auto with arith.
replace (2 * power_div (factorial n) p) with
 (power_div (factorial n) p + power_div (factorial n) p);
 [ idtac | simpl in |- *; ring ].
repeat rewrite <- power_div_mult_prime; auto with arith.
apply f_equal2 with (f := power_div); auto with arith.
apply sym_equal; replace (2 * n) with (n + n);
 [ rewrite <- binomial_fact | simpl in |- * ]; ring.
replace (2 * n) with (n + n); try apply binomial_lt; auto with arith; ring.
apply le_lt_trans with (2 := H1).
simpl in |- *; auto with arith.
intros x H2 H3.
apply div_mult_le; auto with arith.
apply power_lt_O; auto with arith.
Qed.

(**  Upper bound for p^maxExp(binomial 2n n,p) *)
 
Theorem power_div_binomial1 :
 forall n p : nat,
 prime p -> 0 < n -> power p (power_div (binomial (2 * n) n) p) <= 2 * n.
intros n p H H0.
cut (1 < p); [ intros Hp | apply lt_prime ]; auto.
cut (0 < p); [ intros Hp1 | apply lt_trans with (2 := Hp) ]; auto.
case
 (max_such_prop (fun x : nat => power p x <= 2 * n)
    (fun x => le_dec (power p x) (2 * n)) (2 * n)).
exists 0; simpl in |- *; split; auto with arith.
case
 (max_such (fun x : nat => power p x <= 2 * n)
    (fun x : nat => le_dec (power p x) (2 * n)) (2 * n)); 
 auto.
intros H'2 (H1, H2); apply le_trans with (2 := H1).
apply power_le_mono; auto with arith.
rewrite power_div_binomial with (r := 0); auto with arith.
change (div (2 * n) (power p 1) - 2 * div n (power p 1) <= 0) in |- *.
replace (div (2 * n) (power p 1)) with 0; auto with arith.
apply sym_equal; apply lt_div_O.
apply not_le_lt; apply H2; auto with arith.
apply not_le_lt; apply H2; auto with arith.
replace (2 + 0) with (2 * 1); auto with arith.
intros n1 H'1 (H1, H2); apply le_trans with (2 := H1).
replace (S n1) with (S n1 * 1); auto with arith.
rewrite <- sum_nm_c with (p := 1) (c := 1).
rewrite power_div_binomial with (r := n1); auto with arith.
apply power_le_mono; auto with arith.
apply sum_nm_le; auto with arith.
intros x H3 H4; apply minus_le.
rewrite plus_comm; apply div_mult_lt2; auto with arith.
apply power_lt_O; auto with arith.
case (le_or_lt (2 + n1) (2 * n)); intros Hl.
apply not_le_lt; apply H2; auto with arith.
apply lt_trans with (1 := Hl).
apply power_id_lt; auto with arith.
Qed.

(**  Upper bound for the maximal exponent of (binomial 2n n) 
     in a special case *)
 
Theorem power_div_binomial2 :
 forall n p : nat,
 prime p ->
 0 < n -> 2 * n < power p 2 -> power_div (binomial (2 * n) n) p <= 1.
intros n p H H0 H1; generalize (power_div_binomial1 n p H H0).
case (power_div (binomial (2 * n) n) p); auto with arith.
intros n1; case n1; auto with arith.
intros n2 H2; Contradict H2; auto with arith.
apply lt_not_le; apply lt_le_trans with (power p 2); auto with arith.
apply power_le_mono; auto with arith.
apply lt_trans with 1; auto with arith; apply lt_prime; auto with arith.
Qed.

(**  Exact value of the maximal exponent of (binomial 2n n) 
     in a special case *)
 
Theorem power_div_binomial3 :
 forall n p : nat,
 prime p ->
 2 < n -> 2 * n < 3 * p -> p <= n -> power_div (binomial (2 * n) n) p = 0.
intros n p Hp Hn Hp1 Hp2.
cut (1 < p); [ intros Hp3 | apply lt_prime ]; auto.
cut (0 < p); [ intros Hp4 | apply lt_trans with (2 := Hp3) ]; auto.
rewrite power_div_binomial with (r := 0); auto with arith.
change (div (2 * n) (power p 1) - 2 * div n (power p 1) = 0) in |- *.
repeat rewrite power_SO.
replace (div (2 * n) p) with 2.
replace (div n p) with 1; auto with arith.
apply div_unique; auto with arith.
rewrite mult_1_r; auto.
apply plus_lt_reg_l with (p := p).
apply le_lt_trans with (n + n); auto with arith.
replace (n + n) with (2 * n); auto with arith.
replace (p + p * (1 + 1)) with (3 * p); auto with arith.
rewrite (mult_comm p); simpl in |- *; ring.
simpl in |- *; ring.
apply div_unique; auto with arith.
rewrite (mult_comm p); auto with arith.
replace (p * (1 + 2)) with (3 * p); auto with arith.
apply lt_trans with (2 := Hn); auto.
apply lt_le_trans with (1 := Hp1).
replace (power p (2 + 0)) with (p * p).
case (prime_2_or_more p); auto with arith.
intros H1; Contradict Hp1; auto with arith.
apply le_not_lt.
rewrite (fun x => mult_comm x p); rewrite H1; auto with arith.
repeat rewrite (fun x => mult_comm x p); auto with arith.
simpl in |- *; rewrite mult_1_r; auto.
Qed.


(** Upper bound for (binomial 2n+1 n) *)
 
Theorem binomial_odd :
 forall n : nat, binomial (2 * n + 1) (n + 1) <= power 2 (2 * n).
intros n.
case (le_lt_or_eq 0 n); auto with arith; intros H1.
apply mult_S_le_reg_l with (n := 1).
pattern 2 at 3 in |- *; rewrite <- (power_SO 2).
rewrite power_mult.
rewrite (plus_comm 1).
replace (2 * binomial (2 * n + 1) (n + 1)) with
 (binomial (2 * n + 1) n + binomial (2 * n + 1) (n + 1)).
rewrite binomial2.
rewrite sum_nm_split with (r := pred n).
replace (1 + (0 + pred n)) with n; auto with arith.
replace (2 * n + 1 - (1 + pred n)) with (n + 1); auto with arith.
apply
 le_trans with (sum_nm n (n + 1) (fun x : nat => binomial (2 * n + 1) x));
 auto with arith.
rewrite sum_nm_split with (r := 1).
apply le_trans with (sum_nm n 1 (fun x : nat => binomial (2 * n + 1) x));
 auto with arith.
replace (n + 1) with (S n); simpl in |- *; auto; rewrite plus_comm; auto.
replace 1 with (0 + 1); auto with arith.
simpl in |- *; rewrite <- (S_pred n 0); auto with arith.
apply plus_minus; auto with arith; ring.
simpl in |- *; rewrite <- (S_pred n 0); auto with arith.
apply le_lt_trans with n; auto with arith.
pattern n at 1 in |- *; replace n with (n + 0); auto with arith.
replace (2 * n + 1) with (n + (n + 1)); auto with arith.
simpl in |- *; ring.
replace (2 * n + 1) with (n + (n + 1)); auto with arith.
rewrite (binomial_comp n).
simpl in |- *; ring.
simpl in |- *; ring.
rewrite <- H1; simpl in |- *; auto with arith.
Qed.

(** Lower bound for (binomial 2n n) *)
 
Theorem binomial_even :
 forall n : nat, 0 < n -> power 2 (2 * n) <= 2 * n * binomial (2 * n) n.
intros n Hn.
cut (S (2 * n - 2) = 2 * n - 1);
 [ intros H1
 | generalize Hn; case n; simpl in |- *; auto;
    try (intros H1; inversion H1; fail);
    (intros n1; repeat rewrite <- plus_n_Sm; simpl in |- *;
      rewrite <- minus_n_O) ]; auto.
cut (2 * n - 2 < 2 * n - 1); [ intros H2 | rewrite <- H1; auto with arith ].
cut (S (2 * n - 1) = 2 * n);
 [ intros H3
 | generalize Hn; case n; simpl in |- *; auto;
    try (intros H3; inversion H3; fail); intros n1;
    repeat rewrite <- plus_n_Sm; simpl in |- * ]; auto.
rewrite binomial2.
rewrite sum_nm_split with (r := 0); auto with arith.
repeat rewrite <- plus_n_O.
rewrite sum_nm_split with (p := 1) (r := 2 * n - 2); auto with arith.
replace (1 + (1 + (2 * n - 2))) with (2 * n);
 [ idtac | generalize H1 H3; simpl in |- *; intros H4; rewrite H4; auto ].
replace (2 * n - 1 - (1 + (2 * n - 2))) with 0;
 [ idtac | rewrite <- H1; apply minus_n_n ].
apply le_trans with (1 + (S (2 * n - 2) * binomial (2 * n) n + 1)).
repeat apply plus_le_compat; auto with arith.
case n; simpl in |- *; auto.
rewrite <- sum_nm_c with (c := binomial (2 * n) n) (p := 1).
apply sum_nm_le.
intros x Hx H4.
generalize (S_pred _ _ Hn); intros H5; pattern n at 3 in |- *; rewrite H5.
case (le_or_lt x n); intros H6.
replace x with (S (pred n) - (S (pred n) - x)).
apply binomial_mono.
rewrite H5; auto with arith.
rewrite <- H5; auto with arith.
apply sym_equal; apply plus_minus; auto with arith.
rewrite plus_comm; apply le_plus_minus; auto with arith.
pattern (2 * n) at 1 in |- *; rewrite (le_plus_minus x (2 * n));
 auto with arith.
rewrite binomial_comp with (n := x).
rewrite <- (le_plus_minus x (2 * n)); auto with arith.
replace (2 * n - x) with (S (pred n) - (x - n)).
apply binomial_mono.
rewrite H5; auto with arith.
rewrite <- H5; auto with arith.
apply sym_equal; apply plus_minus; auto with arith.
rewrite <- minus_plus_le.
replace (x + 2 * n) with (n + x + n); auto with arith; ring.
apply lt_le_weak; auto.
apply le_trans with (1 := H4).
rewrite <- S_to_plus_one; rewrite H1; pattern (2 * n) at 2 in |- *;
 rewrite <- H3; auto.
apply le_trans with (1 := H4).
rewrite <- S_to_plus_one; rewrite H1; pattern (2 * n) at 2 in |- *;
 rewrite <- H3; auto.
apply le_trans with (1 := H4).
rewrite <- S_to_plus_one; rewrite H1; pattern (2 * n) at 2 in |- *;
 rewrite <- H3; auto.
simpl in |- *; rewrite binomial_def3; auto with arith.
replace (1 + (S (2 * n - 2) * binomial (2 * n) n + 1)) with
 (2 + S (2 * n - 2) * binomial (2 * n) n); [ idtac | ring ].
rewrite H1.
replace (2 * n * binomial (2 * n) n) with
 (binomial (2 * n) n + (2 * n - 1) * binomial (2 * n) n).
apply plus_le_compat; auto with arith.
generalize Hn; elim n; auto with arith.
intros n1; case n1; auto with arith.
intros n0 H Hn0; replace (2 * S (S n0)) with (S (S (2 * S n0)));
 auto with arith.
2: simpl in |- *; repeat rewrite <- plus_n_Sm; auto.
repeat rewrite binomial_def4; auto with arith.
apply le_plus_trans; rewrite plus_comm; auto with arith.
pattern (2 * n) at 4 in |- *; rewrite <- H3; auto.
Qed.