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


Require Import Knuth_def.
Require Import Bertrand.

Require Import WhyArrays.
Require Import Zwf.
Implicit Arguments well_founded [A].

(*Why*) Parameter n : Z.

 
Inductive In (v : Z) (t : array Z) (l u : Z) : Prop :=
    In_cons :
      forall i : Z, (l <= i)%Z /\ (i < u)%Z -> access t i = v -> In v t l u.
 

(* Why obligation from file "Knuth.mlw", characters 468-477 *)
Lemma Prime_po_1 :
 forall (a : array Z) (Pre10 : (n > 0)%Z /\ array_length a = n) 
   (m0 : Z) (Post1 : m0 = 3%Z) (i0 : Z) (Post2 : i0 = 1%Z),
 (0 <= 0)%Z /\ (0 < array_length a)%Z.
Proof.
simpl in |- *; auto with zarith.
Qed.
 
(* Why obligation from file "Knuth.mlw", characters 481-1499 *)
Lemma Prime_po_2 :
 forall (a : array Z) (Pre10 : (n > 0)%Z /\ array_length a = n) 
   (m0 : Z) (Post1 : m0 = 3%Z) (i0 : Z) (Post2 : i0 = 1%Z)
   (Pre9 : (0 <= 0)%Z /\ (0 < array_length a)%Z) (a0 : array Z)
   (Post3 : a0 = store a 0 2%Z), well_founded lexZ.
Proof.
intros a Pre10 m0 Post1 i0 Post2 Pre9 a0 Post3.
unfold lexZ in |- *; apply wf_lexprod; try intros H; apply Zwf_well_founded.
Qed.
 
(* Why obligation from file "Knuth.mlw", characters 1068-1073 *)
Lemma Prime_po_3 :
 forall (a : array Z) (Pre10 : (n > 0)%Z /\ array_length a = n) 
   (m0 : Z) (Post1 : m0 = 3%Z) (i0 : Z) (Post2 : i0 = 1%Z)
   (Pre9 : (0 <= 0)%Z /\ (0 < array_length a)%Z) (a0 : array Z)
   (Post3 : a0 = store a 0 2%Z) (Variant1 : prodZZ) 
   (a1 : array Z) (i1 m1 : Z)
   (Pre8 : Variant1 = pairZ (n - i1) (2 * access a1 (i1 - 1) - m1))
   (Pre7 : ((access a1 (i1 - 1) < m1)%Z /\ (m1 < 2 * access a1 (i1 - 1))%Z) /\
           ((0 < i1)%Z /\ (i1 <= n)%Z) /\
           Zodd m1 /\
           (forall k : Z,
            (access a1 (i1 - 1) < k)%Z /\ (k < m1)%Z -> ~ Zprime k) /\
           (forall k : Z, (0 <= k)%Z /\ (k < i1)%Z -> Zprime (access a1 k)) /\
           (forall k j : Z,
            (0 <= k)%Z /\ (k < j)%Z /\ (j < i1)%Z ->
            (access a1 k < access a1 j)%Z) /\
           (forall k : Z,
            (0 <= k)%Z /\ (k <= access a1 (i1 - 1))%Z /\ Zprime k ->
            In k a1 0 i1) /\ array_length a1 = n) (Test8 : (i1 < n)%Z)
   (b1 : bool) (Post4 : b1 = true) (s1 : Z) (Post5 : s1 = sqr m1) 
   (j1 : Z) (Post6 : j1 = 0%Z) (Variant3 : Z) (b2 : bool) 
   (j2 : Z) (Pre5 : Variant3 = (one b2 + i1 - j2)%Z)
   (Pre4 : (if b2
            then
             forall k : Z,
             (0 <= k)%Z /\ (k < j2)%Z -> ~ Zdivides (access a1 k) m1
            else Zdivides (access a1 j2) m1) /\ (0 <= j2)%Z /\ (j2 < i1)%Z)
   (Test3 : true = b2), (0 <= j2)%Z /\ (j2 < array_length a1)%Z.
Proof.
intros; intuition.
Qed.
 
(* Why obligation from file "Knuth.mlw", characters 1068-1079 *)
Lemma Prime_po_4 :
 forall (a : array Z) (Pre10 : (n > 0)%Z /\ array_length a = n) 
   (m0 : Z) (Post1 : m0 = 3%Z) (i0 : Z) (Post2 : i0 = 1%Z)
   (Pre9 : (0 <= 0)%Z /\ (0 < array_length a)%Z) (a0 : array Z)
   (Post3 : a0 = store a 0 2%Z) (Variant1 : prodZZ) 
   (a1 : array Z) (i1 m1 : Z)
   (Pre8 : Variant1 = pairZ (n - i1) (2 * access a1 (i1 - 1) - m1))
   (Pre7 : ((access a1 (i1 - 1) < m1)%Z /\ (m1 < 2 * access a1 (i1 - 1))%Z) /\
           ((0 < i1)%Z /\ (i1 <= n)%Z) /\
           Zodd m1 /\
           (forall k : Z,
            (access a1 (i1 - 1) < k)%Z /\ (k < m1)%Z -> ~ Zprime k) /\
           (forall k : Z, (0 <= k)%Z /\ (k < i1)%Z -> Zprime (access a1 k)) /\
           (forall k j : Z,
            (0 <= k)%Z /\ (k < j)%Z /\ (j < i1)%Z ->
            (access a1 k < access a1 j)%Z) /\
           (forall k : Z,
            (0 <= k)%Z /\ (k <= access a1 (i1 - 1))%Z /\ Zprime k ->
            In k a1 0 i1) /\ array_length a1 = n) (Test8 : (i1 < n)%Z)
   (b1 : bool) (Post4 : b1 = true) (s1 : Z) (Post5 : s1 = sqr m1) 
   (j1 : Z) (Post6 : j1 = 0%Z) (Variant3 : Z) (b2 : bool) 
   (j2 : Z) (Pre5 : Variant3 = (one b2 + i1 - j2)%Z)
   (Pre4 : (if b2
            then
             forall k : Z,
             (0 <= k)%Z /\ (k < j2)%Z -> ~ Zdivides (access a1 k) m1
            else Zdivides (access a1 j2) m1) /\ (0 <= j2)%Z /\ (j2 < i1)%Z)
   (Test3 : true = b2) (result7 : bool)
   (Bool2 : if result7 then (access a1 j2 <= s1)%Z else (access a1 j2 > s1)%Z),
 if result7
 then true = b2 /\ (access a1 j2 <= s1)%Z \/ false = b2 /\ true = false
 else true = b2 /\ (access a1 j2 > s1)%Z \/ false = b2 /\ false = false.
Proof.
intros a Pre10 m0 Post1 i0 Post2 Pre9 a0 Post3 Variant1 a1 i1 m1 Pre8 Pre7
 Test10 b1 Post4 s1 Post5 j1 Post6 Variant3 b2 j2 Pre5 Pre4 Test3 result7.
case result7; auto.
Qed.
 
(* Why obligation from file "Knuth.mlw", characters 1062-1079 *)
Lemma Prime_po_5 :
 forall (a : array Z) (Pre10 : (n > 0)%Z /\ array_length a = n) 
   (m0 : Z) (Post1 : m0 = 3%Z) (i0 : Z) (Post2 : i0 = 1%Z)
   (Pre9 : (0 <= 0)%Z /\ (0 < array_length a)%Z) (a0 : array Z)
   (Post3 : a0 = store a 0 2%Z) (Variant1 : prodZZ) 
   (a1 : array Z) (i1 m1 : Z)
   (Pre8 : Variant1 = pairZ (n - i1) (2 * access a1 (i1 - 1) - m1))
   (Pre7 : ((access a1 (i1 - 1) < m1)%Z /\ (m1 < 2 * access a1 (i1 - 1))%Z) /\
           ((0 < i1)%Z /\ (i1 <= n)%Z) /\
           Zodd m1 /\
           (forall k : Z,
            (access a1 (i1 - 1) < k)%Z /\ (k < m1)%Z -> ~ Zprime k) /\
           (forall k : Z, (0 <= k)%Z /\ (k < i1)%Z -> Zprime (access a1 k)) /\
           (forall k j : Z,
            (0 <= k)%Z /\ (k < j)%Z /\ (j < i1)%Z ->
            (access a1 k < access a1 j)%Z) /\
           (forall k : Z,
            (0 <= k)%Z /\ (k <= access a1 (i1 - 1))%Z /\ Zprime k ->
            In k a1 0 i1) /\ array_length a1 = n) (Test8 : (i1 < n)%Z)
   (b1 : bool) (Post4 : b1 = true) (s1 : Z) (Post5 : s1 = sqr m1) 
   (j1 : Z) (Post6 : j1 = 0%Z) (Variant3 : Z) (b2 : bool) 
   (j2 : Z) (Pre5 : Variant3 = (one b2 + i1 - j2)%Z)
   (Pre4 : (if b2
            then
             forall k : Z,
             (0 <= k)%Z /\ (k < j2)%Z -> ~ Zdivides (access a1 k) m1
            else Zdivides (access a1 j2) m1) /\ (0 <= j2)%Z /\ (j2 < i1)%Z)
   (Test2 : false = b2) (result7 : bool) (Post10 : result7 = false),
 if result7
 then true = b2 /\ (access a1 j2 <= s1)%Z \/ false = b2 /\ true = false
 else true = b2 /\ (access a1 j2 > s1)%Z \/ false = b2 /\ false = false.
Proof.
intros a Pre10 m0 Post1 i0 Post2 Pre9 a0 Post3 Variant1 a1 i1 m1 Pre8 Pre7
 Test10 b1 Post4 s1 Post5 j1 Post6 Variant3 b2 j2 Pre5 Pre4 Test2 result7
 Post10.
rewrite Post10; auto.
Qed.
 
(* Why obligation from file "Knuth.mlw", characters 1337-1345 *)
Lemma Prime_po_6 :
 forall (a : array Z) (Pre10 : (n > 0)%Z /\ array_length a = n) 
   (m0 : Z) (Post1 : m0 = 3%Z) (i0 : Z) (Post2 : i0 = 1%Z)
   (Pre9 : (0 <= 0)%Z /\ (0 < array_length a)%Z) (a0 : array Z)
   (Post3 : a0 = store a 0 2%Z) (Variant1 : prodZZ) 
   (a1 : array Z) (i1 m1 : Z)
   (Pre8 : Variant1 = pairZ (n - i1) (2 * access a1 (i1 - 1) - m1))
   (Pre7 : ((access a1 (i1 - 1) < m1)%Z /\ (m1 < 2 * access a1 (i1 - 1))%Z) /\
           ((0 < i1)%Z /\ (i1 <= n)%Z) /\
           Zodd m1 /\
           (forall k : Z,
            (access a1 (i1 - 1) < k)%Z /\ (k < m1)%Z -> ~ Zprime k) /\
           (forall k : Z, (0 <= k)%Z /\ (k < i1)%Z -> Zprime (access a1 k)) /\
           (forall k j : Z,
            (0 <= k)%Z /\ (k < j)%Z /\ (j < i1)%Z ->
            (access a1 k < access a1 j)%Z) /\
           (forall k : Z,
            (0 <= k)%Z /\ (k <= access a1 (i1 - 1))%Z /\ Zprime k ->
            In k a1 0 i1) /\ array_length a1 = n) (Test8 : (i1 < n)%Z)
   (b1 : bool) (Post4 : b1 = true) (s1 : Z) (Post5 : s1 = sqr m1) 
   (j1 : Z) (Post6 : j1 = 0%Z) (Variant3 : Z) (b2 : bool) 
   (j2 : Z) (Pre5 : Variant3 = (one b2 + i1 - j2)%Z)
   (Pre4 : (if b2
            then
             forall k : Z,
             (0 <= k)%Z /\ (k < j2)%Z -> ~ Zdivides (access a1 k) m1
            else Zdivides (access a1 j2) m1) /\ (0 <= j2)%Z /\ (j2 < i1)%Z)
   (Test7 : true = b2 /\ (access a1 j2 <= s1)%Z \/ false = b2 /\ true = false)
   (Test6 : mod_ m1 (access a1 j2) = 0%Z) (b3 : bool) 
   (Post7 : b3 = false),
 ((if b3
   then forall k : Z, (0 <= k)%Z /\ (k < j2)%Z -> ~ Zdivides (access a1 k) m1
   else Zdivides (access a1 j2) m1) /\ (0 <= j2)%Z /\ (j2 < i1)%Z) /\
 Zwf 0 (one b3 + i1 - j2) (one b2 + i1 - j2).
Proof.
intros a Pre10 m0 Post1 i0 Post2 Pre9 a0 Post3 Variant1 a1 i1 m1 Pre8 Pre7
 Test10 b1 Post4 s1 Post5 j1 Post6 Variant3 b2 j2 Pre5 Pre4 Test7 Test6 b3
 Post8.
rewrite Post8; case Test7; intros (H1, H2); try discriminate; rewrite <- H1.
rewrite <- H1 in Pre5; repeat split; auto with zarith.
unfold Zdivides in |- *; apply pdiv_divides.
replace 0 with (Zabs_nat 0); auto with zarith.
apply Zabs.Zabs_nat_lt; split; auto with zarith.
cut (Zprime (access a1 j2)); [ intros H3; case H3; auto | intuition ].
apply INV_inv_eq; auto.
intuition.
replace (one true) with 1%Z; auto with zarith.
replace (one true) with 1%Z; auto with zarith.
replace (one true) with 1%Z; auto with zarith.
replace (one false) with 0%Z; auto with zarith.
Qed.
 
(* Why obligation from file "Knuth.mlw", characters 1370-1381 *)
Lemma Prime_po_7 :
 forall (a : array Z) (Pre10 : (n > 0)%Z /\ array_length a = n) 
   (m0 : Z) (Post1 : m0 = 3%Z) (i0 : Z) (Post2 : i0 = 1%Z)
   (Pre9 : (0 <= 0)%Z /\ (0 < array_length a)%Z) (a0 : array Z)
   (Post3 : a0 = store a 0 2%Z) (Variant1 : prodZZ) 
   (a1 : array Z) (i1 m1 : Z)
   (Pre8 : Variant1 = pairZ (n - i1) (2 * access a1 (i1 - 1) - m1))
   (Pre7 : ((access a1 (i1 - 1) < m1)%Z /\ (m1 < 2 * access a1 (i1 - 1))%Z) /\
           ((0 < i1)%Z /\ (i1 <= n)%Z) /\
           Zodd m1 /\
           (forall k : Z,
            (access a1 (i1 - 1) < k)%Z /\ (k < m1)%Z -> ~ Zprime k) /\
           (forall k : Z, (0 <= k)%Z /\ (k < i1)%Z -> Zprime (access a1 k)) /\
           (forall k j : Z,
            (0 <= k)%Z /\ (k < j)%Z /\ (j < i1)%Z ->
            (access a1 k < access a1 j)%Z) /\
           (forall k : Z,
            (0 <= k)%Z /\ (k <= access a1 (i1 - 1))%Z /\ Zprime k ->
            In k a1 0 i1) /\ array_length a1 = n) (Test8 : (i1 < n)%Z)
   (b1 : bool) (Post4 : b1 = true) (s1 : Z) (Post5 : s1 = sqr m1) 
   (j1 : Z) (Post6 : j1 = 0%Z) (Variant3 : Z) (b2 : bool) 
   (j2 : Z) (Pre5 : Variant3 = (one b2 + i1 - j2)%Z)
   (Pre4 : (if b2
            then
             forall k : Z,
             (0 <= k)%Z /\ (k < j2)%Z -> ~ Zdivides (access a1 k) m1
            else Zdivides (access a1 j2) m1) /\ (0 <= j2)%Z /\ (j2 < i1)%Z)
   (Test7 : true = b2 /\ (access a1 j2 <= s1)%Z \/ false = b2 /\ true = false)
   (Test5 : mod_ m1 (access a1 j2) <> 0%Z) (j3 : Z) 
   (Post8 : j3 = (j2 + 1)%Z),
 ((if b2
   then forall k : Z, (0 <= k)%Z /\ (k < j3)%Z -> ~ Zdivides (access a1 k) m1
   else Zdivides (access a1 j3) m1) /\ (0 <= j3)%Z /\ (j3 < i1)%Z) /\
 Zwf 0 (one b2 + i1 - j3) (one b2 + i1 - j2).
Proof.
intros a Pre10 m0 Post1 i0 Post2 Pre9 a0 Post3 Variant1 a1 i1 m1 Pre8 Pre7
 Test10 b1 Post4 s1 Post5 j1 Post6 Variant3 b2 j2 Pre5 Pre4 Test7 Test5 j3
 Post9.
case Test7; intros (H1, H2); try discriminate.
rewrite <- H1; repeat split; auto with zarith.
intros k; rewrite Post9; intros (H3, H4).
case (Zle_lt_or_eq k j2); auto with zarith; intros H7.
rewrite <- H1 in Pre4; case Pre4; auto with zarith.
rewrite H7.
unfold Zdivides in |- *; apply pdiv_not_divides; auto with zarith.
replace 0 with (Zabs_nat 0); auto with zarith.
apply Zabs.Zabs_nat_lt; split; auto with zarith.
cut (Zprime (access a1 j2)); [ intros (H5, H6); auto | intuition ].
Contradict Test5; unfold mod_ in |- *; rewrite Test5; auto with zarith.
rewrite Post9; auto with zarith.
case (Zle_lt_or_eq j2 (i1 - 1)); auto with zarith; intros H3.
absurd (access a1 j2 <= s1)%Z; auto with zarith.
apply Zlt_not_le.
rewrite H3; rewrite Post5.
apply Zlt_inv_square; auto with zarith.
unfold sqr in |- *; auto with zarith.
apply Zlt_le_trans with (2 * access a1 (i1 - 1))%Z; auto with zarith.
apply Zle_lt_trans with m1; auto with zarith.
unfold sqr in |- *.
rewrite <- Znat.inj_mult.
pattern m1 at 3 in |- *; rewrite <- inj_abs; auto with zarith arith.
apply Znat.inj_le; auto with arith.
apply sqr_le.
replace (one true) with 1%Z; auto with zarith.
Qed.
 
(* Why obligation from file "Knuth.mlw", characters 1109-1265 *)
Lemma Prime_po_8 :
 forall (a : array Z) (Pre10 : (n > 0)%Z /\ array_length a = n) 
   (m0 : Z) (Post1 : m0 = 3%Z) (i0 : Z) (Post2 : i0 = 1%Z)
   (Pre9 : (0 <= 0)%Z /\ (0 < array_length a)%Z) (a0 : array Z)
   (Post3 : a0 = store a 0 2%Z) (Variant1 : prodZZ) 
   (a1 : array Z) (i1 m1 : Z)
   (Pre8 : Variant1 = pairZ (n - i1) (2 * access a1 (i1 - 1) - m1))
   (Pre7 : ((access a1 (i1 - 1) < m1)%Z /\ (m1 < 2 * access a1 (i1 - 1))%Z) /\
           ((0 < i1)%Z /\ (i1 <= n)%Z) /\
           Zodd m1 /\
           (forall k : Z,
            (access a1 (i1 - 1) < k)%Z /\ (k < m1)%Z -> ~ Zprime k) /\
           (forall k : Z, (0 <= k)%Z /\ (k < i1)%Z -> Zprime (access a1 k)) /\
           (forall k j : Z,
            (0 <= k)%Z /\ (k < j)%Z /\ (j < i1)%Z ->
            (access a1 k < access a1 j)%Z) /\
           (forall k : Z,
            (0 <= k)%Z /\ (k <= access a1 (i1 - 1))%Z /\ Zprime k ->
            In k a1 0 i1) /\ array_length a1 = n) (Test8 : (i1 < n)%Z)
   (b1 : bool) (Post4 : b1 = true) (s1 : Z) (Post5 : s1 = sqr m1) 
   (j1 : Z) (Post6 : j1 = 0%Z),
 (if b1
  then forall k : Z, (0 <= k)%Z /\ (k < j1)%Z -> ~ Zdivides (access a1 k) m1
  else Zdivides (access a1 j1) m1) /\ (0 <= j1)%Z /\ (j1 < i1)%Z.
Proof.
intros until b1; intro Post4; rewrite Post4; intuition.
Qed.
 
(* Why obligation from file "Knuth.mlw", characters 1406-1408 *)
Lemma Prime_po_9 :
 forall (a : array Z) (Pre10 : (n > 0)%Z /\ array_length a = n) 
   (m0 : Z) (Post1 : m0 = 3%Z) (i0 : Z) (Post2 : i0 = 1%Z)
   (Pre9 : (0 <= 0)%Z /\ (0 < array_length a)%Z) (a0 : array Z)
   (Post3 : a0 = store a 0 2%Z) (Variant1 : prodZZ) 
   (a1 : array Z) (i1 m1 : Z)
   (Pre8 : Variant1 = pairZ (n - i1) (2 * access a1 (i1 - 1) - m1))
   (Pre7 : ((access a1 (i1 - 1) < m1)%Z /\ (m1 < 2 * access a1 (i1 - 1))%Z) /\
           ((0 < i1)%Z /\ (i1 <= n)%Z) /\
           Zodd m1 /\
           (forall k : Z,
            (access a1 (i1 - 1) < k)%Z /\ (k < m1)%Z -> ~ Zprime k) /\
           (forall k : Z, (0 <= k)%Z /\ (k < i1)%Z -> Zprime (access a1 k)) /\
           (forall k j : Z,
            (0 <= k)%Z /\ (k < j)%Z /\ (j < i1)%Z ->
            (access a1 k < access a1 j)%Z) /\
           (forall k : Z,
            (0 <= k)%Z /\ (k <= access a1 (i1 - 1))%Z /\ Zprime k ->
            In k a1 0 i1) /\ array_length a1 = n) (Test8 : (i1 < n)%Z)
   (b1 : bool) (Post4 : b1 = true) (s1 : Z) (Post5 : s1 = sqr m1) 
   (j1 : Z) (Post6 : j1 = 0%Z) (b2 : bool) (j2 : Z)
   (Post12 : ((if b2
               then
                forall k : Z,
                (0 <= k)%Z /\ (k < j2)%Z -> ~ Zdivides (access a1 k) m1
               else Zdivides (access a1 j2) m1) /\ 
              (0 <= j2)%Z /\ (j2 < i1)%Z) /\
             (true = b2 /\ (access a1 j2 > s1)%Z \/
              false = b2 /\ false = false)),
 if b2
 then
  (forall a : array Z,
   a = store a1 i1 m1 ->
   forall i : Z,
   i = (i1 + 1)%Z ->
   forall m : Z,
   m = (m1 + 2)%Z ->
   (((access a (i - 1) < m)%Z /\ (m < 2 * access a (i - 1))%Z) /\
    ((0 < i)%Z /\ (i <= n)%Z) /\
    Zodd m /\
    (forall k : Z, (access a (i - 1) < k)%Z /\ (k < m)%Z -> ~ Zprime k) /\
    (forall k : Z, (0 <= k)%Z /\ (k < i)%Z -> Zprime (access a k)) /\
    (forall k j : Z,
     (0 <= k)%Z /\ (k < j)%Z /\ (j < i)%Z -> (access a k < access a j)%Z) /\
    (forall k : Z,
     (0 <= k)%Z /\ (k <= access a (i - 1))%Z /\ Zprime k -> In k a 0 i) /\
    array_length a = n) /\
   lexZ (pairZ (n - i) (2 * access a (i - 1) - m))
     (pairZ (n - i1) (2 * access a1 (i1 - 1) - m1))) /\
  (0 <= i1)%Z /\ (i1 < array_length a1)%Z
 else
  forall m : Z,
  m = (m1 + 2)%Z ->
  (((access a1 (i1 - 1) < m)%Z /\ (m < 2 * access a1 (i1 - 1))%Z) /\
   ((0 < i1)%Z /\ (i1 <= n)%Z) /\
   Zodd m /\
   (forall k : Z, (access a1 (i1 - 1) < k)%Z /\ (k < m)%Z -> ~ Zprime k) /\
   (forall k : Z, (0 <= k)%Z /\ (k < i1)%Z -> Zprime (access a1 k)) /\
   (forall k j : Z,
    (0 <= k)%Z /\ (k < j)%Z /\ (j < i1)%Z -> (access a1 k < access a1 j)%Z) /\
   (forall k : Z,
    (0 <= k)%Z /\ (k <= access a1 (i1 - 1))%Z /\ Zprime k -> In k a1 0 i1) /\
   array_length a1 = n) /\
  lexZ (pairZ (n - i1) (2 * access a1 (i1 - 1) - m))
    (pairZ (n - i1) (2 * access a1 (i1 - 1) - m1)).
Proof.
intros a Pre10 m0 Post1 i0 Post2 Pre9 a0 Post3 Variant1 a1 i1 m1 Pre8 Pre7
 Test10 b1 Post4 s1 Post5 j1 Post6.
simple destruct b2.
(* b2=true *)
intros j2 Post12. split.
intros a2 Post13 i2 Post14 m H1; rewrite Post13; rewrite Post14; rewrite H1;
 try
  (replace (i1 + 1 - 1)%Z with i1; [ idtac | ring ]; rewrite store_def_1;
    auto with zarith).
cut (Zprime m1); [ intros Zm1 | idtac ].
split.
split; auto with zarith.
split; auto with zarith.
split; auto with zarith.
cut (Zodd m1); [ intros H2; case H2; intros x H3 | intuition ].
exists (x + 1)%Z; rewrite H3; auto with zarith.
split.
intros k (H2, H3); replace k with (m1 + 1)%Z; auto with zarith.
red in |- *; intros (H4, H5); Contradict H5.
replace (Zabs_nat (m1 + 1)) with (S (Zabs_nat m1)).
apply prime_not_prime_S; auto with zarith.
case (prime_2_or_more (Zabs_nat (access a1 (i1 - 1)))).
case Pre7; intros H5 (H6, (H7, (H8, (H9, H10)))); case (H9 (i1 - 1)%Z);
 auto with zarith.
intros H5; rewrite <- H5.
apply lt_Zlt_inv; repeat rewrite inj_abs; auto with zarith.
intros H5; apply lt_trans with (1 := H5).
apply lt_Zlt_inv; repeat rewrite inj_abs; auto with zarith.
case Zm1; auto.
apply inject_nat_eq; rewrite Znat.inj_S.
repeat rewrite inj_abs; auto with zarith.
split; auto with zarith.
intros k (H2, H3).
case (Zle_lt_or_eq k i1); auto with zarith; intros H4.
rewrite store_def_2; auto with zarith; intuition.
rewrite H4; rewrite store_def_1; auto with zarith.
split; auto with zarith.
intros k j (H2, (H3, H4)).
case (Zle_lt_or_eq j i1); auto with zarith; intros H5.
repeat rewrite store_def_2; auto with zarith; intuition.
rewrite H5; rewrite store_def_1; auto with zarith.
rewrite store_def_2; auto with zarith.
rewrite H5 in H3; case (Zle_lt_or_eq k (i1 - 1)); auto with zarith; intros HH.
apply Zlt_trans with (access a1 (i1 - 1)).
case Pre7; intros H6 (H7, (H8, (H9, (H10, (H11, H12))))).
apply H11; repeat split; auto with zarith.
intuition.
rewrite HH; intuition.
split.
intros k (H2, (H3, H4)).
case (Zle_lt_or_eq k m1); auto with zarith; intros H5.
case (Zle_or_lt k (access a1 (i1 - 1))); intros H6.
case Pre7; intros H7 (H8, (H9, (H10, (H11, (H12, (H13, H13a)))))).
case (H13 k); auto with zarith.
intros i (H14, H15) H16; apply In_cons with (i := i); auto with zarith.
rewrite <- H16; apply store_def_2; auto with zarith.
Contradict H4.
case Pre7; intros H7 (H8, (H9, (H10, H11))); auto with zarith.
rewrite H5; apply In_cons with (i := i1); auto with zarith.
apply store_def_1; auto with zarith.
simpl in |- *; intuition.
unfold lexZ, pairZ in |- *; apply left_lex; auto with zarith.
split; auto with zarith.
split; auto with zarith.
apply prime_def1.
apply le_lt_trans with (Zabs_nat (access a1 (i1 - 1))); auto with zarith.
apply le_Zle_inv.
simpl in |- *; rewrite inj_abs; auto with zarith.
apply lt_Zlt_inv.
repeat rewrite inj_abs; auto with zarith.
intros p H5 H6.
cut (Z_of_nat p < access a1 j2)%Z; [ intros H7 | idtac ].
cut (Z_of_nat p < access a1 (i1 - 1))%Z; [ intros H8 | idtac ].
rewrite <- (absolu_INR p).
change (~ Zdivides (Z_of_nat p) m1) in |- *.
cut (In (Z_of_nat p) a1 0 i1); [ intros H9 | idtac ].
inversion H9.
rewrite <- H0.
case Post12; intros (H10, H11) [(H12, H13)| (H12, H13)]; try discriminate.
apply H10; split; auto with zarith.
cut (access a1 i < access a1 j2)%Z; [ intros H14 | idtac ].
case (Zle_or_lt j2 i); auto; intros H15; case (Zle_lt_or_eq _ _ H15);
 intros H16.
Contradict H14; apply Zle_not_lt; apply Zlt_le_weak.
intuition.
Contradict H14; rewrite H16; auto with zarith.
rewrite H0; auto.
case Pre7; intros H11 (H12, (H13, (H14, (H15, (H16, (H17, H17a)))))).
apply H17.
split; auto with zarith.
split; auto with zarith.
split; auto with zarith.
generalize H5; case p; simpl in |- *; auto with zarith.
intros H18; Contradict H18; auto with arith.
unfold Zlt in |- *; auto.
rewrite absolu_INR; auto.
apply Zlt_le_trans with (1 := H7); auto with zarith.
case (Zle_lt_or_eq j2 (i1 - 1)); auto with zarith; intros H8.
apply Zlt_le_weak; intuition.
rewrite H8; auto with zarith.
apply Zle_lt_trans with s1; auto with zarith.
replace (Z_of_nat p) with (Z_of_nat (Misc.sqr (p * p))).
rewrite Post5; unfold sqr in |- *.
apply Znat.inj_le; auto with arith; apply sqr_mono; auto with arith.
rewrite sqr_mult2; auto.
case Post12; intros (H10, H11) [(H12, H13)| (H12, H13)]; try discriminate;
 auto with zarith.
omega.
(* b2 = false *)
intros j2 Post12. split.
case Post12; intros (H1, H2) [(H3, H4)| (H3, H4)]; try discriminate.
split; auto with zarith.
split; auto with zarith.
case (Bertrand (Zabs_nat (access a1 (i1 - 1)))).
case (prime_2_or_more (Zabs_nat (access a1 (i1 - 1)))); auto with arith.
cut (Zprime (access a1 (i1 - 1))); [ intros HH; case HH | intuition ];
 auto with zarith.
intros HH; rewrite HH; auto with zarith.
intros x (H5, (H6, H7)).
case (Zle_or_lt (2 * access a1 (i1 - 1)) (m1 + 2)); auto.
intros H8; absurd (Zprime (Z_of_nat x)); auto with zarith.
case Pre7; intros (H9, H9') (H10, (H11, (H12, H13))).
apply H12; split; auto with zarith.
rewrite <- (inj_abs (access a1 (i1 - 1))); auto with zarith.
case (Zle_lt_or_eq (Z_of_nat x) m1); auto with zarith.
case (Zle_lt_or_eq (Z_of_nat x) (m1 + 1)); auto with zarith.
apply Zlt_succ_le.
apply Zlt_le_trans with (2 * access a1 (i1 - 1))%Z; auto with zarith.
rewrite <- (inj_abs (2 * access a1 (i1 - 1))); auto with zarith.
rewrite absolu_comp_mult.
replace (Zabs_nat 2) with 2; auto with zarith.
apply Znat.inj_lt; auto.
intros H14; absurd (Zprime (Z_of_nat x)).
rewrite H14.
red in |- *; intros (H15, H16); Contradict H16.
apply prime_div_prime with (p := Zabs_nat 2).
apply lt_Zlt_inv; repeat rewrite inj_abs; auto with zarith.
exact (primeb_correct 2).
case H11; intros y H16.
exists (Zabs_nat (y + 1)).
rewrite H16.
rewrite <- absolu_comp_mult.
replace (2 * y + 1 + 1)%Z with ((y + 1) * 2)%Z; auto with zarith.
split; auto with zarith.
rewrite absolu_INR; auto.
intros H14; absurd (Zprime (Z_of_nat x)).
rewrite H14.
red in |- *; intros (H15, H16); Contradict H16.
apply prime_div_prime with (p := Zabs_nat (access a1 j2)); auto with zarith.
apply lt_Zlt_inv; repeat rewrite inj_abs; auto with zarith.
apply Zle_lt_trans with (2 := H9).
case (Zle_lt_or_eq j2 (i1 - 1)); auto with zarith; intros H16.
apply Zlt_le_weak.
case H13; intros H17 (H18, H19).
apply H18; auto with zarith.
rewrite H16; auto with zarith.
cut (Zprime (access a1 j2)); [ intros (H16, H17) | intuition ];
 auto with zarith.
cut (Zprime (access a1 j2)); [ intros (H16, H17) | intuition ];
 auto with zarith.
split; auto with zarith.
rewrite absolu_INR; auto.
split; auto with zarith.
rewrite absolu_INR; auto.
rewrite <- H; auto.
split; auto with zarith.
split; auto with zarith.
cut (Zodd m1); [ intros (x, H5) | intuition ].
exists (x + 1)%Z; auto with zarith.
split; auto with zarith.
intros k (H5, H6).
case (Zle_lt_or_eq k (m1 + 1)); auto with zarith; intros H7.
case (Zle_lt_or_eq k m1); auto with zarith; intros H8.
case Pre7; intros H9 (H10, (H11, (H12, H13))); apply H12; auto with zarith.
rewrite H8; auto.
intros (H9, H10); Contradict H10.
apply prime_div_prime with (p := Zabs_nat (access a1 j2)); auto with zarith.
apply lt_Zlt_inv; repeat rewrite inj_abs; auto with zarith.
rewrite <- H8; apply Zle_lt_trans with (2 := H5).
case (Zle_lt_or_eq j2 (i1 - 1)); auto with zarith; intros H10.
apply Zlt_le_weak.
case Pre7; intros H11 (H12, (H13, (H14, (H15, (H16, H17))))); apply H16;
 auto with zarith.
rewrite H10; auto with zarith.
cut (Zprime (access a1 j2)); [ intros (H16, H17) | intuition ];
 auto with zarith.
cut (Zprime (access a1 j2)); [ intros (H16, H17) | intuition ];
 auto with zarith.
rewrite H7.
intros (H8, H9); Contradict H9.
apply prime_div_prime with (p := Zabs_nat 2).
apply lt_Zlt_inv; repeat rewrite inj_abs; auto with zarith.
exact (primeb_correct 2).
cut (Zodd m1); [ intros (x, H11) | intuition ].
exists (Zabs_nat (x + 1)).
rewrite H11; rewrite <- absolu_comp_mult.
replace (2 * x + 1 + 1)%Z with ((x + 1) * 2)%Z; auto with zarith.
intuition.
rewrite H; unfold lexZ, pairZ in |- *; apply right_lex; auto with zarith.
unfold Zwf in |- *; omega.
Qed. 

(* Why obligation from file "Knuth.mlw", characters 481-1499 *)
Lemma Prime_po_10 :
 forall (a : array Z) (Pre10 : (n > 0)%Z /\ array_length a = n) 
   (m0 : Z) (Post1 : m0 = 3%Z) (i0 : Z) (Post2 : i0 = 1%Z)
   (Pre9 : (0 <= 0)%Z /\ (0 < array_length a)%Z) (a0 : array Z)
   (Post3 : a0 = store a 0 2%Z) (Variant1 : prodZZ) 
   (a1 : array Z) (i1 m1 : Z)
   (Pre8 : Variant1 = pairZ (n - i1) (2 * access a1 (i1 - 1) - m1))
   (Pre7 : ((access a1 (i1 - 1) < m1)%Z /\ (m1 < 2 * access a1 (i1 - 1))%Z) /\
           ((0 < i1)%Z /\ (i1 <= n)%Z) /\
           Zodd m1 /\
           (forall k : Z,
            (access a1 (i1 - 1) < k)%Z /\ (k < m1)%Z -> ~ Zprime k) /\
           (forall k : Z, (0 <= k)%Z /\ (k < i1)%Z -> Zprime (access a1 k)) /\
           (forall k j : Z,
            (0 <= k)%Z /\ (k < j)%Z /\ (j < i1)%Z ->
            (access a1 k < access a1 j)%Z) /\
           (forall k : Z,
            (0 <= k)%Z /\ (k <= access a1 (i1 - 1))%Z /\ Zprime k ->
            In k a1 0 i1) /\ array_length a1 = n) (Test8 : (i1 < n)%Z)
   (a2 : array Z) (i2 m2 : Z)
   (Post17 : (((access a2 (i2 - 1) < m2)%Z /\ (m2 < 2 * access a2 (i2 - 1))%Z) /\
              ((0 < i2)%Z /\ (i2 <= n)%Z) /\
              Zodd m2 /\
              (forall k : Z,
               (access a2 (i2 - 1) < k)%Z /\ (k < m2)%Z -> ~ Zprime k) /\
              (forall k : Z, (0 <= k)%Z /\ (k < i2)%Z -> Zprime (access a2 k)) /\
              (forall k j : Z,
               (0 <= k)%Z /\ (k < j)%Z /\ (j < i2)%Z ->
               (access a2 k < access a2 j)%Z) /\
              (forall k : Z,
               (0 <= k)%Z /\ (k <= access a2 (i2 - 1))%Z /\ Zprime k ->
               In k a2 0 i2) /\ array_length a2 = n) /\
             lexZ (pairZ (n - i2) (2 * access a2 (i2 - 1) - m2))
               (pairZ (n - i1) (2 * access a1 (i1 - 1) - m1))),
 lexZ (pairZ (n - i2) (2 * access a2 (i2 - 1) - m2)) Variant1.
Proof.
intros; rewrite Pre8; intuition.
Qed.
 
(* Why obligation from file "Knuth.mlw", characters 523-957 *)
Lemma Prime_po_11 :
 forall (a : array Z) (Pre10 : (n > 0)%Z /\ array_length a = n) 
   (m0 : Z) (Post1 : m0 = 3%Z) (i0 : Z) (Post2 : i0 = 1%Z)
   (Pre9 : (0 <= 0)%Z /\ (0 < array_length a)%Z) (a0 : array Z)
   (Post3 : a0 = store a 0 2%Z),
 ((access a0 (i0 - 1) < m0)%Z /\ (m0 < 2 * access a0 (i0 - 1))%Z) /\
 ((0 < i0)%Z /\ (i0 <= n)%Z) /\
 Zodd m0 /\
 (forall k : Z, (access a0 (i0 - 1) < k)%Z /\ (k < m0)%Z -> ~ Zprime k) /\
 (forall k : Z, (0 <= k)%Z /\ (k < i0)%Z -> Zprime (access a0 k)) /\
 (forall k j : Z,
  (0 <= k)%Z /\ (k < j)%Z /\ (j < i0)%Z -> (access a0 k < access a0 j)%Z) /\
 (forall k : Z,
  (0 <= k)%Z /\ (k <= access a0 (i0 - 1))%Z /\ Zprime k -> In k a0 0 i0) /\
 array_length a0 = n.
Proof.
intros a Pre10 m0 Post1 i0 Post2 Pre9 a0 Post3.
rewrite Post1; rewrite Post2; rewrite Post3.
replace (1 - 1)%Z with 0%Z; auto with zarith.
repeat rewrite store_def_1; auto with zarith.
split; auto with zarith.
split; auto with zarith.
split; auto with zarith.
exists 1%Z; auto with zarith.
split; auto with zarith.
split; auto with zarith.
intros k (H1, H2); replace k with 0%Z; auto with zarith.
rewrite store_def_1; auto with zarith.
split; auto with zarith.
exact (primeb_correct 2).
split; auto with zarith.
split.
intros k (H1, (H2, H3)); case (Zle_lt_or_eq _ _ H2); intros H4.
case (Zle_lt_or_eq k 1); auto with zarith; intros H5.
Contradict H3; replace k with 0%Z; auto with zarith.
intros (H6, H7); Contradict H7; auto with arith.
Contradict H3; intros (H6, H7); Contradict H7; rewrite H5; auto with arith.
rewrite H4; apply In_cons with (i := 0%Z); auto with zarith.
apply store_def_1; auto with zarith.
simpl in |- *; intuition.
Qed.
 
(* Why obligation from file "Knuth.mlw", characters 407-1720 *)
Lemma Prime_po_12 :
 forall (a : array Z) (Pre10 : (n > 0)%Z /\ array_length a = n) 
   (m0 : Z) (Post1 : m0 = 3%Z) (i0 : Z) (Post2 : i0 = 1%Z)
   (Pre9 : (0 <= 0)%Z /\ (0 < array_length a)%Z) (a0 : array Z)
   (Post3 : a0 = store a 0 2%Z) (a1 : array Z) (i1 m1 : Z)
   (Post16 : (((access a1 (i1 - 1) < m1)%Z /\ (m1 < 2 * access a1 (i1 - 1))%Z) /\
              ((0 < i1)%Z /\ (i1 <= n)%Z) /\
              Zodd m1 /\
              (forall k : Z,
               (access a1 (i1 - 1) < k)%Z /\ (k < m1)%Z -> ~ Zprime k) /\
              (forall k : Z, (0 <= k)%Z /\ (k < i1)%Z -> Zprime (access a1 k)) /\
              (forall k j : Z,
               (0 <= k)%Z /\ (k < j)%Z /\ (j < i1)%Z ->
               (access a1 k < access a1 j)%Z) /\
              (forall k : Z,
               (0 <= k)%Z /\ (k <= access a1 (i1 - 1))%Z /\ Zprime k ->
               In k a1 0 i1) /\ array_length a1 = n) /\ 
             (i1 >= n)%Z),
 (forall k : Z, (0 <= k)%Z /\ (k < n)%Z -> Zprime (access a1 k)) /\
 (forall k j : Z,
  (0 <= k)%Z /\ (k < j)%Z /\ (j < n)%Z -> (access a1 k < access a1 j)%Z) /\
 (forall k : Z,
  (0 <= k)%Z /\ (k <= access a1 (n - 1))%Z /\ Zprime k -> In k a1 0 n).
Proof.
intros a Pre10 m0 Post1 i0 Post2 Pre9 a0 Post3 a1 i1 m1 Post17.
cut (n = i1); [ intros H1 | auto with zarith ].
split; auto with zarith.
intuition.
split; auto with zarith.
intuition.
intros k (H2, (H3, H4)).
cut (In k a1 0 i1); [ intros H5; inversion H5 | intuition ].
apply In_cons with (i := i); auto with zarith.
apply H16; rewrite <- H1; auto with zarith.
Qed.