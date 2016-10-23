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


(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(* $Id$ *)

Require Export ZArith.

(**************************************)
(* Functional arrays, for use in Why. *)
(**************************************)

(* This is an axiomatization of arrays.
 *
 * The type (array N T) is the type of arrays ranging from 0 to N-1 
 * which elements are of type T.
 *
 * Arrays are created with new, accessed with access and modified with store. 
 *
 * Operations of accessing and storing are not guarded, but axioms are.
 * So these arrays can be viewed as arrays where accessing and storing
 * out of the bounds has no effect.
 *)


Set Implicit Arguments.
Unset Strict Implicit.


(* The type of arrays *)

Parameter raw_array : Set -> Set.

Definition array (T : Set) := (Z * raw_array T)%type.


(* Array length *)

Definition array_length (T : Set) (t : array T) : Z := let (n, _) := t in n.


(* Functions to create, access and modify arrays *)

Parameter raw_new : forall T : Set, T -> raw_array T.

Definition new (T : Set) (n : Z) (a : T) : array T := (n, raw_new a).

Parameter raw_access : forall T : Set, raw_array T -> Z -> T.

Definition access (T : Set) (t : array T) (i : Z) : T :=
  let (_, r) := t in raw_access r i.

Parameter raw_store : forall T : Set, raw_array T -> Z -> T -> raw_array T.

Definition store (T : Set) (t : array T) (i : Z) (v : T) : 
  array T := (array_length t, let (_, r) := t in raw_store r i v).


(* Update does not change length *)

Lemma array_length_store :
 forall (T : Set) (t : array T) (i : Z) (v : T),
 array_length (store t i v) = array_length t.
Proof.
trivial.
Qed.


(* Axioms *)

Axiom
  new_def :
    forall (T : Set) (n : Z) (v0 : T) (i : Z),
    (0 <= i < n)%Z -> access (new n v0) i = v0.

Axiom
  store_def_1 :
    forall (T : Set) (t : array T) (v : T) (i : Z),
    (0 <= i < array_length t)%Z -> access (store t i v) i = v.

Axiom
  store_def_2 :
    forall (T : Set) (t : array T) (v : T) (i j : Z),
    (0 <= i < array_length t)%Z ->
    (0 <= j < array_length t)%Z ->
    i <> j -> access (store t i v) j = access t j.

Hint Resolve new_def store_def_1 store_def_2: datatypes.


(* A tactic to simplify access in arrays *)

Ltac WhyArrays :=
  repeat rewrite store_def_1; repeat rewrite array_length_store.

Ltac AccessStore i j H :=
  elim (Z_eq_dec i j);
   [ intro H; rewrite H; rewrite store_def_1; WhyArrays
   | intro H; rewrite store_def_2; [ idtac | idtac | idtac | exact H ] ].

Ltac AccessSame := rewrite store_def_1; WhyArrays; try omega.

Ltac AccessOther := rewrite store_def_2; WhyArrays; try omega.

Ltac ArraySubst t := subst t; simpl in |- *; WhyArrays; try omega.

(* Syntax and pretty-print for arrays *)

(* <Warning> : Grammar is replaced by Notation *)

(***
Syntax constr level 0 :
  array_access
    [ << (access ($VAR $t) $c) >> ] -> [ "#" $t "[" $c:L "]" ].
***)