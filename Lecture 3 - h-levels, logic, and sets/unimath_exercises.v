Require Export UniMath.Foundations.All.

(* Exercise 1*)

(* The unit type is contractible.*)

(* When you need to prove a Σ-type, use the command ~use tpair.~ to split the goal into two subgoals.
   When you have a Σ-type as a hypothesis, use ~pr1~ to get the first component of the pair, and ~pr2~ to get the second component of the pair.*)

Theorem unit_iscontr : iscontr unit.
Proof.
Admitted.

(* Exericse 2 *)

(* The empty type is a proposition. *)

Theorem empty_is_prop : isaprop (∅).
Admitted.

(* Exercise 3 *)

(* Every contractible type is a proposition. *)

Theorem contr_is_prop {C : UU} (h : iscontr C) : isaprop C.
Proof.
Admitted.

(* Exercise 4 *)

(* If a proposition is inhabited, then it is contractible.*)

Theorem inhab_prop_is_contr {P : UU} (p : P) (h : isaprop P) : iscontr P.
Proof.
Admitted.

(* Exercise 5 *)

(* If a type has h-level n, then it has h-level n+1.*)

Theorem hlevel_cumulative  {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
Admitted.

(* Exercise 6*)

(* ~weq A B~ is the type of equivalences from A to B. You can also write ~A ≃ B~ where ≃ is written as ~\simeq~.*)

(* From an equivalence, you can get an inverse function.*)

Theorem inverse {A B : UU} (e : A ≃ B) : B → A.
Proof.
Admitted.

(* Exercise 7 *)

(* Every contractible type is equivalent to the unit.*)

Theorem contr_equiv_unit {C : UU} {h : iscontr C} : C ≃ unit.
Proof.
Admitted.

(* Exercise 8*)

(* Every statement ishlevel n A is a proposition.*)

(* Hint: use ~impred_iscontr~ and ~isofhleveltotal2~ from the library. *)

Theorem hlevelprop (n : nat) (A : UU) : isaprop (isofhlevel n A).
Proof.
Admitted.