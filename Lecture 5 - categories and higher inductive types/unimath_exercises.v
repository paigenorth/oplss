Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Propositional truncation is defined slightly differently in UniMath than how I defined it. Show that it has the same properties in the next few exercises. *)

Variable ua : univalenceStatement.

Variable funext : funextsecStatement.

Definition prop_trunc (X : UU) : UU := ∏ P : hProp, ((X -> P) -> P).

Theorem prop_trunc_unit {X : UU} : X → prop_trunc X.
Admitted.

(* Exercise 2 *)

Theorem prop_trunc_unit_eq {X : UU} {x y : X} : prop_trunc_unit x = prop_trunc_unit y.
Proof.
Admitted.

(* Exercise 3 *)

(* Use ~invproofirrelevance~ or what you have done before.*)

Theorem prop_trunc_prop {X : UU} : isaprop (prop_trunc X).
Proof.
Admitted.

(* Exercise 4 *)

(* Hint: use ~isapropimpl~ and ~isweqimplimpl~.*)

Theorem univ_prop_prop_trunc (T : UU) (P : hProp) : (T → P) ≃ (prop_trunc T → P).
Admitted.

(* Exercise 5 *)

(* Show that hProp is a Set. *)

(* Hint: use ~weqtopaths~, ~isapropweqtoprop~, ~subtypeInjectivity~, and ~isapropisofhlevel~. *)

Theorem hProp_is_Set : isaset hProp.
Proof.
Admitted.

