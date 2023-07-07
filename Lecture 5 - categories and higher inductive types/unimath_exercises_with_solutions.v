Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* Propositional truncation is defined slightly differently in UniMath than how I defined it. Show that it has the same properties in the next few exercises. *)

Variable ua : univalenceStatement.

Variable funext : funextsecStatement.

Definition prop_trunc (X : UU) : UU := ∏ P : hProp, ((X -> P) -> P).

Theorem prop_trunc_unit {X : UU} : X → prop_trunc X.
Proof.
  intro x.
  intro P.
  intro f.
  exact (f x).
Defined.

(* Exercise 2 *)

Lemma prop_trunc_eq {X : UU} {x y : prop_trunc X} : x = y.
Proof.
  unfold prop_trunc in x, y.
  apply funext.
  intro P.
  apply funext.
  intro f.
  exact (pr1 (pr2 P (x P f) (y P f))).
Defined.

Theorem prop_trunc_unit_eq {X : UU} {x y : X} : prop_trunc_unit x = prop_trunc_unit y.
Proof.
  exact prop_trunc_eq.
Defined.

(* Exercise 3 *)

(* Use ~invproofirrelevance~ or what you have done before.*)

Theorem prop_trunc_prop {X : UU} : isaprop (prop_trunc X).
Proof.
  apply invproofirrelevance.
  unfold isProofIrrelevant.
  intros x y.
  exact prop_trunc_eq.
Defined.

(* Exercise 4 *)

(* Hint: use ~isapropimpl~ and ~isweqimplimpl~.*)

Theorem univ_prop_prop_trunc (T : UU) (P : hProp) : (T → P) ≃ (prop_trunc T → P).
Proof.
  assert (isaprop (T → P)) as h.
  {
    apply isapropimpl.
    exact (pr2 P).
  }
  assert (isaprop (prop_trunc T → P)) as i.
  {
    apply isapropimpl.
    exact (pr2 P).
  }
  assert ((T → P) → (prop_trunc T → P)) as f.
  {
    intro f.
    unfold prop_trunc.
    intro g.
    exact (g P f).
  }
  assert ((prop_trunc T → P) → (T → P)).
  {
    intro g.
    intro t.
    exact (g (prop_trunc_unit t)).
  }
  set (j := (@isweqimplimpl (T → P) (prop_trunc T → P) f X h i)).
  exact (f,,j).
Defined.

(* Exercise 5 *)

(* Show that hProp is a Set. *)

(* Hint: use ~weqtopaths~, ~isapropweqtoprop~, ~subtypeInjectivity~, and ~isapropisofhlevel~. *)

Theorem hProp_is_Set : isaset hProp.
Proof.
Admitted.

