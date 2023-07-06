Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* ~<->~ is the infix notation for ~logeq~, logical equivlance, i.e. two functions, back and forth.

You can use the transitivity and symmetry functions that you constructed earlier, or the ones from the library. ~p @ q~ is the composition (transitivity) of p and q and ~!p~ is the inverse (symmetry) of p. You might also want to use ~pathsinv0r~ from the library.*)

Lemma prop_theorem {A : UU} : isaprop A <-> (∏ (x y : A), (x = y)).
Proof.
Admitted.

(* Exercise 2 *)

(* Characterization of equality in Sigma types. *)

(*We first show that there is a quasiequivalence
    (s = t) ≅ ∑ (p : pr1 s = pr1 t), transportf E p (pr2 s) = pr2 t
i.e. functions (s = t) <-> ∑ (p : pr1 s = pr1 t), transportf E p (pr2 s) = pr2 t such that both compositions are pointwise equal to the identity. *)

About transportf.

Definition eq1 {B : UU} {E : B → UU} {s t : ∑ (b : B), E b} (p : s = t) : ∑ (p : pr1 s = pr1 t), transportf E p (pr2 s) = pr2 t.
Proof.
Admitted.

Definition eq2 {B : UU} {E : B → UU} {s t : ∑ (b : B), E b} (u :  ∑ (p : pr1 s = pr1 t), transportf E p (pr2 s) = pr2 t) : s = t.
Proof.
Admitted.

Definition eq3 {B : UU} {E : B → UU} {s t : ∑ (b : B), E b} (p : s = t) : eq2 (eq1 p) = p.
Proof.
Admitted.

Definition eq4 {B : UU} {E : B → UU} {s t : ∑ (b : B), E b} (u :  ∑ (p : pr1 s = pr1 t), transportf E p (pr2 s) = pr2 t) : eq1 (eq2 u) = u.
Proof.
Admitted.

(* ~isweq~ is the statement that a function is an equivalence.*)

Theorem char_eq_sigma {B : UU} {E : B → UU} {s t : ∑ (b : B), E b} : isweq (@eq1 B E s t).
Proof.
    use isweq_iso.
    - exact eq2.
    - exact eq3.
    - exact eq4.
Defined.

(* Exercise 3 *)

(* Function underlying univalence. *)

Definition id_to_equiv (A B : UU) : (A = B) → (A ≃ B).
Proof.
Admitted.

(************)

(* Now we can assume univalence. *)

Variable ua : ∏ (A B : UU), isweq (id_to_equiv A B).

(************)

(* Exercise 4 *)

(* isweq is a proposition *)

(* Hint: use ~isapropisofhlevel~, ~isapropifcontr~ (or use what you defined earlier), and ~impred_isaprop~.*)

Theorem weq_is_prop {A B : UU} (f : A → B) : isaprop (isweq f).
Proof.
Admitted.

(* Exercise 5 *)

(* Logical univalence. *)

(* Function extensionality is called ~isweqtoforallpathsUAH~.*)

(* You might want to use ~invmap~ (or use the version you constructed in the previous exercises), ~isapropifcontr~, ~isofhleveltotal2~, and ~impred_iscontr~. *)

Lemma equiv_to_id {A B : UU} (e : A ≃ B) : (A = B).
Proof.
Admitted.

Lemma prop_function_prop {P Q : hProp} : isaprop (P → Q).
Proof.
Admitted.

Lemma prop_log_equiv_prop {P Q : hProp} : isaprop (P <-> Q).
Proof. 
Admitted.

Lemma prop_equiv_prop {P Q : hProp} : isaprop (P ≃ Q).
Admitted.

Lemma logical_eq_eq_1 {P Q : hProp} (e: P ≃ Q):  (P <-> Q).
Admitted.

Lemma logical_eq_eq_2 {P Q : hProp} (e: P <-> Q): (P ≃ Q).
Admitted.

Lemma logical_eq_eq_3 {P Q : hProp} (e: P ≃ Q) :  logical_eq_eq_2 (logical_eq_eq_1 e) = e.
Proof.
Admitted.

Lemma logical_eq_eq_4 {P Q : hProp} (e : P <-> Q) : logical_eq_eq_1 (logical_eq_eq_2 e) = e.
Proof. 
Admitted.

Lemma logical_eq_eq (P Q : hProp) : isweq (@logical_eq_eq_1 P Q).
Proof.
    use isweq_iso.
    - exact logical_eq_eq_2.
    - exact logical_eq_eq_3.
    - exact logical_eq_eq_4.
Defined.

Theorem logical_univalence {P Q : hProp} : (P = Q) ≃ (P <-> Q).
Proof.
    set (g := subtypeInjectivity isaprop (isapropisofhlevel 1) P Q).
    set (h := (id_to_equiv P Q,,ua P Q)).
    set (i := (@logical_eq_eq_1 P Q,, logical_eq_eq P Q)).
    set (j := weqcomp g h).
    set (k := weqcomp j i).
    exact k.
Defined.