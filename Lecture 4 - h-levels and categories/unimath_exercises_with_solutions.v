Require Export UniMath.Foundations.All.

(* Exercise 1 *)

(* ~<->~ is the infix notation for ~logeq~, logical equivlance, i.e. two functions, back and forth.

You can use the transitivity and symmetry functions that you constructed earlier, or the ones from the library. ~p @ q~ is the composition (transitivity) of p and q and ~!p~ is the inverse (symmetry) of p. You might also want to use ~pathsinv0r~ from the library.*)

Lemma prop_theorem {A : UU} : isaprop A <-> (∏ (x y : A), (x = y)).
Proof.
    unfold logeq.
    use tpair.
    - intro h.
      intros x y.
      destruct (h x y) as [cntr _].
      exact cntr.
    - simpl.
      intro h.
      intros x y.
      use tpair.
      + exact ((h x y) @ !(h y y)).
      + simpl.
        intro t.
        induction t.
        exact (!(pathsinv0r (h x x))).
Defined.

(* Exercise 2 *)

(* Characterization of equality in Sigma types. *)

(*We first show that there is a quasiequivalence
    (s = t) ≅ ∑ (p : pr1 s = pr1 t), transportf E p (pr2 s) = pr2 t
i.e. functions (s = t) <-> ∑ (p : pr1 s = pr1 t), transportf E p (pr2 s) = pr2 t such that both compositions are pointwise equal to the identity. *)

About transportf.

Definition eq1 {B : UU} {E : B → UU} {s t : ∑ (b : B), E b} (p : s = t) : ∑ (p : pr1 s = pr1 t), transportf E p (pr2 s) = pr2 t.
Proof.
    induction p.
    use tpair.
    + apply idpath.
    + simpl.
      apply idpath.
Defined.

Definition eq2 {B : UU} {E : B → UU} {s t : ∑ (b : B), E b} (u :  ∑ (p : pr1 s = pr1 t), transportf E p (pr2 s) = pr2 t) : s = t.
Proof.
    induction s as [b1 e1].
    induction t as [b2 e2].
    simpl.
    induction u as [p q].
    simpl in p, q.
    induction p.
    induction q.
    apply idpath.
Defined.

Definition eq3 {B : UU} {E : B → UU} {s t : ∑ (b : B), E b} (p : s = t) : eq2 (eq1 p) = p.
Proof.
    induction p.
    induction s as [b e].
    simpl.
    apply idpath.
Defined.

Definition eq4 {B : UU} {E : B → UU} {s t : ∑ (b : B), E b} (u :  ∑ (p : pr1 s = pr1 t), transportf E p (pr2 s) = pr2 t) : eq1 (eq2 u) = u.
Proof.
    induction s as [b1 e1].
    induction t as [b2 e2].
    induction u as [p q].
    simpl in p.
    induction p.
    simpl in q.
    induction q.
    simpl.
    apply idpath.
Defined.

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
    intro p.
    induction p.
    use tpair.
    - intro a.
      exact a.
    - simpl.
      intro a.
      use tpair.
      + use tpair.
        * exact a.
        * simpl.
          apply idpath.
      + simpl.
        intro t.
        destruct t as [b p].
        induction p.
        apply idpath.
Defined.

(************)

(* Now we can assume univalence. *)

Variable ua : ∏ (A B : UU), isweq (id_to_equiv A B).

(************)

(* Exercise 4 *)

(* isweq is a proposition *)

(* Hint: use ~isapropisofhlevel~, ~isapropifcontr~ (or use what you defined earlier), and ~impred_isaprop~.*)

Theorem weq_is_prop {A B : UU} (f : A → B) : isaprop (isweq f).
Proof.
    intros v w.
    assert (isaprop (isweq f)) as P.
      {
        apply impred_isaprop.
        intro b.
        apply (isapropisofhlevel 0).
      }
    unfold isofhlevel.
    unfold iscontr.
    use tpair.
    - unfold isweq in v, w.
      apply prop_theorem.
      exact P.
    - simpl.
      assert (isaprop (v = w)) as Q.
      { 
        apply isapropifcontr.
        apply P.
      }
      intro t.
      apply prop_theorem.
      exact Q.
Defined.

(* Exercise 5 *)

(* Logical univalence. *)

(* Function extensionality is called ~isweqtoforallpathsUAH~.*)

(* You might want to use ~invmap~ (or use the version you constructed in the previous exercises), ~isapropifcontr~, ~isofhleveltotal2~, and ~impred_iscontr~. *)

Lemma equiv_to_id {A B : UU} (e : A ≃ B) : (A = B).
Proof.
    set (u := (id_to_equiv A B,,(ua A B))).
    exact (invmap u e).
Defined.

Lemma ua_eq (A B : UU) : (A = B) = (A ≃ B).
Proof.
    exact (equiv_to_id (id_to_equiv A B,,ua A B)).
Defined.

Lemma prop_function_prop {P Q : hProp} : isaprop (P → Q).
Proof.
    intros f g.
    unfold isofhlevel.
    set (h1 := ((toforallpaths (λ _ : P, Q) f g),,isweqtoforallpathsUAH ua P (λ x, Q) f g)).
    set (h2 := equiv_to_id h1).
    rewrite h2.
    apply impred_iscontr.
    intro p.
    apply (pr2 Q).
Defined.

Lemma prop_log_equiv_prop {P Q : hProp} : isaprop (P <-> Q).
Proof. 
    unfold logeq.
    apply isofhleveltotal2.
    - exact prop_function_prop.
    - intro f.
      exact prop_function_prop.
Defined.

Lemma prop_equiv_prop {P Q : hProp} : isaprop (P ≃ Q).
Proof.
    intros e f.
    unfold isofhlevel.
    unfold weq in e,f.
    assert (∏ (A B : UU), A = B → iscontr B → iscontr A ) as H1.
    {
        intros A B p c.
        induction p.
        exact c.
    }
    apply (H1 (e = f) ((∑ p : pr1 e = pr1 f,
    transportf isweq p (pr2 e) = pr2 f))).
    - set (h1 := @eq1 (P → Q) isweq e f).
      set (h2 := (h1,,char_eq_sigma)).
      exact (equiv_to_id h2).
    - apply (isofhleveltotal2 0).
      + apply prop_function_prop.
      + intro p.
        apply weq_is_prop.
Defined.

Lemma logical_eq_eq_1 {P Q : hProp} (e: P ≃ Q):  (P <-> Q).
Proof.
    use tpair.
    - exact (pr1 e).
    - simpl.
      exact (invmap e).
Defined.

Lemma logical_eq_eq_2 {P Q : hProp} (e: P <-> Q): (P ≃ Q).
Proof.
    use tpair.
    - exact (pr1 e).
    - simpl.
      intro q.
      destruct e as [f g].
      use tpair.
      + use tpair.
        * exact (g q).
        * simpl.
          apply prop_theorem.
          exact (pr2 Q).
      + simpl.
        intro t.
        destruct t as [p e].
        induction e.
        use eq2.
        use tpair.
        * simpl.
          apply prop_theorem.
          exact (pr2 P).
        * simpl.
          apply prop_theorem.
          set (h := (pr2 Q) (f (g (f p))) (f p)).
          simpl in h.
          apply isapropifcontr.
          exact h.
Defined.

Lemma logical_eq_eq_3 {P Q : hProp} (e: P ≃ Q) :  logical_eq_eq_2 (logical_eq_eq_1 e) = e.
Proof.
    apply prop_equiv_prop.
Defined.

Lemma logical_eq_eq_4 {P Q : hProp} (e : P <-> Q) : logical_eq_eq_1 (logical_eq_eq_2 e) = e.
Proof. 
    apply prop_log_equiv_prop.
Defined.

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