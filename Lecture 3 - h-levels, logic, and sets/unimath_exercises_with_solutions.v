Require Export UniMath.Foundations.All.

(* Exercise 1*)

(* The unit type is contractible.*)

Print unit.

(* When you need to prove a Σ-type, use the command ~use tpair.~ to split the goal into two subgoals.
   When you have a Σ-type as a hypothesis, use ~pr1~ to get the first component of the pair, and ~pr2~ to get the second component of the pair.*)

Theorem unit_iscontr : iscontr unit.
Proof.
    unfold iscontr.
    use tpair.
    - exact tt.
    - simpl.
      intro t.
      induction t.
      apply idpath.
Defined.

(* Exericse 2 *)

(* The empty type is a proposition. *)

Theorem empty_is_prop : isaprop (∅).
    Proof.
        unfold isaprop.
        simpl.
        intros x y.
        induction x.
Defined.

(* Exercise 3 *)

(* Every contractible type is a proposition. *)

Lemma path_combination {A : UU} {a a' b : A} (p : a = b) (q: a' = b) : a = a'.
Proof.
    induction p.
    induction q.
    apply idpath.
Defined.

Lemma path_combination_fact {A : UU} {a b : A} (p : a = b) : idpath a = path_combination p p.
Proof.
    induction p.
    simpl.
    apply idpath.
Defined.

Theorem contr_is_prop {C : UU} (h : iscontr C) : isaprop C.
Proof.
    unfold isaprop.
    simpl.
    intros x y.
    unfold iscontr.
    use tpair.
    destruct h as [cntr p].
    + exact (path_combination (p x) (p y)).
    + simpl.
      intro t.
      induction t.
      exact (path_combination_fact (pr2 h x)).
Defined.

(* Exercise 4 *)

(* If a proposition is inhabited, then it is contractible.*)

Theorem inhab_prop_is_contr {P : UU} (p : P) (h : isaprop P) : iscontr P.
Proof.
    use tpair.
    - exact p. 
    - simpl.
      intro q.
      unfold isaprop in h.
      simpl isofhlevel in h.
      set (e := h q p).
      exact (pr1 e).
Defined.

(* Exercise 5 *)

(* If a type has h-level n, then it has h-level n+1.*)

Lemma hlevel_cumulativ_ind  (n : nat) : ∏ (T : UU) (h : isofhlevel n T), isofhlevel (S n) T.
Proof.
    induction n.
    - intros T c.
      exact (contr_is_prop c).
    - intros T h.
      simpl isofhlevel.
      intros x y.
      simpl isofhlevel in h.
      exact (IHn (x = y) (h x y)).
Defined.

Theorem hlevel_cumulative  {n : nat} {T : UU} (h : isofhlevel n T) : isofhlevel (S n) T.
Proof.
    apply hlevel_cumulativ_ind.
    exact h.
Defined.

(* Exercise 6*)

(* ~weq A B~ is the type of equivalences from A to B. You can also write ~A ≃ B~ where ≃ is written as ~\simeq~.*)

(* From an equivalence, you can get an inverse function.*)

Theorem inverse {A B : UU} (e : A ≃ B) : B → A.
Proof.
    unfold weq in e.
    destruct e as [f w].
    intro b.
    unfold isweq in w.
    unfold iscontr in w.
    destruct (w b) as [cntr _].
    unfold hfiber in cntr.
    destruct cntr as [x _].
    exact x.
Defined.

(* Exercise 7 *)

(* Every contractible type is equivalent to the unit.*)

Lemma contr_to_path {C : UU} (h : iscontr C) (x y : C) : x = y.
Proof.
    destruct h as [h1 h2].
    exact (path_combination (h2 x) (h2 y)).
Defined.

Lemma paths_in_unit (p : tt = tt) : p = (idpath tt).
Proof.
    exact (contr_to_path (contr_is_prop unit_iscontr tt tt) p (idpath tt)).
Defined.

Theorem contr_equiv_unit {C : UU} {h : iscontr C} : C ≃ unit.
Proof.
    unfold weq.
    use tpair.
    - exact (λ _ , tt).
    - simpl.
      unfold isweq.
      intro y.
      induction y.
      unfold hfiber.
      destruct h as [cntr p].
      use tpair.
      + exact (cntr,,idpath tt).
      + simpl.
        intro t.
        destruct t as [c q].
        rewrite (p c).
        rewrite (paths_in_unit q).
        exact (idpath (cntr,, idpath tt)).
Defined.

(* Exercise 8*)

(* Every statement ishlevel n A is a proposition.*)

(* Hint: use ~impred_iscontr~ and ~isofhleveltotal2~ from the library. *)

Lemma iscontr_prop {A : UU} : isaprop (iscontr A).
Proof.
    unfold isaprop.
    simpl isofhlevel.
    intros [cntr1 c1] [cntr2 c2].
    set (A_is_contr := (cntr1,,c1)).
    assert (h1 : ∏ x : A, (iscontr (∏ t : A, t = x))).
    {
        intro.
        apply impred_iscontr.
        intro.
        use contr_is_prop.
        exact A_is_contr.
    }
    assert (h2 : iscontr (∑ cntr : A, ∏ t : A, t = cntr)).
    {
        use (isofhleveltotal2 0).
        - exact A_is_contr.
        - intro a.
          simpl.
          exact (h1 a). 
    }
    apply contr_is_prop.
    exact h2.
Defined.

Lemma hlevelprop_ind (n : nat) : ∏ A : UU, isaprop (isofhlevel n A).
Proof.
    induction n.
    - intro A.
      use iscontr_prop.
    - intro A.
      intros x y.
      simpl in x, y.
      set (h1 := λ a b : A, IHn (a = b)).
      assert (isaprop (∏ a b : A, isofhlevel n (a = b))).
      {
       use impred_isaprop.
       simpl.
       intro a. 
       use impred_isaprop.
       intro b.
       simpl.
       apply h1.
      }
      apply X.
Defined.

Theorem hlevelprop (n : nat) (A : UU) : isaprop (isofhlevel n A).
Proof.
    apply hlevelprop_ind.
Defined.