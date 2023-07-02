Require Export UniMath.Foundations.All.

(*
Note that there is only one universe in UniMath, called UU (not Prop, Set, or Type as in vanilla Coq). It is defined in UniMath as 

Definition UU := Type.
*)

(* A lot of things are abbreviated with Unicode symbols. Depending on your editor, there is usually a way to get "Agda" or "Latex" input, and then you write the symbol as in Latex. Note that ∑ is ~\Sum~ and ∏ is ~\Prod~ (not ~\Sigma~ and ~\Pi~).*)

(* Exercise 1*)

(*bool is defined as the following in UniMath.Foundations.Preamble:

Inductive bool : UU :=
  | true : bool
  | false : bool.

*)
(* → is defined as

Notation "A -> B" := (forall (_ : A), B) : type_scope.

You can write it as ~\to~.
*)

Definition not : bool → bool.
Proof.
    Admitted.

Compute (not true).
(*Result: = false : bool*)
Compute (not false).
(*Result: = true : bool*)

Print not.
(*Result: not = λ b : bool, bool_rect (λ _ : bool, bool) false true b
	 : bool → bool
 Notes:
 - bool_rect is what we call ind_bool in the notes.
 - The argument (λ _ : bool, bool) : bool -> Type is implicit in the notes.*)

(* Exercise 2*)

(*
nat is defined as the following in Unimath.Foundations.Preamble:

Inductive nat : UU :=
  | O : nat
  | S : nat -> nat.

Notation  "0" := (O) : nat_scope.
Notation  "1" := (S 0) : nat_scope.
...
*)

Definition ι : bool → nat.
Proof.
  Admitted.

(*Exercise 3*)

Definition add : nat → nat → nat.
Proof. 
    Admitted.

Compute (add 5 7).
(*Result: = 12 : nat*)
Compute (add 12 21).
(*Result: = S (S (S (S (S (S (S (S (S 24))))))))
     : nat*)

Print add.
(* Result:
add = 
λ n m : nat, nat_rect (λ _ : nat, nat) n (λ _ IHm : nat, S IHm) m
	 : nat → nat → nat
Note:
- nat_rect is basically what is called ind_N in the notes.
- (λ _ IHm : nat, S IHm) is what is called sz in the notes.
*)

(* Exercise 4 *)

Definition mult : nat → nat → nat.
Proof.
  Admitted.

Compute (mult 2 3).
(*Result: = 6
     : nat*)

(* Exercise 5 *)

(*∑ types are defined in UniMath.Foundations.Preamble as:

Record total2 { T: UU } ( P: T -> UU ) := tpair { pr1 : T; pr2 : P pr1 }.

Arguments tpair {_} _ _ _.
Arguments pr1 {_ _} _.
Arguments pr2 {_ _} _.

Notation "'∑'  x .. y , P" := (total2 (λ x, .. (total2 (λ y, P)) ..))
  (at level 200, x binder, y binder, right associativity) : type_scope.
  (* type this in emacs in agda-input method with \sum *)

Notation "x ,, y" := (tpair _ x y).
*)

(*When a term in a sigma type is in the hypothesis, use the tactic ~destruct _ as [_,_].~ to split it into two hypotheses.*)

Definition π1 {P : UU} (Q : P → UU) : (∑ (x : P), Q x) → P.
Proof.
  Admitted.

(* Exercise 6*)

(* Notes:
- idpath is the name in Unimath for refl.
- Defined as maponpaths in UniMath.Foundations.PartA.*)

(*
The identity type is defined in Unimath as:

Inductive paths {A:UU} (a:A) : A -> UU := paths_refl : paths a a.
Notation "a = b" := (paths a b) : type_scope.
Notation idpath := paths_refl .
*)

Definition ap {A B : UU} (f : A → B) {x y : A} (p : x = y) : f x = f y.
Proof. 
  Admitted.

(* Exercise 7 *)

Definition left_unit (n : nat) : add 0 n = n.
Proof.
  Admitted.

(* Exercise 8 *)

(* Everything respects equality. *)

(* Note: transport is defined as transportf in UniMath.Foundations.PartA.*)

Theorem transport {A : UU} {D : A → UU} {a b : A} (d : D a) (p: a = b) : D b.
Proof.
  Admitted.

(* Exercise 9 (Long) *)

(*
You might want to make the parameter {A:UU} in paths explicit. Do this by writing @paths.
*)

(* Note ∏ is defined in UniMath as

Notation "'∏'  x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity) : type_scope.

You can usually write ∏ as ~\prod~.*)

(* × is defined in Unimath as

Definition dirprod (X Y : UU) := ∑ x:X, Y.

Notation "A × B" := (dirprod A B) : type_scope.

You can write it as ~\times~.*)

Definition reflexive {A : UU} (R: A → A → UU) : UU := ∏ a : A, a = a.

Definition symmetric {A : UU} (R: A → A → UU) : UU := ∏ (a b : A), a = b → b = a.

Definition transitive {A : UU} (R: A → A → UU) : UU := ∏ (a b c : A), a = b → b = c → a = c.

Definition equivalence {A : UU} (R: A → A → UU) : UU := (reflexive R) × (symmetric R) × (transitive R).

Theorem equivalence_paths (A : UU) : equivalence (@paths A).
Proof.
  Admitted.