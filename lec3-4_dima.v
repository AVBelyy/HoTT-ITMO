Inductive Bool: Set:=
true': Bool
| false': Bool.

Definition or' (a b : Bool) := if a then true' else b.
Definition and' (a b : Bool) := if a then b else false'.

Inductive True':Prop :=
  I':True'.
Inductive False' : Prop :=.

Definition Is_true (a:Bool) : Prop := match a with
  true' => True'
| false' => False'
end.

Inductive And (A B : Prop) : Prop := conj' : A -> B -> And A B.
Inductive Or (A B : Prop) : Prop := inl' : A -> Or A B | inr' : B -> Or A B.

Infix "||" := or' : My_scope.
Infix "/_\" := And (at level 80) : My_scope.
Infix "\_/" := Or (at level 80) : My_scope.

Inductive Id {A : Type} (a:A) : A -> Type := id: Id a a.
Infix "==" := Id (at level 70) : My_scope.
Open Scope My_scope.

Definition not' (A: Prop) := A -> False'.
Notation "~ A" := (A -> False') : My_scope.
Infix "!=" := (~(x == y)) (at level 70) : My_scope.


Theorem or_commutes : forall a b, Is_true(a || b) -> Is_true(b || a).
Proof.
  intros a b.
  case a,b.
  simpl.
  intros t.
  exact t.
  simpl.
  intros t.
  exact t.
  simpl.
  intros t.
  exact t.
  simpl.
  intros t.
  exact t.
Qed.

Inductive Empty : Set :=.
Inductive Nat : Set :=
  Zero : Nat
| Succ : Nat -> Nat.

Fixpoint natrec (C : Nat -> Set) (d : C Zero) (e : forall (x: Nat) (y: C x), (C (Succ x))) (n: Nat) : C n :=
  match n with
    Zero => d
   |Succ n' => e n' (natrec C d e n')
  end.

Definition plus' (n m : Nat) : Nat := natrec (fun _ => Nat) n (fun _ y => Succ y) m.
Definition mul'  (n m : Nat) : Nat := natrec (fun _ => Nat) Zero (fun _ y => plus' y n) m.

Infix "+" := plus' : Nat_scope.
Open Scope Nat_scope.

Theorem zero_neutral_right : forall n, (n + Zero) == n.
Proof.
  intros n.
  simpl.
  exact (id n).
Qed.

Theorem zero_neutral_left : forall n, (Zero + n) == n.
Proof.
  intros n.
  unfold plus'.
  elim n.
  simpl.
  exact (id Zero).
  intros n0.
  intros ind_hyp.
  simpl.
  rewrite ind_hyp.
  exact (id _).
Qed.

Theorem comm_plus : forall n m, (n + m) == (m + n).
Proof.
  intros n m.
  unfold plus'.
  elim n.
  simpl.
  exact (zero_neutral_left m).
  intros n0 ind_hyp.
  simpl.
  rewrite <- ind_hyp.
  elim m.
  simpl.
  exact (id _).
  intros n1 ind_hyp2.
  simpl.
  rewrite ind_hyp2.
  exact (id _).
Qed.

Implicit Arguments conj'.
Implicit Arguments inl'.
Implicit Arguments inr'.

Inductive Pi (A : Set) (B : A -> Set) : Set := lambda : (forall x: A, B x) -> Pi A B.
Definition apply' (A : Set) (B : A -> Set) (g : Pi A B) (x : A) := match g with
  lambda f => f x
end.

Notation "A ~> B" := (Pi A (fun _ => B)) (at level 50) : My_scope.
Notation "~' A" := (A ~> Empty) (at level 45) : My_scope.

Definition lambda' (A B : Set) (f : A -> B) : A ~> B := lambda A (fun _ => B) f.
Definition apply'' (A B : Set) (f : A ~> B) (x : A) := apply' A (fun _ => B) f x.

Theorem add_double_not : forall A : Set, A ~> ~' ~' A.
Proof.
  intros A.
  exact (lambda' A (~' ~' A) (fun x => lambda' (~' A) Empty (fun y => apply'' A Empty y x))).
Qed.

Inductive orS (A B : Set) : Set := inlS : A -> orS A B | inrS : B -> orS A B.
Definition when (A B : Set) (C : orS A B -> Set) (p : orS A B) (f : forall x : A, C (inlS A B x)) (g : forall y : B, C (inrS A B y)) :=
  match p with
    inlS a => f a
  | inrS b => g b
  end.

Inductive Sigma (A : Set) (B: A -> Set) : Set := pair : forall (a: A) (b: B a), Sigma A B.
Definition split' (A : Set) (B : A -> Set) (C : Sigma A B -> Set) (f : forall (x : A) (y : B x), C (pair A B x y)) (p : Sigma A B) :=
  match p with
    pair x y => f x y
  end.

Definition fst' (A : Set) (B : A -> Set) (p : Sigma A B) := split' A B (fun _ => A) (fun x y => x) p.
Definition snd' (A : Set) (B : A -> Set) (p : Sigma A B) := split' A B (fun x => B (fst' A B x)) (fun x y => y) p.

(* HW : \forall x \in A: \not P x <=> \not \exists x \in A : P x *)

(*Theorem forall_is_exists : forall (A : Set) (B : A -> Set), (Pi A (fun x => ~' (B x))) ~> ~'(Sigma A B).
Proof.
  (* hw *)
  (* guess : split *)
Qed.*)

Inductive List (A : Set) : Set := null : List A | new : A -> List A -> List A.

Definition head (A: Set) (def : A) (l : List A) : A :=
  match l with
    null => def
  | new x xs => x
  end.

Inductive Maybe {A : Set} : Set := Nothing : Maybe | Just : A -> Maybe.
Definition head' (A: Set) (l : List A) : Maybe :=
  match l with
    null => Nothing
  | new x xs => Just x
  end.

(* hw : Definition head'' (A : Set) (l : List A) (proof: l != null A) : A :=. *)

Definition tail (A : Set) (l : List A) : List A :=
  match l with
    null => null A
  | new x xs => xs
  end.

(* hw : finish it. Definition foldr (A : Set) (B : List A -> Set) (a0 : B null) (f : forall (x : A) (xs : List A) (y : *)

Section Relation_functions.
  Variable A: Type.
  Definition Relation (S : Type) := S -> S -> Prop.
  Variable R : Relation A.
  Section General_properties_of_relations.
    Definition reflective : Prop := forall a, R a a.
    Definition symmetric : Prop := forall a b, R a b -> R b a.
    Definition transitive : Prop := forall a b c, R a b -> R b c -> R a c.
    Definition equiv : Prop := reflective /\ symmetric /\ transitive.
  End General_properties_of_relations.