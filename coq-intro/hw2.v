(* Equality *)

Inductive Id {A : Type} (a : A) : A -> Type :=
    id : Id a a.
Notation "A == B" := (Id A B) (at level 70) : id_scope.

Open Scope id_scope.

Notation "~ A" := (A -> False) : id_scope.
Notation "A /= B" := (~(A == B)) (at level 70) : id_scope.

(* List *)

Inductive List {A : Set} : Set :=
    null : List
  | new : A -> List -> List.

(* HW : head with proof of non-emptiness. Wow. *)

(* TODO : understand *)
Definition head (A : Set) (l : List) (proof : l /= null) : A :=
    (match l as b return (l == b -> A) with
      | null => fun foo : l == null => match (proof foo) return A with end
      | new x _ => fun foo : l == new x _ => x
    end) (id l).

(* HW : foldr with dependent types *)

Fixpoint foldr (A : Set) (B : List -> Set) (l0 : B (null)) (f : forall (x : A) (xs : List) (y : B xs), B (new x xs)) (l : List) : B l :=
    match l with
      | null => l0
      | new x xs => f x xs (foldr A B l0 f xs)
    end.

(* Sigma and Pi types *)

Inductive Empty :=.

Inductive Sigma (A : Set) (B : A -> Set) : Set :=
    pair : forall (a : A) (b : B a), Sigma A B.

Definition split (A : Set) (B : A -> Set) (C : Sigma A B -> Set) (f : forall (x : A) (y : B x), C (pair A B x y)) (p : Sigma A B) :=
    match p with
        pair x y => f x y
    end.

Definition fst (A : Set) (B : A -> Set) (p : Sigma A B) :=
    split A B (fun _ => A) (fun x y => x) p.

Definition snd (A : Set) (B : A -> Set) (p : Sigma A B) :=
    split A B (fun x => B (fst A B x)) (fun x y => y) p.

Inductive Pi (A : Set) (B : A -> Set) : Set :=
    lambda : (forall x : A, B x) -> Pi A B.

Definition apply (A : Set) (B : A -> Set) (g : Pi A B) (x : A) :=
    match g with
        lambda f => f x
    end.

Notation "A ~> B" := (Pi A (fun _ => B)) (at level 50) : pi_scope.
Open Scope pi_scope.
Notation "~' A" := (A ~> Empty) (at level 45) : pi_scope.

Definition lambda' (A B : Set) (f : A -> B) : A ~> B :=
    lambda A (fun _ => B) f.

Definition apply' (A B : Set) (f : A ~> B) (x : A) :=
    apply A (fun _ => B) f x.

(* HW : \forall x \in A: \not P x <=> \not \exists x \in A : P x *)

Theorem forall_is_exists : forall (A : Set) (B : A -> Set), (Pi A (fun x => ~' (B x))) ~> ~'(Sigma A B).
Proof.
    intros A B.
    refine (lambda' _ _ _).
    intros pi.
    refine (lambda _ _ _).
    intros sigma.
    case sigma.
    intros a b.
    case pi.
    intros hyp.
    case (hyp a).
    intros b_to_empty.
    exact (b_to_empty b).
Qed.

Theorem exists_is_forall : forall (A : Set) (B : A -> Set), ~'(Sigma A B) ~> (Pi A (fun x => ~' (B x))).
Proof.
    intros A B.
    refine (lambda' _ _ _).
    intros not_sigma.
    refine (lambda _ _ _).
    intros a.
    refine (lambda' _ _ _).
    intros b.
    case not_sigma.
    intros sigma_to_empty.
    exact (sigma_to_empty (pair A B a b)).
Qed.

(* Meta-relations *)

Inductive And (A B : Prop) : Prop :=
    conj : A -> B -> And A B.

Implicit Arguments conj.

Inductive Or (A B : Prop) : Prop :=
    inl : A -> Or A B
  | inr : B -> Or A B.

Implicit Arguments inl.
Implicit Arguments inr.

Notation "A /.\ B" := (And A B) (at level 80) : rel_scope.
Notation "A \./ B" := (Or A B) (at level 85) : rel_scope.
Open Scope rel_scope.

Section Relation_Definitions.
    Variable A : Type.
    Definition Relation (S : Type) := S -> S -> Prop.
    Variable R : Relation A.

    Section General_Properties_of_Relations.
        Definition reflexive : Prop := forall x : A, R x x.
        Definition symmetric : Prop := forall x y : A, R x y -> R y x.
        Definition transitive : Prop := forall x y z : A, R x y -> R y z -> R x z.
        Definition antisymmetric : Prop := forall x y : A, R x y -> R y x -> x == y.

        Definition equiv := reflexive /.\ symmetric /.\ transitive.
    End General_Properties_of_Relations.

    Section Meta_Relations.
        Definition inclusion (R1 R2 : Relation A) : Prop := forall x y : A, R1 x y -> R2 x y.
        Definition equality (R1 R2 : Relation A) : Prop := inclusion R1 R2 /.\ inclusion R2 R1.
    End Meta_Relations.
End Relation_Definitions.

Section Extensionality_Definition.
    Variable A B : Type.
    Variable R1 : Relation A.
    Variable R2 : Relation B.

    Definition extensional (f : A -> B) : Prop := forall (x y : A), R1 x y -> R2 (f x) (f y).
End Extensionality_Definition.

Section Theorem_about_Minimal_Relations.
    Variable A : Type.
    Variable R : Relation A.
    Hypothesis reflR : reflexive A R.
    Hypothesis minR : forall S : Relation A, reflexive A S -> inclusion A R S.

    Theorem min_refl_rel_is_equiv :
        equiv A R /.\
        forall (B : Type) (R2 : Relation B), equiv B R2 -> forall (f : A -> B), extensional A B R R2 f.
    Proof.
        (* prove first part *)
        split.
        split.
        split.
        (* prove reflexivity of R *)
        exact reflR.
        (* prove symmetry of R *)
        pose (S x y := R y x).
        assert (reflexive A S).
        unfold reflexive.
        intros x.
        exact (reflR x).
        pose (inclRS := minR S H).
        unfold symmetric.
        intros x y.
        exact (inclRS x y).
        (* prove transitivity of R *)
        pose (T x y := forall z, R y z -> R x z).
        assert (reflexive A T).
        unfold reflexive, T.
        intros x z.
        intuition.
        pose (inclRT := minR T H).
        unfold transitive.
        intros.
        exact (inclRT x y H0 z H1).
        (* prove second part *)
        intros.
        unfold extensional.
        intros.
        pose (F x y := R2 (f x) (f y)).
        (* prove reflexivity of F *)
        assert (reflexive A F).
        unfold reflexive.
        intros x0.
        unfold F.
        assert (reflexive B R2).
        destruct H as [r].
        destruct r as [r].
        exact r.
        exact (H1 (f x0)).
        exact (minR F H1 x y H0).
    Qed.
End Theorem_about_Minimal_Relations.

Lemma inclusion_is_reflexive : forall (A : Type), reflexive (Relation A) (inclusion A).
Proof.
    unfold reflexive, inclusion.
    intuition.
Qed.

Lemma inclusion_is_transitive : forall (A : Type), transitive (Relation A) (inclusion A).
Proof.
    unfold transitive, inclusion.
    intuition.
Qed.

Theorem rels_equality_is_equiv_rel : forall (T : Type), equiv (Relation T) (equality T).
Proof.
    intros T.
    unfold equality.
    split.
    split.
    unfold reflexive.
    intros.
    split.
    exact (inclusion_is_reflexive T x).
    exact (inclusion_is_reflexive T x).
    unfold symmetric.
    intros.
    intuition.
    unfold transitive.
    intros.
    destruct H.
    destruct H0.
    exact (conj (inclusion_is_transitive T x y z H H0) (inclusion_is_transitive T z y x H2 H1)).
Qed.
