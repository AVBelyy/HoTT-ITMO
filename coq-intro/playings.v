Theorem identity : forall A B : Prop, A -> B -> A.
Proof.
    intros.
    exact H.
Qed.

Theorem forward_small : forall A B : Prop, A -> (A -> B) -> B.
Proof.
    intros A B.
    intros poA atob.
    pose (poB := atob poA).
    exact poB.
Qed.

Theorem backward_small : forall A B : Prop, A -> (A -> B) -> B.
Proof.
    intros A B.
    intros poA atob.
    refine (atob _).
    exact poA.
Qed.

Theorem backward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
    intros A B C.
    intros a ab abc.
    refine (abc _ _).
    exact a.
    refine (ab _).
    exact a.
Qed.

Inductive Or (A B : Prop) : Prop :=
    | inlS : A -> Or A B
    | inrS : B -> Or A B.

Inductive And (A B : Prop) : Prop :=
    | conjS : A -> B -> And A B.

Notation "A || B" := (Or A B) : my_scope.
Notation "A && B" := (And A B) : my_scope.

Open Scope my_scope.

Theorem or_commutes : forall A B, A || B -> B || A.
Proof.
    intros A B.
    intros A_or_B.
    case A_or_B.
    intros proof_of_A.
    refine (inrS _ _ _).
    exact proof_of_A.
    intros proof_of_B.
    refine (inlS _ _ _).
    exact proof_of_B.
Qed.

Theorem and_commutes : forall A B, A && B -> B && A.
Proof.
    intros A B.
    intros A_and_B.
    case A_and_B.
    intros proof_of_A proof_of_B.
    refine (conjS _ _ _ _).
    exact proof_of_B.
    exact proof_of_A.
Qed.
