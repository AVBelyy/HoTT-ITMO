(* Equality *)

Inductive Id {A : Type} (a : A) : A -> Type :=
    id : Id a a.
Notation "A == B" := (Id A B) (at level 70) : id_scope.

Open Scope id_scope.

Notation "~ A" := (A -> False) : id_scope.
Notation "A /= B" := (~(A == B)) (at level 70) : id_scope.

(* Theorems *)

Theorem minus_right_zero : forall n, n - 0 == n.
Proof.
    intros.
    elim n.
    exact (id _).
    intros.
    exact (id _).
Qed.

Theorem plus_one_is_succ : forall n, n + 1 == S n.
Proof.
    intros.
    elim n.
    exact (id _).
    intros.
    simpl.
    rewrite H.
    exact (id _).
Qed.

Theorem sth_useless : forall n, n + 1 - 1 == n.
Proof.
    intros.
    elim n.
    exact (id _).
    intros.
    rewrite <- H.
    simpl.
    rewrite minus_right_zero.
    rewrite H.
    rewrite plus_one_is_succ.
    exact (id _).
Qed.

Fixpoint natrec (C : nat -> Set) (d : C 0) (e : forall (x : nat) (y : C x), (C (S x))) (n : nat) : C n :=
    match n with
         0 => d
    | S n' => e n' (natrec C d e n')
    end.

Definition summ (r : nat) (f : nat -> nat) : nat :=
    natrec (fun _ => nat) (f r) (fun x y => x + f y) r.

Theorem summ_of_ones :

Theorem summ_of_conseq_nats : forall n, summ n (fun x => x + x) == n * (n + 1).
Proof.
    intros.
    elim n.
    simpl.
    unfold summ.
    unfold natrec.
    exact (id _).
    intros.
    simpl.
    unfold summ.
    unfold natrec.
    fold natrec.
    fold summ.
Qed.
