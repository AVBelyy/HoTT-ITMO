(* Identity *)

Inductive Id {A : Type} (a : A) : A -> Type :=
    id : Id a a.
Notation "A == B" := (Id A B) (at level 70) : id_scope.

Open Scope id_scope.

Notation "~ A" := (A -> False) : id_scope.
Notation "A /= B" := (~(A == B)) (at level 70) : id_scope.

(* Natural numbers *)

Inductive Nat : Set :=
    zero : Nat
  | succ : Nat -> Nat.

Fixpoint plus (n m : Nat) : Nat :=
    match n with
        zero => m
      | succ n' => succ (plus n' m)
    end.
Notation "A + B" := (plus A B) : hw_scope.

Open Scope hw_scope.

Fixpoint mul (n m : Nat) : Nat :=
    match n with
        zero => zero
      | succ n' => m + mul n' m
    end.

Notation "A * B" := (mul A B) : hw_scope.

(* HW1 : plus commutes and associates, mul commutes and distributes *)

Lemma plus_right_zero : forall a, a + zero == a.
Proof.
    intros a.
    elim a.
    exact (id _).
    intros n0 ind_hyp.
    simpl.
    rewrite ind_hyp.
    exact (id _).
Qed.

Lemma plus_shift_succ : forall a b, succ (a + b) == a + succ b.
Proof.
    intros a b.
    elim a.
    simpl.
    exact (id _).
    intros n ind_hyp.
    simpl.
    rewrite ind_hyp.
    exact (id _).
Qed.

Lemma mul_right_zero : forall a, a * zero == zero.
Proof.
    intros a.
    elim a.
    exact (id _).
    intros n ind_hyp.
    simpl.
    exact ind_hyp.
Qed.

Lemma mul_one : forall a, a * succ zero == a.
Proof.
    intros a.
    elim a.
    exact (id _).
    intros n ind_hyp.
    simpl.
    rewrite ind_hyp.
    exact (id _).
Qed.

Theorem plus_comm : forall a b, a + b == b + a.
Proof.
    intros a b.
    elim a.
    elim b.
    exact (id _).
    intros n ind_hyp.
    simpl.
    assert (n + zero == n).
    exact (plus_right_zero n).
    rewrite plus_right_zero.
    exact (id _).
    intros n ind_hyp.
    simpl.
    rewrite ind_hyp.
    exact (plus_shift_succ b n).
Qed.

Theorem plus_assoc : forall a b c, (a + b) + c == a + (b + c).
Proof.
    intros a b c.
    elim a.
    elim b.
    elim c.
    exact (id _).
    intros n ind_hyp.
    exact (id _).
    intros n ind_hyp.
    exact (id _).
    intros n ind_hyp.
    simpl.
    rewrite <- ind_hyp.
    exact (id _).
Qed.

Lemma mul_succ_not_needed : forall a b, a * succ b == a * b + a.
Proof.
    intros a b.
    elim a.
    exact (id _).
    intros n ind_hyp.
    simpl.
    rewrite ind_hyp.
    rewrite (plus_shift_succ b (n * b + n)).
    rewrite (plus_shift_succ (n * b) n).
    rewrite (plus_assoc b (n * b) (succ n)).
    exact (id _).
Qed.

Theorem mul_comm : forall a b, a * b == b * a.
Proof.
    intros a b.
    elim a.
    assert (b * zero == zero).
    exact (mul_right_zero b).
    rewrite mul_right_zero.
    exact (id _).
    intros n ind_hyp.
    simpl.
    rewrite mul_succ_not_needed.
    rewrite ind_hyp.
    rewrite plus_comm.
    exact (id _).
Qed.

Theorem mul_distr : forall a b c, a * (b + c) == a * b + a * c.
Proof.
    intros a b c.
    elim a.
    simpl.
    exact (id _).
    intros n ind_hyp.
    simpl.
    rewrite ind_hyp.
    rewrite (plus_assoc b (n * b) (c + (n * c))).
    rewrite (plus_comm (n * b) (c + (n * c))).
    rewrite (plus_assoc c (n * c) (n * b)).
    rewrite <- (plus_assoc b c ((n * c) + (n * b))).
    rewrite (plus_comm (n * c) (n * b)).
    exact (id _).
Qed.
