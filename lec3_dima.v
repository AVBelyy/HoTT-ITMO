Inductive Bool: Set:=
true': Bool
| false':Bool.

Definition or' (a b : Bool) := if a then true' else b.

Inductive True':Prop :=
  I':True'.

Inductive False' : Prop :=.

Definition Is_true (a:Bool) : Prop := match a with
  true' => True'
| false' => False'
end.

Definition not' (A: Prop) := A -> False'.
Notation "~' A" := (not' A) (at level 75, right associativity): Prop_scope.
Open Scope Prop_scope.

Theorem or_commutes : forall a b, Is_true(or' a b) -> Is_true(or' b a).
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

Inductive Id(A:Type) (x:A) : A->Prop :=
  id : Id A x x.

Notation "x =' y :> A" := (id A x y) (at level 60) : Id_scope.
Open Scope Id_scope.

Theorem zero_neutral_right : forall n, Id Nat (n + Zero) n.
Proof.
  intros n.
  simpl.
  exact (id _ n).
Qed.

Theorem zero_neutral_left : forall n, Id Nat (Zero + n) n.
Proof.
  intros n.
  unfold plus'.
  elim n.
  simpl.
  exact (id _ Zero).
  intros n0.
  intros ind_hyp.
  simpl.
  rewrite ind_hyp.
  exact (id _ _).
Qed.

Theorem comm_plus : forall n m, Id Nat (n + m) (m + n).
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
  exact (id _ _).
  intros n1 ind_hyp2.
  simpl.
  rewrite ind_hyp2.
  exact (id _ _).
Qed.
