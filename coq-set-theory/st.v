Parameter set : Type.

Definition False : Prop := forall P:Prop, P.

Definition not : Prop->Prop := fun A:Prop => A -> False.

Notation "~' x" := (not x) (at level 75, right associativity).

Definition and : Prop->Prop->Prop := fun A B:Prop => forall P:Prop, (A -> B -> P) -> P.

Notation "A /_\ B" := (and A B) (at level 80).

Theorem andI : forall (A B : Prop), A -> B -> A /_\ B.
exact (fun A B a b P H => H a b).
Qed.

Definition or : Prop->Prop->Prop := fun (A B : Prop) => forall P:Prop, (A -> P) -> (B -> P) -> P.

Notation "A \_/ B" := (or A B) (at level 85).

Theorem orIL : forall (A B : Prop), A -> A \_/ B.
exact (fun A B a P H1 H2 => H1 a).
Qed.

Theorem orIR : forall (A B : Prop), B -> A \_/ B.
exact (fun A B b P H1 H2 => H2 b).
Qed.

Definition iff : Prop->Prop->Prop := fun (A B:Prop) => (A -> B) /_\ (B -> A).

Notation "A <=> B" := (iff A B) (at level 95).

Theorem iffI : forall A B:Prop, (A -> B) -> (B -> A) -> (A <=> B).
exact (fun A B => andI (A -> B) (B -> A)).
Qed.

(** Equality can be defined polymorphically as Leibniz equality. As we will only need equality at the type of sets,
 we only define equality on sets using Leibniz equality. **)
Definition eq : set->set->Prop := fun (x y : set) => forall Q:set -> Prop, Q x -> Q y.

Notation "x == y" := (eq x y) (at level 70).
Notation "x /= y" := (~' x == y) (at level 70).

Theorem eqI : forall x:set, x == x.
exact (fun x q H => H).
Qed.

Theorem eq_sym : forall x y:set, x == y -> y == x.
exact (fun x y H => H (fun y => eq y x) (eqI x)).
Qed.

(** Existentials can also be defined polymorphically, but we will only need them for sets and for functions from set to set.
    To emphasize this, we define existential quantification separately for these two instance types. **)
Definition ex : (set->Prop)->Prop := fun P:set->Prop => forall Q:Prop, (forall x, P x -> Q) -> Q.

Notation "'exists' x , p" := (ex (fun x => p))
  (at level 200, x ident).

Theorem exI : forall P:set->Prop, forall x:set, P x -> exists x, P x.
exact (fun P x H1 Q H2 => H2 x H1).
Qed.

Definition ex_f : ((set->set)->Prop)->Prop := fun P:(set->set)->Prop => forall Q:Prop, (forall x, P x -> Q) -> Q.

Notation "'existsf' x , p" := (ex_f (fun x => p))
  (at level 200, x ident).

Theorem exI_f : forall P:(set->set)->Prop, forall F:set->set, P F -> existsf F, P F.
exact (fun P F H1 Q H2 => H2 F H1).
Qed.

Definition exu : (set->Prop)->Prop := fun P:set->Prop => (exists x, P x) /_\ (forall x y:set, P x -> P y -> x == y).

Notation "'exists!' x , p" := (exu (fun x => p))
  (at level 200, x ident).

Theorem exuI : forall P:set->Prop, (exists x, P x) -> (forall x y:set, P x -> P y -> x == y) -> exists! x, P x.
exact (fun P => andI (ex P) (forall x y:set, P x -> P y -> eq x y)).
Qed.

(** ** Description Operator *)

Parameter Descr : ((set->Prop)->set).

Axiom DescrR : forall P:set->Prop, (exists! x, P x) -> P (Descr P).

(** ** Axioms of Set Theory: ZF without Infinity **)

(** In is the membership relation on i.  We use x :e y as notation to mean "x is a member of y" and x /:e y as notation for "x is not a member of y." **)

Parameter In:set->set->Prop.

Notation "x ':e' y" := (In x y) (at level 70).
Notation "x '/:e' y" := (~' (In x y)) (at level 70).

(** Subq is the subset relation on set.  We use X c= Y as notation to mean "X is a subset of Y" and X /c= Y as notation for "X is not a subset of Y." **)

Definition Subq : set->set->Prop :=
fun X Y => forall x:set, x :e X -> x :e Y.

Notation "X 'c=' Y" := (Subq X Y) (at level 70).
Notation "X '/c=' Y" := (~' (Subq X Y)) (at level 70).

Lemma Subq_ref : forall X:set, X c= X.
intros X x H1. exact H1.
Qed.

Lemma Subq_tra : forall X Y Z:set, X c= Y -> Y c= Z -> X c= Z.
intros X Y Z H1 H2 x H3. apply H2. apply H1. exact H3.
Qed.

(** Two sets are equal if they have the same elements. Equivalently, we can always prove two sets are equal by proving they are subsets of each other. **)

Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X == Y.

(** Sets are formed iteratively, so we can prove Properties about all sets by induction on membership.
Suppose P is a Property of sets. If we can prove P holds for X from the inductive hypothesis that P holds for all member of X,
then P must hold for all sets. **)

Axiom In_ind : forall P:set->Prop, (forall X:set, (forall x, x :e X -> P x) -> P X) -> forall X:set, P X.

(** Empty is the empty set. **)

Parameter Empty : set.

Axiom EmptyAx : ~' exists x, x :e Empty.

Lemma EmptyE : forall x:set, x /:e Empty.
exact (fun x H => EmptyAx (exI (fun x => x :e Empty) x H)).
Qed.

(** Given a set X, (Union X) is the set {x | there is some Y such that x :e Y and Y :e X}. That is, Union gives the union of a set of sets. **)

Parameter Union : set->set.

Axiom UnionEq : forall X:set, forall x:set, x :e Union X <=> exists Y, x :e Y /_\ Y :e X.

Lemma UnionE :
forall X x:set, x :e (Union X) -> exists Y, x :e Y /_\ Y :e X.
exact (fun X x : set =>
UnionEq X x (x :e Union X -> exists Y, x :e Y /_\ Y :e X)
  (fun (H1 : x :e Union X -> exists Y, x :e Y /_\ Y :e X)
     (_ : (exists Y, x :e Y /_\ Y :e X) -> x :e Union X) => H1)).
Qed.

Lemma UnionI :
forall X x Y:set, x :e Y -> Y :e X -> x :e (Union X).
exact (fun (X x Y : set) (H1 : x :e Y) (H2 : Y :e X) =>
UnionEq X x (x :e Union X)
  (fun (_ : x :e Union X -> exists Y, x :e Y /_\ Y :e X)
     (H4 : (exists Y, x :e Y /_\ Y :e X) -> x :e Union X) =>
   H4
     (exI (fun Y0 : set => x :e Y0 /_\ Y0 :e X) Y
        (andI (x :e Y) (Y :e X) H1 H2)))).
Qed.

(** (Power X) is the set of all subsets of X. **)

Parameter Power : set->set.

Axiom PowerEq : forall X Y:set, Y :e Power X <=> Y c= X.

Lemma PowerE : forall X Y:set, Y :e Power X -> Y c= X.
exact (fun X Y : set =>
PowerEq X Y (Y :e Power X -> Y c= X)
  (fun (H1 : Y :e Power X -> Y c= X) (_ : Y c= X -> Y :e Power X) => H1)).
Qed.

Lemma PowerI : forall X Y:set, Y c= X -> Y :e (Power X).
exact (fun X Y : set =>
PowerEq X Y (Y c= X -> Y :e Power X)
  (fun (_ : Y :e Power X -> Y c= X) (H2 : Y c= X -> Y :e Power X) => H2)).
Qed.

(** In classical set theory, Separation follows from Replacement.
Separation does not generally follow from Replacement in intuitionistic set theory,
although there are alternative formulations of Replacement which are intuitionistically equivalent to
the combination of Separation and Replacement as used here.
 **)
Parameter Sep : set -> (set -> Prop) -> set.

Notation "{ x :i X | P }" := (Sep X (fun x:set => P)).

Axiom SepEq : forall X:set, forall P:set -> Prop, forall x, x :e {z :i X | P z} <=> x :e X /_\ P x.

Lemma SepI :  forall X:set, forall P:set -> Prop, forall x:set,
 x :e X -> P x -> x :e {z :i X|P z}.
exact (fun (X : set) (P : set -> Prop) (x : set) (H1 : x :e X) (H2 : P x) =>
SepEq X P x (x :e Sep X P)
  (fun (_ : x :e Sep X P -> x :e X /_\ P x)
     (H3 : x :e X /_\ P x -> x :e Sep X P) => H3 (andI (x :e X) (P x) H1 H2))).
Qed.

Lemma SepE :  forall X:set, forall P:set -> Prop, forall x:set,
 x :e {z :i X|P z} -> x :e X /_\ P x.
intros X P x H1. apply (SepEq X P x). exact (fun H2 _ => H2 H1).
Qed.

Lemma SepE1 :  forall X:set, forall P:set -> Prop, forall x:set,
 x :e {z :i X|P z} -> x :e X.
exact (fun (X : set) (P : set -> Prop) (x : set) (H1 : x :e Sep X P) =>
SepEq X P x (x :e X)
  (fun (H2 : x :e Sep X P -> x :e X /_\ P x)
     (_ : x :e X /_\ P x -> x :e Sep X P) =>
   H2 H1 (x :e X) (fun (H3 : x :e X) (_ : P x) => H3))).
Qed.

Lemma SepE2 :  forall X:set, forall P:set -> Prop, forall x:set,
 x :e {z :i X|P z} -> P x.
exact (fun (X : set) (P : set -> Prop) (x : set) (H1 : x :e Sep X P) =>
SepEq X P x (P x)
  (fun (H2 : x :e Sep X P -> x :e X /_\ P x)
     (_ : x :e X /_\ P x -> x :e Sep X P) =>
   H2 H1 (P x) (fun (_ : x :e X) (H3 : P x) => H3))).
Qed.

(** Given a set X and a function F, (Repl X F) is the set {F x|x :e X}. That is, Repl allows us to form a set by
 replacing the elements x in a set X with corresponding elements F x.
 I write (Repl X F) in the eta-expanded form (Repl X (fun z => F z)) just so I can legitimately use the binder notation
 in the written description.
 **)

Parameter Repl : set->(set->set)->set.

Notation "{ F | x :i X }" := (Repl X (fun x:set => F)).

Axiom ReplEq :
forall X:set, forall F:set->set, forall y:set, y :e {F z|z :i X} <=> exists x, x :e X /_\ y == F x.

Lemma ReplE :
forall X:set, forall F:set->set, forall y:set, y :e {F z|z :i X} -> exists x, x :e X /_\ y == F x.
exact (fun (X : set) (F : set -> set) (y : set) =>
ReplEq X F y
  (y :e Repl X (fun x : set => F x) -> exists x, x :e X /_\ y == F x)
  (fun
     (H1 : y :e Repl X (fun x : set => F x) ->
           exists x, x :e X /_\ y == F x)
     (_ : (exists x, x :e X /_\ y == F x) ->
          y :e Repl X (fun x : set => F x)) => H1)).
Qed.

Lemma ReplI :
forall X:set, forall F:set->set, forall x:set, x :e X -> F x :e {F x|x :i X}.
exact (fun (X : set) (F : set -> set) (x : set) (H1 : x :e X) =>
ReplEq X F (F x) (F x :e Repl X (fun x0 : set => F x0))
  (fun
     (_ : F x :e Repl X (fun x0 : set => F x0) ->
          exists x0, x0 :e X /_\ F x == F x0)
     (H4 : (exists x0, x0 :e X /_\ F x == F x0) ->
           F x :e Repl X (fun x0 : set => F x0)) =>
   H4
     (exI (fun x0 : set => x0 :e X /_\ F x == F x0) x
        (andI (x :e X) (F x == F x) H1 (eqI (F x)))))).
Qed.

Lemma Subq_Empty : forall X:set, Empty c= X.
Proof.
    (* CW *)
    exact (fun (X x : set) (H : x :e Empty) => EmptyE x H (x :e X)).
Qed.

Lemma Empty_Power : forall X:set, Empty :e Power X.
Proof.
    (* CW *)
    intros X. apply PowerI. apply Subq_Empty.
Qed.

Lemma In_Power : forall X:set, X :e Power X.
Proof.
    (* CW *)
    intros X. apply PowerI. apply Subq_ref.
Qed.

Lemma Repl_Empty : forall F:set -> set, {F x|x :i Empty} == Empty.
Proof.
    (* HW *)
    exact (fun F : set -> set =>
    set_ext (Repl Empty F) Empty
      (fun (x : set) (H1 : x :e Repl Empty F) =>
       ReplE Empty F x H1 (x :e Empty)
         (fun (y : set) (H1' : y :e Empty /_\ x == F y) =>
          H1' (x :e Empty)
            (fun (H2 : y :e Empty) (_ : x == F y) => EmptyE y H2 (x :e Empty))))
      (fun (x : set) (H1 : x :e Empty) => EmptyE x H1 (x :e Repl Empty F))).
Qed.

(** Given two sets y and z, (UPair y z) is {y,z}. **)
(** Unordered pairs are often taken as primitives in ZF, but they are definable from the primitives above.
    Zermelo [1930] pointed this out in classical ZF. The argument is given in Suppes [1960;Dover version 1972]
    and formalized in Isabelle-ZF by Paulson [1993].
    The argument in the classical case is a little simpler since (Power (Power Empty)) is a two element set.
    In the intuitionistic case, we use separation to extract a two element subset of (Power (Power Empty)) before using replacement.
 **)
Definition TSet : set := {X :i Power (Power Empty) | Empty :e X \_/ Empty /:e X}.
Definition UPair : set->set->set :=
 fun y z:set =>
 {Descr (fun w:set => forall p:set->Prop, (Empty /:e X -> p y) -> (Empty :e X  -> p z) -> p w)|X :i TSet}.

Notation "{ x , y }" := (UPair x y).

Lemma UPairE :
forall x y z:set, x :e {y,z} -> x == y \_/ x == z.
intros x y z H1. apply ReplE in H1. apply H1.
intros u H2. apply H2. intros H3 H4.
apply (SepE _ _ _ H3). intros H5 H6. apply (eq_sym _ _ H4).
apply (DescrR (fun v:set => forall p:set->Prop, (Empty /:e u -> p y) -> (Empty :e u  -> p z) -> p v)).
- apply exuI.
  + apply H6.
    * intros H7. apply (exI _ z). intros p _ H8. exact (H8 H7).
    * intros H7. apply (exI _ y). intros p H8 _. exact (H8 H7).
  + intros v w H7 H8. apply H7.
    * { intros H9 p H10. apply H8.
        - intros _. exact H10.
        - intros H11. apply (H9 H11).
      }
    * { intros H9 p H10. apply H8.
        - intros H11. apply (H11 H9).
        - intros _. exact H10.
      }
- intros _. apply orIL. apply eqI.
- intros _. apply orIR. apply eqI.
Qed.

Lemma UPairI1 :
forall y z:set, y :e {y,z}.
intros y z.
assert (H1:Descr (fun v => forall p:set->Prop, (Empty /:e Empty -> p y) -> (Empty :e Empty  -> p z) -> p v) == y).
{
  apply (DescrR (fun v => forall p:set->Prop, (Empty /:e Empty -> p y) -> (Empty :e Empty  -> p z) -> p v)).
  - apply exuI.
    + apply (exI _ y). intros p H2 _. apply H2. apply EmptyE.
    + intros v w H2 H3. apply H2.
      * { intros H4 p H5. apply H3.
          - intros _. exact H5.
          - intros H6. apply (EmptyE _ H6).
        }
      * intros H4. apply (EmptyE _ H4).
  - intros _. apply eqI.
  - intros H2. apply (EmptyE _ H2).
}
apply (H1 (fun w => w :e UPair y z)).
change ((fun u => Descr (fun v => forall p:set->Prop, (Empty /:e u -> p y) -> (Empty :e u  -> p z) -> p v)) Empty :e UPair y z).
apply ReplI. apply SepI.
- apply Empty_Power.
- apply orIR. apply EmptyE.
Qed.

Lemma UPairI2 :
forall y z:set, z :e {y,z}.
intros y z.
assert (H1:Descr (fun v => forall p:set->Prop, (Empty /:e Power Empty -> p y) -> (Empty :e Power Empty  -> p z) -> p v) == z).
{
  apply (DescrR (fun v => forall p:set->Prop, (Empty /:e Power Empty -> p y) -> (Empty :e Power Empty  -> p z) -> p v)).
  - apply exuI.
    + apply (exI _ z). intros p _ H2. apply H2. apply Empty_Power.
    + intros v w H2 H3. apply H2.
      * intros H4. apply H4. apply Empty_Power.
      * { intros H4 p H5. apply H3.
          - intros H6. apply H6. apply Empty_Power.
          - intros _. exact H5.
        }
  - intros H2. apply H2. apply Empty_Power.
  - intros _. apply eqI.
}
apply (H1 (fun w => w :e UPair y z)).
change ((fun u => Descr (fun v => forall p:set->Prop, (Empty /:e u -> p y) -> (Empty :e u  -> p z) -> p v)) (Power Empty) :e UPair y z).
apply ReplI. apply SepI.
- apply In_Power.
- apply orIL. apply Empty_Power.
Qed.

Lemma UPairEq :
forall x y z, x :e {y,z} <=> x == y \_/ x == z.
intros x y z. apply andI. apply UPairE. intros H1. apply H1.
intros H2. apply H2. apply UPairI1.
intros H2. apply H2. apply UPairI2.
Qed.


Definition Sing : set->set := fun y:set => {y,y}.

Notation "{| y |}" := (Sing y).

Lemma SingI : forall y, y :e {| y |}.
Proof.
  intros y. unfold Sing. apply UPairI1.
Qed.

Lemma SingE : forall x y, x :e {| y |} -> x == y.
Proof.
  intros x y H1. apply (UPairE _ _ _ H1). exact (fun H => H). exact (fun H => H).
Qed.

Lemma SingEq : forall x y, x :e {| y |} <=> x == y.
Proof.
    (* CW *)
    intros x y. apply andI. apply SingE. intros H. apply H. apply SingI.
Qed.

(** Given sets X and Y, binunion X Y is the binary union of X and Y. **)
Definition binunion : set -> set -> set := fun X Y => Union {X,Y}.

Notation "X :u: Y" := (binunion X Y) (at level 40).

Lemma binunionI1 : forall X Y z, z :e X -> z :e X :u: Y.
exact (fun (X Y z : set) (H1 : z :e X) => UnionI (UPair X Y) z X H1 (UPairI1 X Y)).
Qed.

Lemma binunionI2 : forall X Y z, z :e Y -> z :e X :u: Y.
exact (fun (X Y z : set) (H1 : z :e Y) => UnionI (UPair X Y) z Y H1 (UPairI2 X Y)).
Qed.

Lemma binunionE : forall X Y z, z :e X :u: Y -> z :e X \_/ z :e Y.
exact (fun (X Y z : set) (H1 : z :e binunion X Y) =>
UnionE (UPair X Y) z H1 (z :e X \_/ z :e Y)
  (fun (w : set) (H1' : z :e w /_\ w :e UPair X Y) =>
   H1' (z :e X \_/ z :e Y)
     (fun (H2 : z :e w) (H3 : w :e UPair X Y) =>
      UPairE w X Y H3 (z :e X \_/ z :e Y)
        (fun H4 : w == X =>
         orIL (z :e X) (z :e Y) (H4 (fun X0 : set => z :e X0) H2))
        (fun H4 : w == Y =>
         orIR (z :e X) (z :e Y) (H4 (fun Y0 : set => z :e Y0) H2))))).
Qed.

Lemma binunionEq : forall X Y z, z :e X :u: Y <=> z :e X \_/ z :e Y.
intros X Y z. apply andI. apply binunionE. intros H1. apply H1. apply binunionI1. apply binunionI2.
Qed.

(** Given sets X and Y, setminus X Y is {x :e X | x /:e Y}. **)
Definition setminus : set -> set -> set := fun X Y => {x :i X| x /:e Y}.

Notation "X \ Y" := (setminus X Y) (at level 40).

Lemma setminusI : forall X Y z, z :e X -> z /:e Y -> z :e X \ Y.
exact (fun (X Y z : set) (H1 : z :e X) (H2 : z /:e Y) => SepI X (fun x : set => x /:e Y) z H1 H2).
Qed.

Lemma setminusE1 : forall X Y z, z :e X \ Y -> z :e X.
exact (fun (X Y z : set) (H1 : z :e setminus X Y) => SepE1 X (fun x : set => x /:e Y) z H1).
Qed.

Lemma setminusE2 : forall X Y z, z :e X \ Y -> z /:e Y.
exact (fun (X Y z : set) (H1 : z :e setminus X Y) => SepE2 X (fun x : set => x /:e Y) z H1).
Qed.

Lemma setminusEq : forall X Y z, z :e X \ Y <=> z :e X /_\ z /:e Y.
intros X Y. apply SepEq.
Qed.

(** Given a set X and a function F from sets to sets, famunion X F is the union of all F x where x ranges over X. **)
Definition famunion : set -> (set -> set) -> set :=
fun X F => Union {F x|x :i X}.

Notation "'U' x : X , F" := (famunion X (fun x => F))
  (at level 200, x ident).

Lemma famunionI : forall X:set, forall F:set -> set, forall x y:set, x :e X -> y :e (F x) -> y :e U x:X, F x.
exact (fun (X : set) (F : set -> set) (x y : set) (H1 : x :e X) (H2 : y :e F x) =>
UnionI (Repl X F) y (F x) H2 (ReplI X F x H1)).
Qed.

Lemma famunionE : forall X:set, forall F:set -> set, forall y:set, y :e (U x:X, F x) -> exists x, x :e X /_\ y :e (F x).
exact (fun (X : set) (F : set -> set) (y : set) (H1 : y :e famunion X F) =>
UnionE (Repl X F) y H1 (exists x, x :e X /_\ y :e F x)
  (fun (z : set) (H1' : y :e z /_\ z :e Repl X F) =>
   H1' (exists x, x :e X /_\ y :e F x)
     (fun (H2 : y :e z) (H3 : z :e Repl X F) =>
      ReplE X F z H3 (exists x, x :e X /_\ y :e F x)
        (fun (x : set) (H3' : x :e X /_\ z == F x) =>
         H3' (exists x0, x0 :e X /_\ y :e F x0)
           (fun (H4 : x :e X) (H5 : z == F x) =>
            exI (fun x0 : set => x0 :e X /_\ y :e F x0) x
              (andI (x :e X) (y :e F x) H4 (H5 (fun s : set => y :e s) H2))))))).
Qed.

Lemma famunionEq : forall X:set, forall F:set -> set, forall y:set, y :e (U x:X, F x) <=> exists x, x :e X /_\ y :e (F x).
intros X F y. apply andI. apply famunionE. intros H1. apply H1. intros x H2. apply H2. intros H3 H4.
exact (famunionI _ _ _ _ H3 H4).
Qed.
