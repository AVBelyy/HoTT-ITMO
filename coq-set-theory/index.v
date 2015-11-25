(* c= *)
Definition Subq : set->set->Prop :=
fun X Y => forall x:set, x :e X -> x :e Y.

Lemma Subq_ref : forall X:set, X c= X.
Qed.

Lemma Subq_tra : forall X Y Z:set, X c= Y -> Y c= Z -> X c= Z.
Qed.

Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X == Y.
Theorem set_ext_inv : forall X Y:set, X == Y -> (X c= Y /_\ Y c= X).
(* HW *)
Qed.


Parameter Empty : set.
Axiom EmptyAx : ~' exists x, x :e Empty.

Lemma EmptyE : forall x:set, x /:e Empty.
(* CW *)
Qed.


Parameter Union : set->set.
Axiom UnionEq : forall X:set, forall x:set, x :e Union X <=> exists Y, x :e Y /_\ Y :e X.

Lemma UnionE :
forall X x:set, x :e (Union X) -> exists Y, x :e Y /_\ Y :e X.
(* CW *)
Qed.

Lemma UnionI :
forall X x Y:set, x :e Y -> Y :e X -> x :e (Union X).
(* CW *)
Qed.


Parameter Power : set->set.
Axiom PowerEq : forall X Y:set, Y :e Power X <=> Y c= X.

Lemma PowerE : forall X Y:set, Y :e Power X -> Y c= X.
(* CW *)
Qed.

Lemma PowerI : forall X Y:set, Y c= X -> Y :e (Power X).
(* CW *)
Qed.

Lemma In_Power : forall X:set, X :e Power X.
(* CW *)
Qed.

(* { x :i X | P } *)
Parameter Sep : set -> (set -> Prop) -> set.
Axiom SepEq : forall X:set, forall P:set -> Prop, forall x, x :e {z :i X | P z} <=> x :e X /_\ P x.

Lemma SepI : forall X:set, forall P:set -> Prop, forall x:set,
 x :e X -> P x -> x :e {z :i X|P z}.
(* CW *)
Qed.

Lemma SepE : forall X:set, forall P:set -> Prop, forall x:set,
x :e {z :i X|P z} -> x :e X /_\ P x.
(* CW *)
Qed.

Lemma SepE1 : forall X:set, forall P:set -> Prop, forall x:set,
 x :e {z :i X|P z} -> x :e X.
(* CW *)
Qed.

Lemma SepE2 : forall X:set, forall P:set -> Prop, forall x:set,
 x :e {z :i X|P z} -> P x.
(* CW *)
Qed.

Parameter Repl : set->(set->set)->set.
Axiom ReplEq :
forall X:set, forall F:set->set, forall y:set, y :e {F z|z :i X} <=> exists x, x :e X /_\ y == F x.

(* HW *)
Lemma ReplE :
forall X:set, forall F:set->set, forall y:set, y :e {F z|z :i X} -> exists x, x :e X /_\ y == F x.
Qed.
Lemma ReplI :
forall X:set, forall F:set->set, forall x:set, x :e X -> F x :e {F x|x :i X}.
Qed.

Lemma Subq_Empty : forall X:set, Empty c= X.
(* CW *)
Qed.
Lemma Empty_Power : forall X:set, Empty :e Power X.
(* CW *)
Qed.
Lemma Repl_Empty : forall F:set -> set, {F x|x :i Empty} == Empty.
(* CW *)
Qed.

Parameter Descr : ((set->Prop)->set).
Axiom DescrR : forall P:set->Prop, (exists! x, P x) -> P (Descr P).

(* {x, y} *)
Definition TSet : set := {X :i Power (Power Empty) | Empty :e X \_/ Empty /:e X}.
Definition UPair : set->set->set :=
 fun y z:set =>
 {Descr (fun w:set => forall p:set->Prop, (Empty /:e X -> p y) -> (Empty :e X  -> p z) -> p w)|X :i TSet}.

(* HW *)
Lemma UPairE :
forall x y z:set, x :e {y,z} -> x == y \_/ x == z.
Qed.
Lemma UPairI1 :
forall y z:set, y :e {y,z}.
Qed.
Lemma UPairI2 :
forall y z:set, z :e {y,z}.
Qed.

(* CW *)
Lemma UPairEq :
forall x y z, x :e {y,z} <=> x == y \_/ x == z.
Qed.

(* {| y |} *)
Definition Sing : set->set := fun y:set => {y,y}.

Lemma SingI : forall y, y :e {| y |}.
Qed.
Lemma SingE : forall x y, x :e {| y |} -> x == y.
Qed.
Lemma SingEq : forall x y, x :e {| y |} <=> x == y.
(* CW *)
Qed.

(* :u: *)
Definition binunion : set -> set -> set := fun X Y => Union {X,Y}.
Lemma binunionI1 : forall X Y z, z :e X -> z :e X :u: Y.
(* CW *)
Qed.

Lemma binunionI2 : forall X Y z, z :e Y -> z :e X :u: Y.
(* CW *)
Qed.

Lemma binunionE : forall X Y z, z :e X :u: Y -> z :e X \_/ z :e Y.
(* HW *)
Qed.

Lemma binunionEq : forall X Y z, z :e X :u: Y <=> z :e X \_/ z :e Y.
(* CW *)
Qed.
