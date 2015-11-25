Module Basics.

(* Для начала, как обычно, заново определим ложь, конъюнкцию и дизъюнкцию *)
(* Наши определения будут немного отличаться от предыдущих *)

Definition False : Prop := forall P:Prop, P.

Definition not : Prop -> Prop := fun A:Prop => A -> False.

Notation "~' x" := (not x) (at level 75, right associativity).

(* Конъюнкция *)
Definition and : Prop->Prop->Prop := fun A B:Prop => forall P:Prop, (A -> B -> P) -> P.

Notation "A /_\ B" := (and A B) (at level 80).

(* Аксиома A → B → A /\ B *)
Theorem andI : forall (A B : Prop), A -> B -> A /_\ B.
Proof.
    exact (fun A B a b P H => H a b).
    (* Также можно доказать так:
    intros A B a b.
    unfold and.
    intros P H.
    exact (H a b).
    *)
Qed.

(* Дизъюнция *)
Definition or : Prop->Prop->Prop := fun (A B : Prop) => forall P:Prop, (A -> P) -> (B -> P) -> P.

Notation "A \_/ B" := (or A B) (at level 85).

(* Аксиома A → A \/ B *)
Theorem orIL : forall (A B : Prop), A -> A \_/ B.
Proof.
    exact (fun A B a P H1 H2 => H1 a).
Qed.

(* Аксиома B → A \/ B *)
Theorem orIR : forall (A B : Prop), B -> A \_/ B.
Proof.
    exact (fun A B b P H1 H2 => H2 b).
Qed.

(* Эквивалентность через конъюнкцию *)
Definition iff : Prop->Prop->Prop := fun (A B:Prop) => (A -> B) /_\ (B -> A).

Notation "A <=> B" := (iff A B) (at level 95).


(* Теперь начнем развлекаться со множествами *)

(* Для начала определим множество *)
Parameter set : Type.

(* Равенство двух множеств *)
(* Любое суждение, верное для одного множества, верно и для другого *)
Definition eq : set->set->Prop := fun (x y : set) => forall Q:set -> Prop, Q x -> Q y.

Notation "x == y" := (eq x y) (at level 70).
Notation "x /= y" := (~' x == y) (at level 70).

(* Докажем рефлексивность такого равенства *)
Theorem eqI : forall x:set, x == x.
Proof.
    exact (fun x q H => H).
Qed.

(* И симметричность *)
Theorem eq_sym : forall x y:set, x == y -> y == x.
Proof.
    (* CW *)
    exact (fun x y H => H (fun y => eq y x) (eqI x)).
Qed.

(* Определим квантор существования для set *)
Definition ex : (set->Prop)->Prop := fun P:set->Prop => forall Q:Prop, (forall x, P x -> Q) -> Q.

Notation "'exists' x , p" := (ex (fun x => p))
  (at level 200, x ident).

(* P x -> \exists x P x *)
Theorem exI : forall P:set->Prop, forall x:set, P x -> exists x, P x.
Proof.
    exact (fun P x H1 Q H2 => H2 x H1).
Qed.

(* Такой же квантор существования, только для функций вида set -> set *)
Definition ex_f : ((set->set)->Prop)->Prop := fun P:(set->set)->Prop => forall Q:Prop, (forall x, P x -> Q) -> Q.

Notation "'existsf' x , p" := (ex_f (fun x => p))
  (at level 200, x ident).

Theorem exI_f : forall P:(set->set)->Prop, forall F:set->set, P F -> existsf F, P F.
Proof.
    (* CW *)
    exact (fun P F H1 Q H2 => H2 F H1).
Qed.

(* Квантор единственного существования *)
Definition exu : (set->Prop)->Prop := fun P:set->Prop => (exists x, P x) /_\ (forall x y:set, P x -> P y -> x == y).

Notation "'exists!' x , p" := (exu (fun x => p))
  (at level 200, x ident).

Theorem exuI : forall P:set->Prop, (exists x, P x) -> (forall x y:set, P x -> P y -> x == y) -> exists! x, P x.
Proof.
    (* CW *)
    intros P.
    exact (andI (ex P) (forall x y:set, P x -> P y -> x == y)).
Qed.

(* Оператор описания множества *)
(* Пригодится позже в доказательствах, пока можно пропустить *)
Parameter Descr : ((set->Prop)->set).

Axiom DescrR : forall P:set->Prop, (exists! x, P x) -> P (Descr P).


(* Определим базовые отношения, свойства и операции над множествами *)

(* In - отношение "x принадлежит множеству y" *)

Parameter In : set->set->Prop.

Notation "x ':e' y" := (In x y) (at level 70).
Notation "x '/:e' y" := (~' (In x y)) (at level 70).

(* Subq - отношение "A вложено в B" *)

Definition Subq : set->set->Prop :=
fun X Y => forall x:set, x :e X -> x :e Y.

Notation "X 'c=' Y" := (Subq X Y) (at level 70).
Notation "X '/c=' Y" := (~' (Subq X Y)) (at level 70).

Lemma Subq_ref : forall X:set, X c= X.
    intros X x H1. exact H1.
Qed.

Lemma Subq_tra : forall X Y Z:set, X c= Y -> Y c= Z -> X c= Z.
    (* CW *)
    intros X Y Z H1 H2 x H3. apply H2. apply H1. exact H3.
Qed.

(* Равенство множеств - это вложенность множеств друг в друга *)

Axiom set_ext : forall X Y:set, X c= Y -> Y c= X -> X == Y.

(* Равенство в другую сторону *)

Theorem set_ext_inv : forall X Y:set, X == Y -> (X c= Y /_\ Y c= X).
Proof.
    (* HW *)
    admit.
Qed.

(* Индукция по множеству *)

Axiom In_ind : forall P:set->Prop, (forall X:set, (forall x, x :e X -> P x) -> P X) -> forall X:set, P X.

Parameter Empty : set.

Axiom EmptyAx : ~' exists x, x :e Empty.

Lemma EmptyE : forall x:set, x /:e Empty.
    (* CW *)
    exact (fun x H => EmptyAx (exI (fun x => x :e Empty) x H)).
Qed.

(* Union(X) - операция объединения всех подмножеств X *)
(* То есть Union(X) = {x | \exists Y: x \in Y, Y \in X} *)

Parameter Union : set->set.

Axiom UnionEq : forall X:set, forall x:set, x :e Union X <=> exists Y, x :e Y /_\ Y :e X.

Lemma A_and_B_A : forall A B:Prop, A /_\ B -> A.
Proof.
    unfold and.
    intros.
    pose (t := H A).
    intuition.
Qed.

Lemma A_and_B_B : forall A B:Prop, A /_\ B -> B.
Proof.
    unfold and.
    intros.
    pose (t := H B).
    intuition.
Qed.

Lemma UnionE :
forall X x:set, x :e (Union X) -> exists Y, x :e Y /_\ Y :e X.
Proof.
    (* CW *)
    exact (fun X x : set =>
    UnionEq X x (x :e Union X -> exists Y, x :e Y /_\ Y :e X)
      (fun (H1 : x :e Union X -> exists Y, x :e Y /_\ Y :e X)
         (_ : (exists Y, x :e Y /_\ Y :e X) -> x :e Union X) => H1)).
Qed.

Lemma UnionI :
forall X x Y:set, x :e Y -> Y :e X -> x :e (Union X).
Proof.
    (* CW *)
    exact (fun (X x Y : set) (H1 : x :e Y) (H2 : Y :e X) =>
    UnionEq X x (x :e Union X)
      (fun (_ : x :e Union X -> exists Y, x :e Y /_\ Y :e X)
         (H4 : (exists Y, x :e Y /_\ Y :e X) -> x :e Union X) =>
       H4
         (exI (fun Y0 : set => x :e Y0 /_\ Y0 :e X) Y
            (andI (x :e Y) (Y :e X) H1 H2)))).
Qed.

(* Power(X) - множество всех подмножеств X *)

Parameter Power : set->set.

Axiom PowerEq : forall X Y:set, Y :e Power X <=> Y c= X.

Lemma PowerE : forall X Y:set, Y :e Power X -> Y c= X.
Proof.
    intros.
    pose (t := PowerEq X Y).
    unfold iff in t.
    pose (tt := A_and_B_A _ _ t).
    exact (tt H).
Qed.

Lemma PowerI : forall X Y:set, Y c= X -> Y :e (Power X).
    intros.
    pose (t := PowerEq X Y).
    unfold iff in t.
    pose (tt := A_and_B_B _ _ t).
    exact (tt H).
Qed.

Lemma In_Power : forall X:set, X :e Power X.
Proof.
    (* CW *)
    intros X. apply PowerI. apply Subq_ref.
Qed.

(* Sep(X, P) = {x | x :e X, P x} *)

Parameter Sep : set -> (set -> Prop) -> set.

Notation "{ x :i X | P }" := (Sep X (fun x:set => P)).

Axiom SepEq : forall X:set, forall P:set -> Prop, forall x, x :e {z :i X | P z} <=> x :e X /_\ P x.

Lemma SepI : forall X:set, forall P:set -> Prop, forall x:set,
 x :e X -> P x -> x :e {z :i X|P z}.
Proof.
    (* CW *)
    exact (fun (X : set) (P : set -> Prop) (x : set) (H1 : x :e X) (H2 : P x) =>
    SepEq X P x (x :e Sep X P)
      (fun (_ : x :e Sep X P -> x :e X /_\ P x)
         (H3 : x :e X /_\ P x -> x :e Sep X P) => H3 (andI (x :e X) (P x) H1 H2))).
Qed.

Lemma SepE : forall X:set, forall P:set -> Prop, forall x:set,
 x :e {z :i X|P z} -> x :e X /_\ P x.
Proof.
    (* CW *)
    intros X P x H1. apply (SepEq X P x). exact (fun H2 _ => H2 H1).
Qed.

Lemma SepE1 : forall X:set, forall P:set -> Prop, forall x:set,
 x :e {z :i X|P z} -> x :e X.
Proof.
    (* CW *)
    exact (fun (X : set) (P : set -> Prop) (x : set) (H1 : x :e Sep X P) =>
    SepEq X P x (x :e X)
      (fun (H2 : x :e Sep X P -> x :e X /_\ P x)
         (_ : x :e X /_\ P x -> x :e Sep X P) =>
       H2 H1 (x :e X) (fun (H3 : x :e X) (_ : P x) => H3))).
Qed.

Lemma SepE2 : forall X:set, forall P:set -> Prop, forall x:set,
 x :e {z :i X|P z} -> P x.
Proof.
    (* CW *)
    exact (fun (X : set) (P : set -> Prop) (x : set) (H1 : x :e Sep X P) =>
    SepEq X P x (P x)
      (fun (H2 : x :e Sep X P -> x :e X /_\ P x)
         (_ : x :e X /_\ P x -> x :e Sep X P) =>
       H2 H1 (P x) (fun (_ : x :e X) (H3 : P x) => H3))).
Qed.

(* Repl(X, F) = {F x | x :e X} *)

Parameter Repl : set->(set->set)->set.

Notation "{ F | x :i X }" := (Repl X (fun x:set => F)).

Axiom ReplEq :
forall X:set, forall F:set->set, forall y:set, y :e {F z|z :i X} <=> exists x, x :e X /_\ y == F x.

Lemma ReplE :
forall X:set, forall F:set->set, forall y:set, y :e {F z|z :i X} -> exists x, x :e X /_\ y == F x.
Proof.
    (* HW *)
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
Proof.
    (* HW *)
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

(* Прикольные леммки для разных операций над пустыми множествами *)
(* Пригодятся позже, когда определим ординалы *)

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

(* Неупорядоченная пара *)

Definition TSet : set := {X :i Power (Power Empty) | Empty :e X \_/ Empty /:e X}.
Definition UPair : set->set->set :=
 fun y z:set =>
 {Descr (fun w:set => forall p:set->Prop, (Empty /:e X -> p y) -> (Empty :e X  -> p z) -> p w)|X :i TSet}.

Notation "{ x , y }" := (UPair x y).

Lemma UPairE :
forall x y z:set, x :e {y,z} -> x == y \_/ x == z.
Proof.
    (* HW *)
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
Proof.
    (* HW *)
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
Proof.
    (* HW *)
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
Proof.
    (* CW *)
    intros x y z. apply andI. apply UPairE. intros H1. apply H1.
    intros H2. apply H2. apply UPairI1.
    intros H2. apply H2. apply UPairI2.
Qed.

(* sing(Y) = {Y, Y} *)

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

(* binunion(X, Y) = Union({X, Y}) *)

Definition binunion : set -> set -> set := fun X Y => Union {X,Y}.

Notation "X :u: Y" := (binunion X Y) (at level 40).

Lemma binunionI1 : forall X Y z, z :e X -> z :e X :u: Y.
    (* CW *)
    exact (fun (X Y z : set) (H1 : z :e X) => UnionI (UPair X Y) z X H1 (UPairI1 X Y)).
Qed.

Lemma binunionI2 : forall X Y z, z :e Y -> z :e X :u: Y.
    (* CW *)
    exact (fun (X Y z : set) (H1 : z :e Y) => UnionI (UPair X Y) z Y H1 (UPairI2 X Y)).
Qed.

Lemma binunionE : forall X Y z, z :e X :u: Y -> z :e X \_/ z :e Y.
    (* HW *)
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
    (* CW *)
    intros X Y z. apply andI. apply binunionE. intros H1. apply H1. apply binunionI1. apply binunionI2.
Qed.

(* TODO : setminus, famunion, ordinals, more and more fun to follow *)

End Basics.

Export Basics.
