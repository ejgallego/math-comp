Reserved Notation "x -> y" (at level 99, right associativity, y at level 200).
Reserved Notation "x <-> y" (at level 95, no associativity).
Reserved Notation "x /\ y" (at level 80, right associativity).
Reserved Notation "x \/ y" (at level 85, right associativity).
Reserved Notation "~ x" (at level 75, right associativity).

(** Notations for equality and inequalities *)

Reserved Notation "x = y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x = y" (at level 70, no associativity).
Reserved Notation "x = y = z"
(at level 70, no associativity, y at next level).

Reserved Notation "x <> y  :>  T"
(at level 70, y at next level, no associativity).
Reserved Notation "x <> y" (at level 70, no associativity).

Reserved Notation "x <= y" (at level 70, no associativity).
Reserved Notation "x < y" (at level 70, no associativity).
Reserved Notation "x >= y" (at level 70, no associativity).
Reserved Notation "x > y" (at level 70, no associativity).

Reserved Notation "x <= y <= z" (at level 70, y at next level).
Reserved Notation "x <= y < z" (at level 70, y at next level).
Reserved Notation "x < y < z" (at level 70, y at next level).
Reserved Notation "x < y <= z" (at level 70, y at next level).

(** Arithmetical notations (also used for type constructors) *)

Reserved Notation "x + y" (at level 50, left associativity).
Reserved Notation "x - y" (at level 50, left associativity).
Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "x / y" (at level 40, left associativity).
Reserved Notation "- x" (at level 35, right associativity).
Reserved Notation "/ x" (at level 35, right associativity).
Reserved Notation "x ^ y" (at level 30, right associativity).

(** Notations for booleans *)

Reserved Notation "x || y" (at level 50, left associativity).
Reserved Notation "x && y" (at level 40, left associativity).

(** Notations for pairs *)

Reserved Notation "( x , y , .. , z )" (at level 0).

(** Notation "{ x }" is reserved and has a special status as component
    of other notations such as "{ A } + { B }" and "A + { B }" (which
    are at the same level as "x + y");
    "{ x }" is at level 0 to factor with "{ x : A | P }" *)

Reserved Notation "{ x }" (at level 0, x at level 99).

(** Notations for sigma-types or subsets *)

Reserved Notation "{ x  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x  |  P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A  |  P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  |  P  & Q }" (at level 0, x at level 99).

Reserved Notation "{ x : A  & P }" (at level 0, x at level 99).
Reserved Notation "{ x : A  & P  & Q }" (at level 0, x at level 99).

Delimit Scope type_scope with type.
Delimit Scope core_scope with core.

Open Scope core_scope.
Open Scope type_scope.

Declare ML Module "coretactics".
Declare ML Module "extratactics".

Set Implicit Arguments.

Notation "A -> B" := (forall (_ : A), B) : type_scope.

Inductive True : Prop :=
  I : True.

(** [False] is the always false proposition *)
Inductive False : Prop :=.

(** [not A], written [~A], is the negation of [A] *)
Definition not (A:Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.

Hint Unfold not: core.

Inductive and (A B:Prop) : Prop :=
  conj : A -> B -> A /\ B

where "A /\ B" := (and A B) : type_scope.

Section Conjunction.

  Variables A B : Prop.

  Theorem proj1 : A /\ B -> A.
  Proof.
    destruct 1; trivial.
  Qed.

  Theorem proj2 : A /\ B -> B.
  Proof.
    destruct 1; trivial.
  Qed.

End Conjunction.

(** [or A B], written [A \/ B], is the disjunction of [A] and [B] *)

Inductive or (A B:Prop) : Prop :=
  | or_introl : A -> A \/ B
  | or_intror : B -> A \/ B

where "A \/ B" := (or A B) : type_scope.

Arguments or_introl [A B] _, [A] B _.
Arguments or_intror [A B] _, A [B] _.

(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

Definition iff (A B:Prop) := (A -> B) /\ (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

Hint Unfold iff: extcore.

Definition IF_then_else (P Q R:Prop) := P /\ Q \/ ~ P /\ R.

Notation "'IF' c1 'then' c2 'else' c3" := (IF_then_else c1 c2 c3)
  (at level 200, right associativity) : type_scope.

Inductive ex (A:Type) (P:A -> Prop) : Prop :=
  ex_intro : forall x:A, P x -> ex (A:=A) P.

Inductive ex2 (A:Type) (P Q:A -> Prop) : Prop :=
  ex_intro2 : forall x:A, P x -> Q x -> ex2 (A:=A) P Q.

(* Rule order is important to give printing priority to fully typed exists *)
Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "'exists2' x , p & q" := (ex2 (fun x => p) (fun x => q))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : t , p & q" := (ex2 (fun x:t => p) (fun x:t => q))
  (at level 200, x ident, t at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' x  :  t ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.

Inductive eq (A:Type) (x:A) : A -> Prop :=
    eq_refl : x = x :>A

where "x = y :> A" := (@eq A x y) : type_scope.

Notation "x = y" := (x = y :>_) : type_scope.
Notation "x <> y  :> T" := (~ x = y :>T) : type_scope.
Notation "x <> y" := (x <> y :>_) : type_scope.

Arguments eq {A} x _.
Arguments eq_refl {A x} , [A] x.

Arguments eq_ind [A] x P _ y _.
Arguments eq_rec [A] x P _ y _.
Arguments eq_rect [A] x P _ y _.

Hint Resolve I conj or_introl or_intror : core. 
Hint Resolve eq_refl: core. 
Hint Resolve ex_intro ex_intro2: core.

Section equality.

Variables A B : Type.
Variable  f : A -> B.
Variables x y z : A.

    Theorem eq_sym : x = y -> y = x.
    Proof.
      destruct 1; trivial.
    Defined.

    Theorem eq_trans : x = y -> y = z -> x = z.
    Proof.
      destruct 2; trivial.
    Defined.

Theorem f_equal : x = y -> f x = f y.
Proof. destruct 1; trivial. Defined.

    Theorem not_eq_sym : x <> y -> y <> x.
    Proof.
      red; intros h1 h2; apply h1; destruct h2; trivial.
    Qed.

End equality.

  Definition eq_ind_r :
    forall (A:Type) (x:A) (P:A -> Prop), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0. elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_rec_r :
    forall (A:Type) (x:A) (P:A -> Set), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.

  Definition eq_rect_r :
    forall (A:Type) (x:A) (P:A -> Type), P x -> forall y:A, y = x -> P y.
    intros A x P H y H0; elim eq_sym with (1 := H0); assumption.
  Defined.

Theorem f_equal2 :
  forall (A1 A2 B:Type) (f:A1 -> A2 -> B) (x1 y1:A1)
    (x2 y2:A2), x1 = y1 -> x2 = y2 -> f x1 x2 = f y1 y2.
Proof.
  destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal3 :
  forall (A1 A2 A3 B:Type) (f:A1 -> A2 -> A3 -> B) (x1 y1:A1)
    (x2 y2:A2) (x3 y3:A3),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> f x1 x2 x3 = f y1 y2 y3.
Proof.
  destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal4 :
  forall (A1 A2 A3 A4 B:Type) (f:A1 -> A2 -> A3 -> A4 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4),
    x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Theorem f_equal5 :
  forall (A1 A2 A3 A4 A5 B:Type) (f:A1 -> A2 -> A3 -> A4 -> A5 -> B)
    (x1 y1:A1) (x2 y2:A2) (x3 y3:A3) (x4 y4:A4) (x5 y5:A5),
    x1 = y1 ->
    x2 = y2 ->
    x3 = y3 -> x4 = y4 -> x5 = y5 -> f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof.
  destruct 1; destruct 1; destruct 1; destruct 1; destruct 1; reflexivity.
Qed.

Notation sym_eq := eq_sym (compat "8.3").
Notation trans_eq := eq_trans (compat "8.3").
Notation sym_not_eq := not_eq_sym (compat "8.3").

Notation refl_equal := eq_refl (compat "8.3").
Notation sym_equal := eq_sym (compat "8.3").
Notation trans_equal := eq_trans (compat "8.3").
Notation sym_not_equal := not_eq_sym (compat "8.3").

Hint Immediate eq_sym not_eq_sym: core.

Inductive unit : Set :=
    tt : unit.

Inductive bool : Set :=
  | true : bool
  | false : bool.

Add Printing If bool.

Delimit Scope bool_scope with bool.

Bind Scope bool_scope with bool.

Definition is_true b := b = true.

Definition andb (b1 b2:bool) : bool := if b1 then b2 else false.

Definition orb (b1 b2:bool) : bool := if b1 then true else b2.

Definition implb (b1 b2:bool) : bool := if b1 then b2 else true.

Definition xorb (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => false
    | true, false => true
    | false, true => true
    | false, false => false
  end.

Definition negb (b:bool) := if b then false else true.

Infix "||" := orb : bool_scope.
Infix "&&" := andb : bool_scope.

Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.

Arguments None {A}.

Inductive sum (A B:Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Arguments pair {A B} _ _.

Section projections.
  Context {A : Type} {B : Type}.

  Definition fst (p:A * B) := match p with
				| (x, y) => x
                              end.
  Definition snd (p:A * B) := match p with
				| (x, y) => y
                              end.
End projections.

Hint Resolve pair inl inr: core.

Lemma surjective_pairing :
  forall (A B:Type) (p:A * B), p = pair (fst p) (snd p).
Proof.
  destruct p; reflexivity.
Qed.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.

Inductive sig (A:Type) (P:A -> Prop) : Type :=
    exist : forall x:A, P x -> sig P.

Inductive sig2 (A:Type) (P Q:A -> Prop) : Type :=
    exist2 : forall x:A, P x -> Q x -> sig2 P Q.

Inductive sigT (A:Type) (P:A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.

Inductive sigT2 (A:Type) (P Q:A -> Type) : Type :=
    existT2 : forall x:A, P x -> Q x -> sigT2 P Q.

(* Notations *)

Arguments sig (A P)%type.
Arguments sig2 (A P Q)%type.
Arguments sigT (A P)%type.
Arguments sigT2 (A P Q)%type.

Notation "{ x  |  P }" := (sig (fun x => P)) : type_scope.
Notation "{ x  |  P  & Q }" := (sig2 (fun x => P) (fun x => Q)) : type_scope.
Notation "{ x : A  |  P }" := (sig (A:=A) (fun x => P)) : type_scope.
Notation "{ x : A  |  P  & Q }" := (sig2 (A:=A) (fun x => P) (fun x => Q)) :
  type_scope.
Notation "{ x : A  & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
Notation "{ x : A  & P  & Q }" := (sigT2 (A:=A) (fun x => P) (fun x => Q)) :
  type_scope.

Add Printing Let sig.
Add Printing Let sig2.
Add Printing Let sigT.
Add Printing Let sigT2.
Section Subset_projections.

  Variable A : Type.
  Variable P : A -> Prop.

  Definition proj1_sig (e:sig P) := match e with
                                    | exist _ a b => a
                                    end.

  Definition proj2_sig (e:sig P) :=
    match e return P (proj1_sig e) with
    | exist _ a b => b
    end.

End Subset_projections.


(** [sig2] of a predicate can be projected to a [sig].

    This allows [proj1_sig] and [proj2_sig] to be usable with [sig2].

    The [let] statements occur in the body of the [exist] so that
    [proj1_sig] of a coerced [X : sig2 P Q] will unify with [let (a,
    _, _) := X in a] *)

Definition sig_of_sig2 (A : Type) (P Q : A -> Prop) (X : sig2 P Q) : sig P
  := exist P
           (let (a, _, _) := X in a)
           (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).

(** Projections of [sig2]

    An element [y] of a subset [{x:A | (P x) & (Q x)}] is the triple
    of an [a] of type [A], a of a proof [h] that [a] satisfies [P],
    and a proof [h'] that [a] satisfies [Q].  Then
    [(proj1_sig (sig_of_sig2 y))] is the witness [a],
    [(proj2_sig (sig_of_sig2 y))] is the proof of [(P a)], and 
    [(proj3_sig y)] is the proof of [(Q a)]. *)

Section Subset_projections2.

  Variable A : Type.
  Variables P Q : A -> Prop.

  Definition proj3_sig (e : sig2 P Q) :=
    let (a, b, c) return Q (proj1_sig (sig_of_sig2 e)) := e in c.

End Subset_projections2.


(** Projections of [sigT]

    An element [x] of a sigma-type [{y:A & P y}] is a dependent pair
    made of an [a] of type [A] and an [h] of type [P a].  Then,
    [(projT1 x)] is the first projection and [(projT2 x)] is the
    second projection, the type of which depends on the [projT1]. *)



Section Projections.

  Variable A : Type.
  Variable P : A -> Type.

  Definition projT1 (x:sigT P) : A := match x with
                                      | existT _ a _ => a
                                      end.

  Definition projT2 (x:sigT P) : P (projT1 x) :=
    match x return P (projT1 x) with
    | existT _ _ h => h
    end.

End Projections.

(** [sigT2] of a predicate can be projected to a [sigT].

    This allows [projT1] and [projT2] to be usable with [sigT2].

    The [let] statements occur in the body of the [existT] so that
    [projT1] of a coerced [X : sigT2 P Q] will unify with [let (a,
    _, _) := X in a] *)

Definition sigT_of_sigT2 (A : Type) (P Q : A -> Type) (X : sigT2 P Q) : sigT P
  := existT P
            (let (a, _, _) := X in a)
            (let (x, p, _) as s return (P (let (a, _, _) := s in a)) := X in p).

(** Projections of [sigT2]

    An element [x] of a sigma-type [{y:A & P y & Q y}] is a dependent
    pair made of an [a] of type [A], an [h] of type [P a], and an [h']
    of type [Q a].  Then, [(projT1 (sigT_of_sigT2 x))] is the first
    projection, [(projT2 (sigT_of_sigT2 x))] is the second projection,
    and [(projT3 x)] is the third projection, the types of which
    depends on the [projT1]. *)

Section Projections2.

  Variable A : Type.
  Variables P Q : A -> Type.

  Definition projT3 (e : sigT2 P Q) :=
    let (a, b, c) return Q (projT1 (sigT_of_sigT2 e)) := e in c.

End Projections2.

(** [sigT] of a predicate is equivalent to [sig] *)

Definition sig_of_sigT (A : Type) (P : A -> Prop) (X : sigT P) : sig P
  := exist P (projT1 X) (projT2 X).

Definition sigT_of_sig (A : Type) (P : A -> Prop) (X : sig P) : sigT P
  := existT P (proj1_sig X) (proj2_sig X).

(** [sigT2] of a predicate is equivalent to [sig2] *)

Definition sig2_of_sigT2 (A : Type) (P Q : A -> Prop) (X : sigT2 P Q) : sig2 P Q
  := exist2 P Q (projT1 (sigT_of_sigT2 X)) (projT2 (sigT_of_sigT2 X)) (projT3 X).

Definition sigT2_of_sig2 (A : Type) (P Q : A -> Prop) (X : sig2 P Q) : sigT2 P Q
  := existT2 P Q (proj1_sig (sig_of_sig2 X)) (proj2_sig (sig_of_sig2 X)) (proj3_sig X).

(** [sumbool] is a boolean type equipped with the justification of
    their value *)

Inductive sumbool (A B:Prop) : Set :=
  | left : A -> {A} + {B}
  | right : B -> {A} + {B}
 where "{ A } + { B }" := (sumbool A B) : type_scope.

Add Printing If sumbool.

Arguments left {A B} _, [A] B _.
Arguments right {A B} _ , A [B] _.

(** [sumor] is an option type equipped with the justification of why
    it may not be a regular value *)

Inductive sumor (A:Type) (B:Prop) : Type :=
  | inleft : A -> A + {B}
  | inright : B -> A + {B}
 where "A + { B }" := (sumor A B) : type_scope.

Add Printing If sumor.

Arguments inleft {A B} _ , [A] B _.
Arguments inright {A B} _ , A [B] _.

Notation sigS := sigT (compat "8.2").
Notation existS := existT (compat "8.2").
Notation sigS_rect := sigT_rect (compat "8.2").
Notation sigS_rec := sigT_rec (compat "8.2").
Notation sigS_ind := sigT_ind (compat "8.2").
Notation projS1 := projT1 (compat "8.2").
Notation projS2 := projT2 (compat "8.2").

Notation sigS2 := sigT2 (compat "8.2").
Notation existS2 := existT2 (compat "8.2").
Notation sigS2_rect := sigT2_rect (compat "8.2").
Notation sigS2_rec := sigT2_rec (compat "8.2").
Notation sigS2_ind := sigT2_ind (compat "8.2").

Inductive identity (A:Type) (a:A) : A -> Type :=
  identity_refl : identity a a.
Hint Resolve identity_refl: core.

Arguments identity_ind [A] a P f y i.
Arguments identity_rec [A] a P f y i.
Arguments identity_rect [A] a P f y i.

(** Identity type *)

Definition ID := forall A:Type, A -> A.
Definition id : ID := fun A x => x.

Definition IDProp := forall A:Prop, A -> A.
Definition idProp : IDProp := fun A x => x.

Fixpoint add n m :=
  match n with
  | O => m
  | S p => S (p + m)
  end

where "n + m" := (add n m) : nat_scope.

Notation plus := add (compat "8.4").
Infix "+" := add : nat_scope.

Fixpoint sub n m :=
  match n, m with
  | S k, S l => k - l
  | _, _ => n
  end

where "n - m" := (sub n m) : nat_scope.

Notation minus := sub (compat "8.4").
Infix "-" := sub : nat_scope.

Fixpoint mul n m :=
  match n with
  | O => O
  | S p => m + p * m
  end

where "n * m" := (mul n m) : nat_scope.

Notation mult := mul (compat "8.4").
Infix "*" := mul : nat_scope.

Definition succ := S.

Definition pred n :=
  match n with
    | O => n
    | S u => u
  end.

Open Scope nat_scope.

Inductive le (n:nat) : nat -> Prop :=
  | le_n : n <= n
  | le_S : forall m:nat, n <= m -> n <= S m

where "n <= m" := (le n m) : nat_scope.

Hint Constructors le: core.

Definition lt (n m:nat) := S n <= m.
Hint Unfold lt: core.

Infix "<" := lt : nat_scope.

Definition ge (n m:nat) := m <= n.
Hint Unfold ge: core.

Infix ">=" := ge : nat_scope.

Definition gt (n m:nat) := m < n.
Hint Unfold gt: core.

Infix ">" := gt : nat_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : nat_scope.
Notation "x < y < z" := (x < y /\ y < z) : nat_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : nat_scope.

Definition eq_S := f_equal S.
Definition f_equal_nat := f_equal (A:=nat).

Hint Resolve eq_S: v62.
Hint Resolve f_equal_nat: core.

(** The predecessor function *)

Definition f_equal_pred := f_equal pred.
Hint Resolve f_equal_pred: v62.

Theorem pred_Sn : forall n:nat, n = pred (S n).
Proof.
  simpl; reflexivity.
Qed.

(** Injectivity of successor *)


Definition eq_add_S n m (H: S n = S m): n = m := f_equal pred H.
Hint Immediate eq_add_S: core.

Theorem O_S : forall n:nat, O <> S n.
Proof.
  discriminate.
Qed.

Theorem not_eq_S : forall n m:nat, n <> m -> S n <> S m.
Proof.
  red; auto.
Qed.
Hint Resolve not_eq_S: core.

Hint Resolve O_S: core.

Theorem n_Sn : forall n:nat, n <> S n.
Proof.
  induction n; auto.
Qed.
Hint Resolve n_Sn: core.

Definition f_equal2_plus := f_equal2 plus.
Hint Resolve f_equal2_plus: v62.
Definition f_equal2_nat := f_equal2 (A1:=nat) (A2:=nat). 
Hint Resolve f_equal2_nat: core.

Lemma plus_n_O : forall n:nat, n = n + O.
Proof.
  induction n; simpl; auto.
Qed.
Hint Resolve plus_n_O: core.

Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
Proof.
  intros n m; induction n; simpl; auto.
Qed.
Hint Resolve plus_n_Sm: core.

Lemma mult_n_O : forall n:nat, O = n * O.
Proof.
  induction n; simpl; auto.
Qed.
Hint Resolve mult_n_O: core.

Lemma mult_n_Sm : forall n m:nat, n * m + n = n * S m.
Proof.
  intros; induction n as [| p H]; simpl; auto.
  destruct H; rewrite <- plus_n_Sm; apply eq_S.
  pattern m at 1 3; elim m; simpl; auto.
Qed.
Hint Resolve mult_n_Sm: core.

Definition prod_uncurry (A B C:Type) (f:prod A B -> C)
  (x:A) (y:B) : C := f (pair x y).

Definition prod_curry (A B C:Type) (f:A -> B -> C)
  (p:prod A B) : C := match p with
                       | pair x y => f x y
                       end.

Declare ML Module "eauto".
Declare ML Module "tauto".
Declare ML Module "nat_syntax_plugin".

(* Declare ML Module "g_class". *)
(* Declare ML Module "g_eqdecide". *)
(* Declare ML Module "g_rewrite". *)
(* Declare ML Module "extraction_plugin". *)
(* Declare ML Module "decl_mode_plugin". *)
(* Declare ML Module "cc_plugin". *)
(* Declare ML Module "ground_plugin". *)
(* Declare ML Module "recdef_plugin". *)

