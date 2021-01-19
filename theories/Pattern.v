(** * Generic pattern-matching *)

(* begin hide *)
From Mtac2 Require Import Logic List intf.Unification Sorts MTele Exceptions.
Import Sorts.S.
Import ListNotations.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

(** This file contains the infrastructure to construct pattern matches
    of various forms. The constructs `mmatch` and `match_goal` are
    different instances of what is shown in this file. *)

(** ** Introduction *)
(** There are two types of patterns, distinguished by its type:

  - [pattern] describes a pattern with _holes_ that are instantiated
    with meta-variables (_evars_). It includes the following
    notations, that we make concrete with examples:

    - In [ [? (A:Type) (f:A->Prop)] forall x:A, f x => t ] what comes
      after the [?] are the holes of the pattern. This pattern matches
      a term like [forall x:nat, x >= 0]. Since Mtac2 uses higher-order
      unification to perform the matching, [f] will be instantiated
      with [fun x:nat =>x >= 0].

    - In [ [¿ s] [? (A:Type) (f:A->s)] forall x:A, f x => t ] the
      pattern [p] is tested first with the [s] being [Propₛ], and if
      that fails, with [Typeₛ]. This pattern is useful for
      generalizing branches with [Prop] or [Type] sorts. [ [¿ s] ] can
      also be written [ [S? s] ].

    Patterns can be annotated with a [Unification] identifier, in
    order to pick the algorithm to perform unification. This
    identifier is part of the double-arrow:

    - [=n>] neither the scrutinee nor the pattern are reduced
      ([UniMatchNoRed]).

    - [=u>] the scrutinee and the pattern are reduced ([UniCoq]).

    - [=c>] the scrutinee and the pattern are reduced ([UniEvarconv]).

    - [=>] the scrutinee is reduced but the pattern isn't ([UniMatch]).

    Finally, sometimes it is useful to have a hypothesis proving that
    the scrutinee is definitionally equal to the pattern. This is
    written adding a [ [H] ] to the right side of the arrow. For
    instance, if the scrutinee is [scr], the pattern [ [? (A:Type)
    (f:A->Prop)] forall x:A, f x => [eqFA] t ] will have variable
    [eqFA] being a proof that [scr =m= forall x:A, f x]. Note that it uses
    the polymorphic equality type [meq].

  - [branch A B y] is a [pattern A B y] with extra layers for matching
    the shape of an object _without creating evars_. Evars are costly
    in terms of performance, and in many cases they can be
    avoided. These patterns help matching without paying that cost.

    - [ [# plus | x y =n> code] ] will match [plus n m], instantiating
      [x] with [n] and [y] with [m].

    - TODO: add the other patterns.
*)

(** ** Implementation *)

(** A [pattern A B y] describes a pattern matching element [y] and
    returning something of the form [B y]. It consists of the
    following constructors:

  - [pany t] matches always, and is note as [ _ => t ]. [t] is then the
    code to be run.

  - [pbase x f U] matches [x] with [y] according to the unification
    strategy [U].  If it succeeds, then it executes [f meq_refl].

  - [ptele f] allows introducing a variable in the pattern, which is
    then replaced with a meta-variable, like [x] in [ [? x] S x =>
    ... ].

  - [psort f] introduces a sort.  *)

(* TODO I don't understand this comment:
   B will be instantiated with the M monad or the gtactic monad. In principle,
   we could make it part of the B, but then higher order unification will fail. *)
Inductive pattern@{a} (A : Type@{a}) (B : A -> Prop) (y : A) : Prop :=
  | pany : B y -> pattern A B y
  | pbase : forall x : A, (y =m= x -> B x) -> Unification -> pattern A B y
  | ptele : forall {C:Type@{a}}, (forall x : C, pattern A B y) -> pattern A B y
  | psort : (Sort -> pattern A B y) -> pattern A B y.

Arguments pany {A B y} _.
Arguments pbase {A B y} _ _ _.
Arguments ptele {A B y C} _.
Arguments psort {A B y} _.

(**
 - [branch_pattern] is the base case, and it just contains a
   [pattern].

 - [branch_app_static] TODO

 - [branch_foallP f] checks the term is a [forall (x:X), Y x : Prop] and calls
   [f X Y] upon success.

 - [branch_foallT f] is equivalent to [branch_forallP] but for [Type]. *)
Inductive branch@{a elem_a x+} : forall {A : Type@{a}} {B : A -> Prop} {y : A}, Prop :=
| branch_pattern {A : Type@{a}} {B : A -> Prop} {y : A}: pattern A B y -> @branch A B y
| branch_app_static {A : Type@{a}} {B : A -> Prop} {y : A}:
    forall {m:MTele@{elem_a}} (uni : Unification) (C : selem_of (MTele_Const@{_ _} (s:=Typeₛ) A m)),
      MTele_sort@{elem_a _ _ a elem_a} (MTele_ConstMap (si := Typeₛ) Propₛ (fun a : A => B a) C) ->
      @branch A B y
| branch_forallP {B : Prop -> Prop} {y : Prop}:
    (forall (X : Type@{x}) (Y : X -> Prop), B (forall x : X, Y x)) ->
    @branch Prop B y
| branch_forallT {B : Type@{elem_a} -> Prop} {y : Type@{elem_a}}:
    (forall (X : Type@{elem_a}) (Y : X -> Type@{elem_a}), B (forall x : X, Y x)) ->
    @branch Type@{elem_a} B y.
Arguments branch _ _ _ : clear implicits.

(* | branch_app_dynamic {A} {B : forall A, A -> Type} {y}: *)
(*     (forall X (Y : X -> Type) (f : forall x, Y x) (x : X), M (B _ (f x))) -> *)
(*     @branch M _ B A y *)

Declare Scope pattern_scope.

Notation "[¿ s .. t ] ps" := (psort (fun s => .. (psort (fun t => ps)) ..))
  (at level 202, s binder, t binder, ps at next level, only parsing) : pattern_scope.
Notation "'[S?' s .. t ] ps" := (psort (fun s => .. (psort (fun t => ps)) ..))
  (at level 202, s binder, t binder, ps at next level) : pattern_scope.

Notation "[? x .. y ] ps" := (ptele (fun x => .. (ptele (fun y => ps)).. ))
  (at level 202, x binder, y binder, ps at next level) : pattern_scope.
Notation "p => b" := (pbase p%core (fun _ => b%core) UniMatch)
  (no associativity, at level 201) : pattern_scope.
Notation "p => [ H ] b" := (pbase p%core (fun H => b%core) UniMatch)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "p => [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatch)
  (no associativity, at level 201, H binder, G binder) : pattern_scope.
Notation "'_' => b " := (pany b%core)
  (at level 201, b at next level) : pattern_scope.

Notation "p '=n>' b" := (pbase p%core (fun _ => b%core) UniMatchNoRed)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=n>' [ H ] b" := (pbase p%core (fun H => b%core) UniMatchNoRed)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "p =n> [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatchNoRed)
  (no associativity, at level 201, H binder, G binder) : pattern_scope.

Notation "p '=u>' b" := (pbase p%core (fun _ => b%core) UniCoq)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=u>' [ H ] b" := (pbase p%core (fun H => b%core) UniCoq)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "p =u> [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniCoq)
  (no associativity, at level 201, H binder, G binder) : pattern_scope.

Notation "p '=c>' b" := (pbase p%core (fun _ => b%core) UniEvarconv)
  (no associativity, at level 201) : pattern_scope.
Notation "p '=c>' [ H ] b" := (pbase p%core (fun H => b%core) UniEvarconv)
  (no associativity, at level 201, H at next level) : pattern_scope.
Notation "p =c> [ H .. G ] b" := (pbase p%core (fun H => .. (fun G => b%core) .. ) UniEvarconv)
  (no associativity, at level 201, H binder, G binder) : pattern_scope.

Delimit Scope pattern_scope with pattern.

Declare Scope branch_scope.

Notation "[¿ s .. t ] ps" := (branch_pattern (psort (fun s => .. (psort (fun t => ps%pattern)) ..)))
  (at level 202, s binder, t binder, ps at next level, only parsing) : branch_scope.
Notation "'[S?' s .. t ] ps" := (branch_pattern (psort (fun s => .. (psort (fun t => ps%pattern)) ..)))
  (at level 202, s binder, t binder, ps at next level) : branch_scope.

Notation "[? x .. y ] ps" := (branch_pattern (ptele (fun x => .. (ptele (fun y => ps%pattern)).. )))
  (at level 202, x binder, y binder, ps at next level) : branch_scope.
Notation "p => b" := (branch_pattern (pbase p%core (fun _ => b%core) UniMatch))
  (no associativity, at level 201) : branch_scope.
Notation "p => [ H ] b" := (branch_pattern (pbase p%core (fun H => b%core) UniMatch))
  (no associativity, at level 201, H at next level) : branch_scope.
Notation "p => [ H .. G ] b" := (branch_pattern (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatch))
  (no associativity, at level 201, H binder, G binder) : branch_scope.
Notation "'_' => b " := (branch_pattern (pany b%core))
  (at level 201, b at next level) : branch_scope.

Notation "p '=n>' b" := (branch_pattern (pbase p%core (fun _ => b%core) UniMatchNoRed))
  (no associativity, at level 201) : branch_scope.
Notation "p '=n>' [ H ] b" := (branch_pattern (pbase p%core (fun H => b%core) UniMatchNoRed))
  (no associativity, at level 201, H at next level) : branch_scope.
Notation "p =n> [ H .. G ] b" := (branch_pattern (pbase p%core (fun H => .. (fun G => b%core) .. ) UniMatchNoRed))
  (no associativity, at level 201, H binder, G binder) : branch_scope.

Notation "p '=u>' b" := (branch_pattern (pbase p%core (fun _ => b%core) UniCoq))
  (no associativity, at level 201) : branch_scope.
Notation "p '=u>' [ H ] b" := (branch_pattern (pbase p%core (fun H => b%core) UniCoq))
  (no associativity, at level 201, H at next level) : branch_scope.
Notation "p =u> [ H .. G ] b" := (branch_pattern (pbase p%core (fun H => .. (fun G => b%core) .. ) UniCoq))
  (no associativity, at level 201, H binder, G binder) : branch_scope.

Notation "p '=c>' b" := (branch_pattern (pbase p%core (fun _ => b%core) UniEvarconv))
  (no associativity, at level 201) : branch_scope.
Notation "p '=c>' [ H ] b" := (branch_pattern (pbase p%core (fun H => b%core) UniEvarconv))
  (no associativity, at level 201, H at next level) : branch_scope.
Notation "p =c> [ H .. G ] b" := (branch_pattern (pbase p%core (fun H => .. (fun G => b%core) .. ) UniEvarconv))
  (no associativity, at level 201, H binder, G binder) : branch_scope.

Delimit Scope branch_scope with branch.

Declare Scope with_pattern_scope.

Notation "'with' | p1 | .. | pn 'end'" :=
  ((@mcons (branch _ _ _) p1%branch (.. (@mcons (branch _ _ _) pn%branch [m:]) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.
Notation "'with' p1 | .. | pn 'end'" :=
  ((@mcons (branch _ _ _) p1%branch (.. (@mcons (branch _ _ _) pn%branch [m:]) ..)))
  (at level 91, p1 at level 210, pn at level 210) : with_pattern_scope.

Delimit Scope with_pattern_scope with with_pattern.

(** Syntax for decomposition of applications with a known head symbol.

   The [=>] arrows are annotated with the reduction strategy used for the
   initial arguments that are part of the head symbol term [f]. The delimiter
   [|] separates the head symbol term from the arguments, which are binders that
   can be refered to in [b]
*)

Notation "'[#' ] f '|' x .. z '=n>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniMatchNoRed
     f
     (fun x => .. (fun z => b) ..)
  ) (at level 201, x binder, z binder) : branch_scope.

Notation "'[#' ] f '|' '=n>' b" :=
  (branch_app_static (m := mBase) UniMatchNoRed f b) (at level 201) : branch_scope.

Notation "'[#' ] f '|' x .. z '=m>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniMatch
     f
     (fun x => .. (fun z => b) ..)
  ) (at level 201, x binder, z binder) : branch_scope.

Notation "'[#' ] f '|' '=m>' b" :=
  (branch_app_static (m := mBase) UniMatch f b) (at level 201) : branch_scope.

Notation "'[#' ] f '|' x .. z '=u>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniCoq
     f
     (fun x => .. (fun z => b) ..)
  ) (at level 201, x binder, z binder) : branch_scope.

Notation "'[#' ] f '|' '=u>' b" :=
  (branch_app_static (m := mBase) UniCoq f b) (at level 201) : branch_scope.

Notation "'[#' ] f '|' x .. z '=c>' b" :=
  (branch_app_static
     (m := mTele (fun x => .. (mTele (fun z => mBase)) ..))
     UniEvarconv
     f
     (fun x => .. (fun z => b) ..)
  ) (at level 201, x binder, z binder) : branch_scope.

Notation "'[#' ] f '|' '=c>' b" :=
  (branch_app_static (m := mBase) UniEvarconv f b) (at level 201) : branch_scope.


(** Syntax for decomposition of [forall x : X, P x].

   We define two variants, one for [Prop] and for [Type].
   The initial tokens are [[!Prop]] and [[!Type]] and the remaining
   syntax tries to mirror an actual [forall].
 *)
Notation "'[!Prop' ] 'forall' '_' : X , P =n> b" :=
  (branch_forallP (fun X P => b))
    (at level 201) : branch_scope.
Notation "'[!Type' ] 'forall' '_' : X , P =n> b" :=
  (branch_forallT (fun X P => b))
    (at level 201) : branch_scope.

Structure Predicate :=
  PREDICATE {
    predicate_pred : Prop
  }.

Structure Matcher {A : Type} {y : A} :=
  MATCHER {
    matcher_pred: forall y, Predicate;
    matcher_ret: Prop;
    _ : forall (E: Exception) (ps : mlist (branch A (fun y => predicate_pred (matcher_pred y)) y)), matcher_ret
  }.
Arguments Matcher {_} _.
Arguments MATCHER {_} {_}.

Definition matcher_match {A y} (m : Matcher y) : forall (E: Exception) (ps : mlist (branch A (fun y => predicate_pred (matcher_pred m y)) y)), matcher_ret m :=
  ltac:(destruct m as [ ? ? x]; refine x).

Structure InDepMatcher :=
  INDEPMATCHER {
    idmatcher_return : Prop;
    _ : forall A y (E: Exception) (ps : mlist (branch A (fun _ => idmatcher_return) y)), idmatcher_return;
  }.

Definition idmatcher_match (m : InDepMatcher) : forall A y (E: Exception) (ps : mlist (branch A (fun _ => idmatcher_return m) y)), idmatcher_return m :=
  ltac:(destruct m as [ ? x]; refine x).

Definition idmatcher_match_invert (m : InDepMatcher) (A : Type) (y : A) (R : Prop) :
  R =m= idmatcher_return m ->
  forall (_ : Exception) (_ : mlist (branch A (fun _ => R) y)),
    (* R y =m= matcher_return y m -> *)
    R.
  intros ->. eauto using idmatcher_match. Defined.

Arguments idmatcher_match _ _ _ _ & _.

Definition matcher_match_invert (A : Type) (y : A) (m : Matcher y) (R : A -> Prop) :
  (matcher_ret m =m= R y) ->
  (fun y => predicate_pred (matcher_pred m y)) =m= R ->
  forall (_ : Exception) (_ : mlist (branch A R y)),
    (* R y =m= matcher_return y m -> *)
    R y.
  intros <- <-. eauto using matcher_match. Defined.

Arguments matcher_match_invert _ _ _ _ & _ _ _ _ .


Notation "'mmatch' x ls" :=
  (idmatcher_match _ _ x DoesNotMatch ls%with_pattern)
  (at level 200, ls at level 91).
Notation "'mmatch' x 'return' p ls" :=
  (idmatcher_match_invert _ _ x p meq_refl DoesNotMatch ls%with_pattern)
  (at level 200, ls at level 91).
Notation "'mmatch' x 'as' y 'return' p ls" :=
  (matcher_match_invert _ x _ (fun y => p%type) meq_refl meq_refl DoesNotMatch ls%with_pattern)
  (at level 200, ls at level 91).
Notation "'mmatch' x 'in' T 'as' y 'return' p ls" :=
  (matcher_match_invert T%type x _ (fun y => p%type) meq_refl meq_refl DoesNotMatch ls%with_pattern)
  (at level 200, ls at level 91).
