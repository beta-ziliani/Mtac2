From Mtac2 Require Import Base Datatypes List MTele MTeleMatch MTeleMatchDef MFixDef Sorts.
Require Import Strings.String.
Import Sorts.
Import M.notations.
Import Mtac2.List.ListNotations.
Import ProdNotations.

Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.
Unset Universe Minimization ToSet.

Local Inductive msigT {A} (P : A -> Type) : Type := | mexistT x : P x -> msigT P.
Local Notation "'{$'  x .. y  &  P }" := (msigT (fun x => .. (msigT (fun y => P)) .. )) (x binder, y binder).
Local Definition mprojT1 {A} {P} : @msigT A P -> A := fun '(mexistT _ x _) => x.
Local Definition mprojT2 {A} {P} : forall s : @msigT A P, P (mprojT1 s) := fun '(mexistT _ _ p) => p.
Local Inductive TTele : Type :=
| ttbase (X : Type) : TTele
| tttele {X} : (X -> TTele) -> TTele.
Fixpoint TTele_ty (M : Type -> Type) t :=
  match t with
  | ttbase X => M X
  | tttele F => forall x, TTele_ty M (F x)
  end.

Local Fixpoint TTele_bind {X} {t} : (X -> TTele_ty M t) -> (TTele_ty M.t t) :=
  match t with
  | ttbase X => M.bind (M.evar _)
  | tttele F => fun f (t : _) => @TTele_bind X (F t) (fun x : X => f x t)
  end
.

Local Fixpoint func_of (l : mlist Prop) :=
  match l with
  | mnil => True
  | mcons T l => prod T (func_of l)
end.

Local Notation "x -*> y" := (prod (func_of x) y) (only parsing, at level 91).

Local Notation tty := (TTele_ty (fun T => msigT (fun l => M (l -*> T)))).

Local Fixpoint TTele_bind' {X : Prop} (x : X) {t} : (TTele_ty (fun T => msigT (fun l => X -> M (l -*> T))) t) -> (tty t) :=
  match t with
  | ttbase B => fun '(mexistT _ l f) => mexistT _ (X :m: l) (
                  H <- M.evar X;
                  ''(goals, R) <- f H;
                  M.ret ((H,goals), R))
  | tttele F => fun f t =>
                  TTele_bind' x (f t)
  end
.

Definition lift_lemma : forall (A : Prop), A ->
      M (msigT tty) :=
  let m := (mTele (fun (A : Prop) => (mTele (fun (a:A) => mBase)))) in
  @mfix' m
         (fun A (a:A) => msigT tty)
        (fun rec (A : Prop) =>
           let m (A : Prop) := mTele (fun a:A => mBase) in
           mtmmatch'
             _ m (fun A a => msigT tty) A
             [m:
              (mtptele (fun B:Prop => mtptele (fun (C:Prop) => (mtpbase ( m:=fun A:Prop => A -> M _)) _ (
              fun (f : B -> C) =>
                n <- M.fresh_binder_name A;
                M.nu n mNone (fun b : B =>
                               ''(mexistT _ t X) <- rec C (f b);
                               match t as t return tty t -> M (_) with
                               | tttele _ =>
                                 fun _ =>
                                   M.failwith "Lemma to be lifted has dependent quantifiers after non-dependent ones. This is not supported."
                               | ttbase P => fun f =>
                                               let '(mexistT _ l f) := f in
                                               f' <- M.abs_fun b f;
                                               f' <- M.coerce f';
                                               let T' := reduce (RedWhd RedAll)
                                                                (TTele_bind' b (t:=ttbase _) (mexistT _ l f')) in
                                          M.ret (mexistT tty (ttbase P) T')
                               end X
                     )
              ) UniMatchNoRed)))%mtpattern
             |
             (mtptele (fun B:Type => mtptele (fun (C:B -> Prop) => (mtpbase ( m:=fun A:Prop => A -> M _)) _ (
              fun (f : forall b:B, C b) =>
                n <- M.fresh_binder_name A;
                M.nu n mNone (fun b : B =>
                               ''(mexistT _ t X) <- rec _ (f b);
                               t' <- M.abs_fun b t;
                               X <- M.coerce X;
                               X' <- M.abs_fun (P:=fun b => tty (t' b)) b X;
                               M.ret (mexistT tty (tttele t') (fun x => X' x))
                     )
              ) UniMatchNoRed)))%mtpattern
              |
              (mtpbase ( m:=fun A:Prop => A -> M _) A
                       (fun a:A =>
                          M.ret (mexistT tty (ttbase A) (mexistT _ mnil (M.ret (I,a))))
                       )
                       UniCoq
              )%mtpattern
             ]%with_mtpattern
        )
.


Local Fixpoint TTele_App {P1} {t} (P2 : forall T (H : P1 T), Type) : TTele_ty P1 t -> Type :=
  match t with
  | ttbase P => fun x => P2 _ x
  | tttele F => fun g => forall x, TTele_App P2 (g x)
  end.

Local Fixpoint TTele_app {P1} {t} P2 (f : forall T PT, P2 T PT) : forall tt, TTele_App (P1:=P1) (t:=t) P2 tt :=
match t with
| ttbase T => fun tt : P1 T => f _ _
| tttele F => fun (tt : forall t, TTele_ty P1 (F t)) t => @TTele_app _ (F t) _ f (tt t)
end.

Definition do_def n {A:Prop} (a:A) :=
  ''(mexistT _ t f) <- lift_lemma A (a);
  (* let f := reduce (RedStrong [rl: RedBeta; RedZeta; RedFix; RedMatch; RedDeltaOnly [rl: Dyn (@M.type_of); Dyn (@TTele_ty)] ]) (f) in *)
  let x := reduce (RedStrong [rl: RedFix; RedMatch; RedBeta; RedDeltaOnly [rl: Dyn (@TTele_app)]]) (TTele_app (fun T PT => let '(mexistT _ l _) := PT in M (l -*> T))
                                                (fun T PT => let '(mexistT _ l X) := PT in
                                                             X
                                                ) f) in
  let T := reduce (RedStrong [rl: RedBeta; RedZeta; RedFix; RedMatch;
                           RedDeltaOnly [rl: Dyn (@M.type_of); Dyn (@TTele_ty); Dyn (@TTele_App); Dyn (@TTele_app); Dyn (@func_of)] ]) (M.type_of x) in
               @M.declare dok_Definition n false T x;; M.ret tt.




Module TT.

Require Import Tactics.

(** We use a synonim to prod to emulate typed goals. The idea
    is that at the left we have the hypotheses, and at the right
    the goal type. A goal H1, ..., Hn |- G is then written
    (H1 * ... * Hn) =m> G

    A lemma lifted to this type will produce an element of type G given
    promises (evars) for H1, ..., Hn.
*)

Definition myprod := prod.
Arguments myprod _%type _%type.

Notation "T1 '|m-' G" := (myprod T1 G)
  (at level 98, no associativity,
   format "T1  |m-  G") : type_scope.


Import M. Import M.notations.

(** composes on the left of the arrow *)
Definition compl {A} {B} (f: M (A |m- B)) (g : M A) : M B :=
  ''(a, b) <- f;
  a' <- g;
  mif unify a a' UniCoq then
    ret b
  else failwith "nope".

(** composes a product *)
Definition compi {A} {B} (g : M A) (h : M B) : M (A * B) :=
  g >>= fun xg=> h >>= fun xh => ret (xg, xh).

(** A typed assumption tactic *)
Set Print Universes.
Open Scope pattern_scope.
Polymorphic Definition find(*@{i j k k1 a1 a2 a3 a4 a5 a6 a7 a8}*) {A:Type(*@{i}*)} :=
  mfix1 f (l : mlist(*@{j}*) Hyp(*@{k}*)) : M A :=
    mmatch'(*@{a1 a2 a3 a4 a5 a6 a7 a8}*) l (mcons(*@{j}*)
      ([? x d (l': mlist(*@{j}*) Hyp(*@{k}*))] (mcons(*@{j}*) (@ahyp(*@{k}*) A x d) l') => M.ret x)
      (mcons(*@{j}*) ([? (ah:Hyp(*@{k}*)) (l': mlist(*@{j}*) Hyp(*@{k}*))] (mcons(*@{j}*) ah l') => f l')
      (mcons(*@{j}*) ([? l': mlist(*@{j}*) Hyp(*@{k}*)] l' => M.raise(*@{k1}*) exception)
       mnil(*@{j}*))))
    .

Polymorphic Definition assumption(*@{i j k k1 a1 a2 a3 a4 a5 a6 a7 a8}*) {A:Type(*@{i}*)} : M.t A :=
  l <- hyps;
  @find(*@{i j k k1 a1 a2 a3 a4 a5 a6 a7 a8}*) A l.

(** Solves goal A provided tactic t *)
Definition by' {A} (t: tactic) : M A :=
  e <- evar A;
  l <- t (Goal SType e);
  l' <- T.filter_goals l;
  match l' with mnil => ret e | _ => failwith "couldn't solve" end.

Definition use {A} (t: tactic) : M A :=
  e <- evar A;
  t (Goal SType e);;
  ret e.


Definition is_prod T :=
  mmatch T with
  | [? A B] (A * B)%type => ret true
  | _ => ret false
  end.

Definition dest_pair {T} (x:T) : M (dyn * dyn) :=
  mmatch Dyn x with
  | [? A B a b] @Dyn (A*B) (a, b) => ret (Dyn a, Dyn b)
  end.

(** Given an element with type of the form (A1 * ... * An),
    it generates a goal for each unsolved variable in the pair. *)
Program Definition to_goals : forall {A}, A -> M (mlist (unit *m goal)) :=
  mfix2 to_goals (A: Type) (a: A) : M _ :=
  mif is_evar a then ret [m: (m: tt, Goal SType a)]
  else
    mif is_prod A then
      ''(d1, d2) <- dest_pair a;
      dcase d1 as x in
      dcase d2 as y in
      t1s <- to_goals _ x;
      t2s <- to_goals _ y;
      ret (t1s +m+ t2s)
    else
      ret [m:].

(** From a typed tactic with type A |m- B, it generates an untyped one *)
Definition to_tactic {A B} (f: M (A |m- B)) : tactic := fun g=>
  gT <- goal_type g;
  mif unify gT B UniCoq then
    ''(a, b) <- f;
    al <- to_goals a;
    ls <- T.filter_goals al;
    T.exact b g;;
    ret ls
  else
    failwith "nope".

Definition pass := evar.
Arguments pass {_}.

Import Strings.Ascii.
Local Open Scope string.

Definition doTT {A:Prop} (x:A) :=
  s <- pretty_print x;
  let s :=
      match String.get 0 s with
      | Some "@"%char => String.substring 1 (String.length s -1) s
      | _ => s
      end  ++ "T" in
  print s;;
  do_def s x.

Definition TT A := M (A *m mlist goal).

Definition use' {A} (t : tactic) : TT A :=
  (e <- M.evar A;
  gs <- t (Goal Sorts.Sorts.SType e);
  let gs := mmap (fun '(m: _, g) => g) gs in
  M.ret (m: e, gs))%MC.

Definition lift {A} (t : M A) : TT A :=
  t >>= (fun a => M.ret (m: a,  mnil)).

Coercion lift : M.t >-> TT.
Definition fappgl {A B C} (comb : C -> C -> M C) (f : M ((A -> B) *m C)) (x : M (A *m C)) : M (B *m C) :=
  (f >>=
     (fun '(m: b, cb) =>
        ''(m: a, ca) <- x;
        c <- comb ca cb;
        M.ret (m: b a, c)
     )
  )%MC.

Definition Mappend {A} (xs ys : mlist A) :=
  let zs := dreduce (mapp) (mapp xs ys) in
  M.ret zs.


Definition apply {A} : (A *m mlist goal) -> tactic :=
  (fun '(m: a, gs) g =>
    T.exact a g;;
            match g with
            | Goal _ g =>
              M.ret (mmap (fun g => (m: tt, g)) gs)
            | _ => M.raise NotAGoal
            end
  )%MC.

Module notations.
Notation "[t: x | .. | y ]" := (TT.compi x (.. (TT.compi y (M.ret I)) ..)).
Notation "'doTT' t" := (ltac:(mrun (doTT t))) (at level 0).
Infix "<**>" := (fappgl Mappend) (at level 61, left associativity) : M_scope.
End notations.


End TT.
