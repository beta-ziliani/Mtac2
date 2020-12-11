(** * Unification strategies *)

(** Most of Mtac2's unification strategies come from the
    #<a href="https://github.com/Unicoq/Unicoq">Unicoq
    library</a>#. *)

Inductive Unification : Set :=
| UniCoq : Unification
| UniMatch : Unification
| UniMatchNoRed : Unification
| UniEvarconv : Unification.

(**
  - [UniCoq] is the default convertibility unification algorithm in
    Unicoq: the two terms are reduced if needed to.
  - [UniMatch] is like UniCoq, but it does not reduce the term on the
    left, in order to force the one on the right to _match_ it as
    is.
  - [UniMatchNoRed] also avoids reducing the term on the right.
  - [UniEvarconv] calls Coq's own unification algorithm (the one from
    tactics like [refine] and Ssreflect's, not the one for tactics
    like [apply]).
*)
