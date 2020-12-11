(** * Shallow reification of inductive types and pattern matchings *)
(* begin hide *)
From Coq Require Import BinNums.
From Mtac2 Require Import List.
From Mtac2.intf Require Import Dyn.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.
Set Polymorphic Inductive Cumulativity.
(* end hide *)

(** An inductive type: *)
Record Ind_dyn :=
  mkInd_dyn {
      ind_dyn_ind : dyn;
      ind_dyn_nparams : N;
      ind_dyn_nindices : N;
      ind_dyn_constrs : mlist dyn
    }.
(**
  - [ind_dyn_ind]: The unapplied inductive type itself as a [dyn].
  - [ind_dyn_nparams]: The number of parameters.
  - [ind_dyn_nindices]: The number of indices.
  - [ind_dyn_constrs]: the inductive type's constructors as [dyn]s. *)

(** A pattern-matching: *)
Record Case :=
    mkCase {
        case_ind : Type;
        case_val : case_ind;
        case_return : dyn;
        case_branches : mlist dyn
        }.
(**
  - [case_ind]: The inductive type of the element being matched.
  - [case_val]: The element.
  - [case_return]: The function with the return type.
  - [case_branches]: The branches, as list of functions. *)
