From MetaCoq Require Import MetaCoq.
Require Import Bool.Bool.

Example hyp_well_formed : True.
MProof.
  \nu x := I,
   l <- hypotheses;
   oeq <- munify l [ahyp x (Some I)] UniCoq;
   match oeq with
   | None => raise exception
   | _ => ret I
   end.
Qed.

Example env_well_formed : True.
MProof.
  \nu x := I,
   oeq <- munify x I UniCoq;
   match oeq with
   | None => raise exception
   | _ => ret I
   end.
Qed.

Example fail_returning_var : True.
MProof.
  mtry
    (\nu x := I, ret x);; raise exception
  with VarAppearsInValue => ret I
  end.
Qed.
