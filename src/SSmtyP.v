Add LoadPath "src".
Require Import Maps.
Require Import Context.

Import Context.Context.
Require Import Coq.Lists.List.
Require Import SSmty.

Import SSmty.SSmty.


Module SSmtyP.
(* Structual Typing *)

(*
Fixpoint rcd_cons_ty (rcd : list (id * ty)) (retty : ty) : ty :=
    match rcd with
    | nil => retty
    | (_, h)::t => TFun h (rcd_cons_ty t retty)
    end. 
*)

Fixpoint rcd_field_ty (rcd: list (id * ty)) (field : id) : option ty :=
    match rcd with
    | nil => None
    | (i, ret)::t  => if (eq_id_dec i field) 
                        then Some ret 
                        else rcd_field_ty t field
    end.



Inductive has_type : Context ty -> tm -> ty -> Prop :=
| ht_none : 
    forall ctx,
        has_type ctx tnone TNone
| ht_rcd :
    forall ctx i t0 t1 T T',
        has_type t0 T ->
        has_type t1 T' ->
        has_type ctx (trcons i t0 t1) (TRcons i T T')
| ht_if : 
    forall ctx crit tb fb T,
    has_type ctx crit TBool ->
    has_type ctx tb T ->
    has_type ctx fb T ->
    has_type ctx (tif crit tb fb) T
| ht_var: forall ctx T i,
    byContext ctx i = T ->
    has_type ctx (tvar i) T
| ht_zero : forall ctx,
    has_type ctx tzero TNat
| ht_suc : forall ctx t,
    has_type ctx t TNat ->
    has_type ctx (tsuc t) TNat
| ht_dec : forall ctx t,
    has_type ctx t TNat ->
    has_type ctx (tdec t) TNat
| ht_ngt : forall ctx t0 t1,
    has_type ctx t0 TNat ->
    has_type ctx t1 TNat ->
    has_type ctx (ngt t0 t1) TBool
| ht_nlt : forall ctx t0 t1,
    has_type ctx t0 TNat ->
    has_type ctx t1 TNat ->
    has_type ctx (nlt t0 t1) TBool
| ht_neq : forall ctx t0 t1,
    has_type ctx t0 TNat ->
    has_type ctx t1 TNat ->
    has_type ctx (neq t0 t1) TBool
| ht_neq : forall ctx t0 t1,
    has_type ctx t0 TNat ->
    has_type ctx t1 TNat ->
    has_type ctx (neq t0 t1) TBool
| ht_chr : forall ctx n,
    has_type ctx (tchr n) TChr
| ht_ceq : forall ctx t0 t1,
    has_type ctx t0 TChr ->
    has_type ctx t1 TChr ->
    has_type ctx (ceq t0 t1) TBool
| ht_fun : forall ctx i T body TO,
    has_type (update i T ctx) body TO ->
    has_type ctx (tfun i T body) (TFun T TO)
| ht_app : forall ctx t0 t1 T0 T1,
    has_type ctx t0 (TFun T0 T1) ->
    has_type ctx t1 T0 ->
    has_type ctx (tapp t0 t1) T1
| ht_let : forall ctx i T bind body T',
    has_type (update i T ctx) bind T ->
    has_type (update i T ctx) body T' ->
    has_type ctx (tlet i T bind body) T'
| ht_true : forall ctx,
    has_type ctx ttrue TBool
| ht_false : forall ctx,
    has_type ctx tfalse TBool
| ht_beq : forall ctx t0 t1,
    has_type ctx t0 TBool ->
    has_type ctx t1 TBool ->
    has_type ctx (tbeq t0 t1) TBool
| ht_left : forall ctx t0 TL TR,
    has_type ctx t0 TL ->
    has_type ctx (tleft t0 TR) (TSum TL TR)
| ht_right : forall ctx t0 TL TR,
    has_type ctx t0 TR ->
    has_type ctx (tright TL t0) (TSum TL TR)
| ht_case : forall ctx crit tl tr TL TR TO,
    has_type ctx crit (TSum TL TR) ->
    has_type ctx tl (TFun TL TO) ->
    has_type ctx tr (TFun TR TO) ->
    has_type ctx (tcase crit tl tr) TO
| ht_field : forall ctx suty i,
    rcd_field_ty rcd i = Some T ->
    has_type (ht_field (TRcd tid suty rcd) i) (TFun (TRcd tid suty rcd) T)
| ht_seq : forall ctx t0 t1 T0 T1,
    has_type t0 T0 ->
    has_type t1 T1 ->
    has_type (tseq t0 t1) T1.


End SSmtyP.