Add LoadPath "src".
Require Import Maps.
Require Import Context.

Import Context.Context.
Require Import Coq.Lists.List.
Require Import Smty.

Import Smty.Smty.


Module SmtyP.

Unset Strict Implicit.

Inductive has_type (tctx : Context Rcd) : Context ty -> tm -> ty -> Prop :=
| ht_none : 
    forall vctx,
        has_type tctx vctx tnone TNone
| ht_if : 
    forall vctx crit tb fb T,
    has_type tctx vctx crit TBool ->
    has_type tctx vctx tb T ->
    has_type tctx vctx fb T ->
    has_type tctx vctx (tif crit tb fb) T
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
    has_type


