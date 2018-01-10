Add LoadPath "src".
Require Import Maps.
Require Import Context.

Import Context.Context.
Require Import Coq.Lists.List.
Require Import Smty.

Import Smty.Smty.


Module SmtyP.



Inductive has_type {tctx : Context (type := Rcd)} : Context ty -> tm -> ty -> Prop :=
| ht_none : 
    forall ctx,
        has_type ctx tnone TNone
| ht_if : 
    forall vctx crit tb fb T,
    has_type vctx crit TBool ->
    has_type vctx tb T ->
    has_type vctx fb T ->
    has_type vctx (tif crit tb fb) T
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


