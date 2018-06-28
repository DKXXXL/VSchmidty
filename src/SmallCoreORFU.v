Add LoadPath "src".
Require Import Maps.
Require Import Context.

Import Context.Context.
Require Import Coq.Lists.List.
Require Import LibTactics.
Require Import SmallCore.
Require Import Coq.ZArith.ZArith.

Import SmallCore.SmallCore.

Import Context.Context.

Module SmallCoreORFU.

Inductive orfu : ty -> Prop :=
    | orfu_tvar : forall i, orfu (TVar i)
    | orfu_tnone : orfu TNone
    | orfu_trcons : 
        forall i t T,
            orfu t ->
            orfu T ->
            rcd_field_ty' T i = None ->
            orfu (TRcons i t T)
    | orfu_tfun :  
        forall i o,
            orfu i ->
            orfu o ->
            orfu (TFun i o)
    | orfu_tsum :
        forall x y,
            orfu x ->
            orfu y ->
            orfu (TSum x y).

Theorem orfu_ORFU:
    forall T,
        orfu T ->
        ORFU T.

    intros T h.
    induction T; intros; subst; eauto;
    try (
        match goal with
        | h : only_rcd (_ _) |- _ => inversion h; subst; eauto
        end
    );
    try (match goal with
        | h : orfu _ |- _ => inversion h; subst; eauto
        end
    ).
Qed.

Theorem subty_orfu_trans:
    forall x y,
        subty x y ->
        orfu x ->
        orfu y.

    intros x y h.
    induction h; intros; subst; eauto;
    try (
        match goal with
        | h : orfu _ |- _ => inversion h; subst; eauto
        end
    ).
    Abort.

End SmallCoreORFU.