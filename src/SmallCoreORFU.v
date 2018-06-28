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
Hint Constructors orfu.

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

(* Theorem subty_orfu_trans:
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
    Abort. *)

Theorem subty_defined_well_strong_orfu:
    forall x y,
        subty x y ->
        orfu x ->
        forall T fid,
            rcd_field_ty' y fid = Some T ->
            exists T', rcd_field_ty' x fid = Some T' /\ subty T' T.

    intros.
    assert (ORFU x).
    eapply orfu_ORFU; eauto.
    eapply subty_defined_well_strong_ORFU; eauto.
Qed.

Lemma not_only_rcd_orfu:
    forall T,
        ~only_rcd T ->
        orfu T.
    intros T;
    induction T;intros; subst; eauto; try discriminate; try contradiction.
Abort.

Theorem RFU_orfu:
    forall T,
        RFU T ->
        orfu T.
    intros T;
    induction T; intros; subst; eauto;
    try (
        match goal with
        | h : RFU _ |- _ => inversion h; subst; eauto
        end
    ).
    eapply orfu_trcons; eauto.
Abort.


End SmallCoreORFU.