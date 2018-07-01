Add LoadPath "src".
Require Import Maps.
Require Import Context.

Import Context.Context.
Require Import Coq.Lists.List.
Require Import LibTactics.

Module SmallCore.

Definition  tyId := id.
Definition  tyBase := id.
Definition  fieldId := id.


Inductive ty : Set :=
    | TFun : ty -> ty -> ty
    | TSum : ty -> ty -> ty
    | TVar : tyId -> ty
    | TNone : ty
    (* 
        TVar represents primitive type variable
    *)
    | TRcons : fieldId -> ty -> ty -> ty.

Hint Constructors ty.

Inductive Extty : Set :=
    | ETVar : tyId  -> Extty
    | ETFun : tyId -> Extty -> Extty (* No higher order Function*)
    | ETSum : Extty -> Extty -> Extty. 

Parameter Ext : Set.
Parameter ExttyInterpreter : Extty -> Ext.
Parameter Exteq : Ext -> Ext -> Prop.
Notation "x '==e' y" := (Exteq x y) (at level 40).


Inductive only_rcd : ty -> Prop :=
    | orcdBase : only_rcd TNone
    | orcdRcd : forall i T T',
        only_rcd T' ->
        only_rcd (TRcons i T T').

Hint Constructors only_rcd.

Inductive wf_ty : ty -> Prop :=
    | wfFun : forall i o, wf_ty i -> wf_ty o -> wf_ty (TFun i o)
    | wfSum : forall l r, wf_ty l -> wf_ty r -> wf_ty (TSum l r)
    | wfNone :  wf_ty TNone
    | wfRcd : forall i T T',
        wf_ty T ->
        wf_ty T' ->
        only_rcd T' ->
        wf_ty (TRcons i T T')
    | wfVar : forall i,
        wf_ty (TVar i).

    Hint Constructors wf_ty.


Axiom wf_ty_indistinct:
    forall T (t1 t2: wf_ty T),
        t1 = t2.

Axiom orcd_indistinct:
    forall T (t1 t2: only_rcd T),
        t1 = t2.

    
Theorem only_rcd_dec:
    forall T,
        only_rcd T + {only_rcd T -> False}.
    
    intros.
    induction T; subst; eauto;
    try (
        left; eauto; fail
    );
    try (right; intro h0; inversion h0; eauto; fail).
    destruct IHT1; destruct IHT2; subst; eauto;
    try(
        right; intro h0; inversion h0; subst; eauto; fail
    ).
Qed.

Theorem wf_ty_dec :
    forall T,
        {wf_ty T} + {~wf_ty T}.
    
    intros T.
    induction T; subst; eauto;
    
        repeat (match goal with
                | h0 : {_} + {_} |- _ => destruct h0; subst; eauto
                end);
    try (
        try(
            left; eauto; fail
        );
        try(
            right; intro h0; inversion h0; subst; eauto; fail
        );
        fail
    ).
    destruct (only_rcd_dec T2);
    try(
        left; eauto; fail
    );
    try(
        right; intro h0; inversion h0; subst; eauto; fail
    ).
Qed.



Inductive tm : Set :=
    | tvar : id -> tm
    | tnone : tm
(* 
    | tbox : tm -> tyId -> tm
    | tunbox : tm -> tm
    (* Primitivize and unprimitivize, key to Recursive type *)
     *)


    | tfun : id -> forall (T: ty),  wf_ty T -> tm -> tm 

    | tapp : tm -> tm -> tm
    | tlet : id -> forall (T: ty),  wf_ty T -> tm -> tm -> tm
    | tfixApp : id -> forall (T: ty),  wf_ty T -> tm -> tm
    | tleft : tm -> forall (T: ty),  wf_ty T -> tm 
    | tright: forall (T : ty),  wf_ty T -> tm -> tm
    | tcase : tm -> tm -> tm -> tm 
    | trcons : id -> tm -> tm -> tm
    | text : forall (T : Extty), 
                forall (t : Ext),
                 t ==e ExttyInterpreter T -> tm
        (* extension *)
        (*
            tcase (\ x -> x) (\ y -> y)
        *)
        (*
            type information is 
            lexical scoped
        *)
    (* | tletrcd : id -> tyId -> ty -> list (id* ty) -> tm -> tm
        (*
            letRcd (contructorA TypeA ParentType ((a, Int) (b, Int))
            in ... 
                 TypeA <: ParentType
            then constructorA :: Int -> Int -> TypeA
                 TypeA.a :: TypeA -> Int

            letRcd (i J (Nat Nat))
            then i :: Int -> Int -> J
        *) *)
    | tfield : forall (T: ty), only_rcd T ->  wf_ty T -> id -> tm.

Fixpoint rcd_field_ty' (rcd: ty) (field : id) : option ty :=
    match rcd with
    | TRcons i head tail => if (eq_id_dec i field) then Some head else rcd_field_ty' tail field
    | _ => None
    end.

Definition rcd_field_ty (rcd: ty) (h : only_rcd rcd) (h' : wf_ty rcd) (field : id) : option ty :=
    rcd_field_ty' rcd field.    

Lemma rcd_field_ty'_wf_is_wf:
    forall T i T',
        wf_ty T ->
        rcd_field_ty' T i = Some T' ->
        wf_ty T'.
    intros T.
    induction T; intros; subst; eauto; cbn in *; eauto; try discriminate.
    destruct (eq_id_dec f i); subst; eauto.
    inversion H; subst ;eauto. inversion H0; subst; eauto.
    eapply IHT2; eauto.
    inversion H; subst; eauto.
Qed.
    
Lemma rcd_field_ty'_wf_is_onlyrcd:
    forall T i T' (h: wf_ty T),
        rcd_field_ty' T i = Some T' ->
        only_rcd T.
    intros T.
    induction T; intros; subst; eauto; cbn in *; eauto; try discriminate.
    eapply orcdRcd. inversion h; subst; eauto.
Qed.

Definition subty_prop_weak (x y : ty) := 
    forall T fid,
        rcd_field_ty' y fid = Some T ->
        exists T', rcd_field_ty' x fid = Some T'.


Inductive subty  : ty -> ty -> Prop :=
    | subFun : forall x x' y y',
                subty x' x ->
                subty y y' ->
                subty (TFun x y) (TFun x' y')
    | subSum : forall x x' y y',
                subty x x' ->
                subty y y' ->
                subty (TSum x y) (TSum x' y')
    | subRcdd : forall i p1 p2 q1 q2,
                wf_ty q1 ->
                only_rcd q1 ->
                wf_ty q2 ->
                only_rcd q2 ->
                subty p1 p2 ->
                subty q1 q2 ->
                subty (TRcons i p1 q1) (TRcons i p2 q2)
    | subRcdw : forall i p q1 q2,
                wf_ty q1 ->
                only_rcd q1 ->
                wf_ty q2 ->
                only_rcd q2 ->
                subty q1 q2 ->
                wf_ty p ->
                subty (TRcons i p q1) q2
    | subRefl : forall t,
                wf_ty t ->
                subty t t
    | subTrans : forall t0 t1 t2,
                subty t0 t1 ->
                subty t1 t2 ->
                subty t0 t2.
    
Hint Constructors subty.

Theorem subty_rcd:
    forall a b,
        only_rcd b ->
        subty a b ->
        only_rcd a.
    intros a b h0 h.
    generalize dependent h0.
    induction h; intros; subst; eauto.
    inversion h0.
    inversion h0.
Qed.

Theorem subty_rcd1:
    forall T1 T2,
        only_rcd T1 ->
        subty T1 T2 ->
        only_rcd T2.

    intros T1 T2 h0 h.
    generalize dependent h0.
    induction h; intros; subst; eauto.
    inversion h0.
    inversion h0.
Qed.

Theorem subty_defined_well_weak :
    forall x y,
        subty x y ->
        subty_prop_weak x y.

    intros x y h. unfold subty_prop_weak.
    induction h; intros; subst; eauto;
    simpl in *;

    try(destruct (eq_id_dec i fid); subst; eauto; fail).
    destruct (IHh2 _ _ H); eauto.
Qed.

Inductive record_field_unique : ty -> Prop :=
    | rfu_none : record_field_unique TNone
    | rfu_rcons : forall i t T,
        (only_rcd t -> record_field_unique t) -> 
        record_field_unique T ->
        rcd_field_ty' T i = None ->
        record_field_unique (TRcons i t T).



Hint Constructors record_field_unique.

Notation "'RFU'" := record_field_unique.

Notation "'ORFU' x" := (only_rcd x -> RFU x) (at level 10).


Ltac destructALL :=
repeat (
    match goal with
    | h0: _ \/ _ |- _ => destruct h0
    | h0: _ /\ _ |- _ => destruct h0
    | h0: exists _, _ |- _ => destruct h0
    | h0: {_ | _} |- _ => destruct h0
    | h0: {_} + {_} |- _ => destruct h0
    | h0: _ + {_} |- _ => destruct h0
    | h0: _ + _ |- _ => destruct h0
    end
).

Theorem RFU_dec :
    forall T,
        {RFU T} + {~RFU T}.

    intros T.
    induction T; subst; eauto;
    try (
        right; intros CCC; inversion CCC; fail
    );
    try (
        destructALL;
        try (left; eauto; fail);
        try (right; intros CCC; inversion CCC; try contradiction; try discriminate); fail
    ).
    (* case TRcons*)
    destruct IHT1; destruct IHT2;
    destruct (rcd_field_ty' T2 f) eqn:hh;
    subst; eauto;
    try (
        right; intros CCC; inversion CCC; subst; try contradiction; 
        try rewrite hh in *; try contradiction; try discriminate; fail
    ).
    destruct (only_rcd_dec T1); subst; eauto.
    right; intro. inversion H; subst; eauto.
    left. eapply rfu_rcons; eauto. intro. try contradiction.
    
Qed.

Theorem subty_prop_weak' :
    forall x y,
        subty x y ->
        forall i,
            rcd_field_ty' x i = None ->
            rcd_field_ty' y i = None.

    intros x y h.
    induction h; intros; subst; eauto;
    simpl in *; eauto.
    
    (* case SubRcdw *)
    destruct (eq_id_dec i i0); subst; eauto.
    inversion H3.

    (* case SubRcdd *)
    destruct (eq_id_dec i i0); subst; eauto.
    inversion H4.
Qed.

Theorem RFU_trans:
    forall x y,
        subty x y ->
        RFU x ->
        RFU y.

    intros x y h.
    induction h; intros; subst; eauto;
    try (match goal with
        | hh : RFU _ |- _ => inversion hh; subst; eauto ; try discriminate; fail
        end; fail
    );
    try (
        match goal with
        | hh: only_rcd _ |- _ => inversion hh; subst; eauto; try contradiction;try discriminate; fail
        end
    ).

    inversion H3; subst; eauto.
    
    eapply rfu_rcons; eauto. intro.
    eapply IHh1. eapply H7. eapply subty_rcd; eauto.
    eapply subty_prop_weak'; eauto.


Qed.


Theorem subty_defined_well_strong':
    forall x y,
        subty x y ->
        only_rcd x ->
        RFU x ->
        forall T fid,
            rcd_field_ty' y fid = Some T ->
            exists T', rcd_field_ty' x fid = Some T' /\ subty T' T.

    intros x y h h0 h1.
    assert (RFU y); try eapply RFU_trans; eauto.
    generalize dependent h0; generalize dependent H. generalize dependent h1.
    induction h;intros; subst; eauto;
    try (simpl in *; try discriminate; try contradiction; fail).
    (* case subRcdw *)
    simpl in *. inversion H3; inversion h0; subst; eauto.
    destruct (eq_id_dec i fid); subst; eauto; try discriminate.
    inversion H4; subst; eauto.

    (* case subRcdd *)
    simpl in *. inversion h1; subst; eauto.
    destruct (eq_id_dec i fid); subst; eauto; try discriminate.
    inversion h0; subst; eauto.
    destruct (IHh H10 H4 H7 _ _ H5). 
    rewrite H11 in *; try contradiction; try discriminate.
    destruct H6; try discriminate.

    (* case subRefl *)
    exists T; split; eauto.
    eapply subRefl. eapply rcd_field_ty'_wf_is_wf; eauto.
    (* case subTrans*)
    assert (RFU t1); try eapply RFU_trans; eauto.
    poses' (subty_rcd1 _ _ h3 h1).
    destruct (IHh2 H1 H H2 _ _ H0).
    destruct H3.
    destruct (IHh1 h0 H1 h3 _ _ H3); eauto.
    destruct H5.
    eauto.
Qed.

Theorem RFU_is_rcd:
    forall T,
        RFU T ->
        only_rcd T.
    
    intros T h.
    induction h; subst; eauto.
Qed.

Theorem subty_wf:
    forall x y,
        subty x y ->
        wf_ty x /\ wf_ty y.
    
intros x y h;
induction h; destructALL; subst; split; eauto.
Qed.

Theorem subty_defined_well_strong:
    forall x y,
        subty x y ->
        RFU x ->
        forall T fid,
            rcd_field_ty' y fid = Some T ->
            exists T', rcd_field_ty' x fid = Some T' /\ subty T' T.

    intros.
    assert (only_rcd x). eapply RFU_is_rcd; eauto.
    eapply subty_defined_well_strong'; eauto.
Qed.
        
Theorem subty_defined_well_strong_ORFU:
    forall x y,
        subty x y ->
        ORFU x ->
        forall T fid,
            rcd_field_ty' y fid = Some T ->
            exists T', rcd_field_ty' x fid = Some T' /\ subty T' T.

    intros.
    destruct (only_rcd_dec x). eapply subty_defined_well_strong'; eauto.
    cut (only_rcd x); eauto; try contradiction.
    poses' (subty_defined_well_weak _ _ H _ _ H1); destructALL.
    eapply rcd_field_ty'_wf_is_onlyrcd.
    cut (wf_ty x /\ wf_ty y); try tauto.
    eapply subty_wf; eauto.
    exact H2.
Qed.

Theorem ORFU_trans:
    forall x y,
        subty x y ->
        ORFU x ->
        ORFU y.

    intros x y h h0.
    intro. eapply RFU_trans; eauto.
    eapply h0. eapply subty_rcd; eauto.
Qed.

End SmallCore.

