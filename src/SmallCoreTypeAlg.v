Add LoadPath "src".
Require Import Maps.
Require Import Context.

Import Context.Context.
Require Import Coq.Lists.List.
Require Import LibTactics.
Require Import SmallCore.
Require Import Coq.ZArith.ZArith.
Require Import SmallCorePropSubty.
Require Import SmallCoreStep.
Require Import SmallCoreORFU.
Require Import SmallCoreTyping.

Import SmallCore.SmallCore.
Import SmallCoreTyping.SmallCoreTyping.
Import SmallCoreORFU.SmallCoreORFU.
Import SmallCoreStep.SmallCoreStep.
Import SmallCorePropSubty.SmallCorePropSubty.
Import Context.Context.

Module SmallCoreTypeAlg.

Theorem has_type_dec:
    forall ctx t T,
        {has_type ctx t T} + {~has_type ctx t T}.

Abort.

Fixpoint check_type (ctx : Context (type := {x : ty | wf_ty x})) (t : tm) : option ty.
    refine
    (match t with
        | tvar i => _
        | tnone => Some TNone
        | tfun i T h body => match (check_type (update i (exist wf_ty T h) ctx) body) with
                                | None => None 
                                | Some o => _
                             end
        | tapp f x => _
        | tlet i T h bind body => _
        | tfixApp i T h self => _
        | tleft lt RT h => _
        | tright LT h rt => _

        | tcase crit lf rf => _
        | trcons i head tail => _
        | text T t h => Some (extty_to_ty T)
        | tfield T h0 h1 i => _
    end
    ).


    Ltac NotNoneInCtx :=
        match goal with
        | h : _ = None |- _ => exact None 
        | h : None = _ |- _ => exact None 
        | |- _ => idtac
        end.
    Ltac AssertORFU Tx :=
        destruct (orfu_dec Tx);
        match goal with
        | h : ~orfu Tx |- _ => exact None
        | |- _ => idtac
        end.

    (* case tvar *)
    destruct (byContext ctx i) eqn:h0; NotNoneInCtx.
    destruct s. 
    AssertORFU x.
    exact (Some x).

    (* case tfun *)
    AssertORFU T. exact (Some (TFun T o)).


    (* case tapp *)
    destruct (check_type ctx f) eqn:h0; NotNoneInCtx.
    destruct t0 eqn: h1;
    match goal with
    | h : t0 = TFun ?I ?O |- _ =>
        destruct (check_type ctx x) eqn:h2;
        NotNoneInCtx
    | |- _ => exact None
    end; NotNoneInCtx.
    destruct (subty_dec t1 t1_1).
    exact (Some t1_2).
    (* when ~ x <: I*)
    exact None.

    (* case tlet *)
    destruct (check_type ctx bind) eqn:h0;
    NotNoneInCtx.
    destruct (eq_ty_dec T t0).
    destruct (check_type (update i (exist wf_ty T h) ctx) body) eqn:h1;
    NotNoneInCtx.
    exact (Some t1). exact None.

    (* case tfixApp *)
    destruct (check_type (update i (exist wf_ty T h) ctx) self) eqn: h0; NotNoneInCtx.
    destruct (subty_dec t0 T). 
    AssertORFU T.
    exact (Some T). exact None. 

    (* case tleft *)
    destruct (check_type ctx lt) eqn: h0; NotNoneInCtx.
    AssertORFU RT.
    exact (Some (TSum t0 RT)).

    (* case tright *)
    destruct (check_type ctx rt) eqn: h0; NotNoneInCtx.
    AssertORFU LT.
    exact (Some (TSum LT t0)).

    (* case tcase *)
    destruct (check_type ctx crit) eqn:h0;
    destruct (check_type ctx lf) eqn:h1;
    destruct (check_type ctx rf) eqn:h2;
    NotNoneInCtx.
        (* crit must be sum*)
        destruct t0 eqn:h3;
        match goal with
        | h : t0 = TSum _ _ |- _ => idtac
        | |- _ => exact None
        end.
        (* lf, rf must be a function*)
        destruct t1 eqn:h4;
        match goal with
        | h : t1 = TFun _ _ |- _ => idtac
        | |- _ => exact None
        end;
        destruct t2 eqn:h5;
        match goal with
        | h : t2 = TFun _ _ |- _ => idtac
        | |- _ => exact None
        end.
        destruct (subty_dec t3_1 t3_3);
        destruct (subty_dec t3_2 t3_5);
        destruct (eq_ty_dec t3_4 t3_6);
        subst; 
        match goal with
        | h0 : check_type ctx crit = Some (TSum ?li ?ri),
          h1 : check_type ctx lf = Some (TFun ?li' ?o),
          h2 : check_type ctx rf = Some (TFun ?ri' ?o),
          h3 : subty ?li ?li' ,
          h4 : subty ?ri ?ri'
          |- _ => exact o
        | |- _ => exact None
        end.
    
        (* case trcons *)
        destruct (check_type ctx head) eqn: h0; 
        destruct (check_type ctx tail) eqn: h1;
        NotNoneInCtx.
        destruct (only_rcd_dec t1).
        destruct (rcd_field_ty' t1 i) eqn: h2.
        exact None.
        AssertORFU t1.
        exact (Some (TRcons i t0 t1)).
        exact None.

        (* case tfield *)
        destruct (rcd_field_ty T h0 h1 i) eqn: h2;
        NotNoneInCtx.
        AssertORFU T. AssertORFU t0.
        exact (Some (TFun T t0)).

Defined.


Theorem typing_alg_well_formed:
    forall ctx t T,
        check_type ctx t = Some  T ->
        wf_ty T.

Proof with eauto; try discriminate.
    intros ctx t. glize ctx 0.
    induction t; intros; cbn in *; subst; eauto; try discriminate;
    repeat (
        match goal with
        | h : (match ?x with _ => _ end) _ = _ |- _ =>
            let h := fresh c in
            destruct x eqn:h
        | h : (match ?x with _ => _ end) _ _ = _ |- _ =>
            let h := fresh c in
            destruct x eqn:h
        | h : (match ?x with _ => _ end) = _ |- _ =>
            let h := fresh c in
            destruct x eqn:h
        | h : (if ?x then _ else _) = _ |- _ =>
            let h := fresh c in
            destruct x
        | h : Some _ = Some _ |- _ => inversion h; subst;eauto; try discriminate; clear h
        end;eauto; try discriminate
    );subst ...

    (* case tapp *)
    forwards*: IHt1...
    forwards*: IHt2...
    inversion H; eauto.

    (* case text *)
    eapply Extty_well_formed.


    (* case tfield *)
    eapply wfFun; eauto.
    unfold rcd_field_ty in *.
    eapply rcd_field_ty'_wf_is_wf; eauto.
Qed.


Theorem typing_alg_orfu:
    forall ctx t T,
    check_type ctx t = Some  T ->
    orfu T.

    intros ctx t. glize ctx 0.
    induction t; intros; cbn in *; subst; eauto; try discriminate;
    repeat (
        match goal with
        | h : (match ?x with _ => _ end) _ = _ |- _ =>
            let h := fresh c in
            destruct x eqn:h
        | h : (match ?x with _ => _ end) _ _ = _ |- _ =>
            let h := fresh c in
            destruct x eqn:h
        | h : (match ?x with _ => _ end) = _ |- _ =>
            let h := fresh c in
            destruct x eqn:h
        | h : (if ?x then _ else _) = _ |- _ =>
            let h := fresh c in
            destruct x 
        | h : Some _ = Some _ |- _ => inversion h; subst;eauto; try discriminate; clear h
        end;eauto; try discriminate
    );subst ...

    (* case tapp *)
    forwards*: IHt1. inversion H; subst; eauto.

    (* case tcase *)
    
    inversion H.
    inversion H.
    inversion H.
    inversion H.
    eapply extty_orfu.
Qed.



   


Theorem typing_alg_leg:
    forall ctx t T,
        check_type ctx t = Some T ->
        has_type ctx t T.

    intros ctx t. glize ctx 0.
    induction t; intros; subst; cbn in *; eauto; try discriminate.
    
    (* TNone *)
    destruct (byContext ctx i) eqn:h0.
    destruct s; eauto.
    destruct (orfu_dec x); subst; eauto; try discriminate.
    inversion H; subst; eauto.
    try discriminate.
    inversion H; subst; eauto.
    

    (* TFun *)
    destruct (check_type (update i (exist wf_ty T w) ctx) t) eqn:h0.
    destruct (orfu_dec T); subst; eauto; try discriminate.
    inversion H; subst; eauto.
    try discriminate.

    (* case tapp *)
    destruct (check_type ctx t1) eqn:h0.
    destruct t. destruct (check_type ctx t2) eqn:h1.
    destruct (subty_dec t t3); eauto. inversion H; subst; eauto.
    eapply ht_app; eauto.