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
Require Import SmallCoreTypeAlg.

Import SmallCore.SmallCore.
Import SmallCoreTypeAlg.SmallCoreTypeAlg.
Import SmallCoreTyping.SmallCoreTyping.
Import SmallCoreORFU.SmallCoreORFU.
Import SmallCoreStep.SmallCoreStep.
Import SmallCorePropSubty.SmallCorePropSubty.
Import Context.Context.

Module SmallCoreAlg.

Theorem typing_alg_progress:
    forall t T,
        check_type empty t = Some T ->
        value t \/ exists t', step t t'.
        
    intros. eapply progress. eapply typing_alg_leg; eauto.
Qed.

Theorem eq_extty_dec:
    forall (X Y : Extty),
        {X = Y} + {X <> Y}.
    
    intros X.
    induction X; intro Y;
    induction Y; intros; subst; eauto;
    try (
        left; eauto; fail);
    try (
        right; intro; 
        try match goal with
        | h : _ = _ |- _ => inversion h; subst; eauto; try discriminate
        end; eauto; try discriminate; fail
    ).
    destruct (eq_id_dec t t0); subst; eauto;
    try (
        left; eauto; fail);
    try (
        right; intro; 
        try match goal with
        | h : _ = _ |- _ => inversion h; subst; eauto; try discriminate
        end; eauto; try discriminate; fail
    ).

    destruct (eq_id_dec t t0); subst; eauto.
    clear IHY.
    destruct (IHX Y); destructALL; subst; eauto;
    try (
        left;subst; eauto; fail);
    try (
        right; intro; 
        try match goal with
        | h : _ = _ |- _ => inversion h; subst; eauto; try discriminate
        end; eauto; try discriminate; fail
    ).
    right; intro. inversion H; subst; eauto.

    clear IHY1; clear IHY2.
    destruct (IHX1 Y1); destruct (IHX2 Y2); destructALL;
    try (
        left; subst; eauto; fail);
    try (
        right; intro; 
        try match goal with
        | h : _ = _ |- _ => inversion h; subst; eauto; try discriminate
        end; eauto; try discriminate; fail
    ).
Qed.




Fixpoint one_step (t: tm) : tm.
    refine (
        match t with
        | tapp f x => _
        | tlet i T h bind body => _
        | tfixApp i T h self => subst i (tfixApp i T h self) self 
        | tleft lt RT h => _
        | tright LT h rt => _
        | tcase crit lb rb => _ 
        | trcons i head tail => _
        | x => x
        end
    ).

    (* case tapp *)
    destruct (value_dec f);
    try (
        match goal with
        | h : ~value ?F |- _=> exact (tapp (one_step F) x)
        end
    );
    destruct (value_dec x);
    try (
        match goal with
        | h : ~value ?X |- _=> exact (tapp f (one_step x))
        end
    ).


    destruct f eqn:h0;
    (
        match goal with
        | h: f = (tfun _ _ _ _) |- _ => idtac
        | h: f = (tfield _ _ _ _) |- _ => idtac
        | h : f = text _ _ _ |- _ => idtac
        | |- _ => exact t
        end
    ).

    (* case f = tfun *)
    exact (subst i x t1).
    (* case f = text *)
        destruct x eqn: h1;
        match goal with
        | h : x = text _ _ _ |- _ => idtac
        | |- _ => exact t
        end.
        destruct T eqn: h2;
        match goal with
        | h : T = ETFun _ _ |- _ => idtac
        | |- _ => exact t
        end.
        destruct (eq_extty_dec (ETVar t3) T0).
        subst.
        destruct (ExttmInterpreter t3 e1 t1 t2 e e0).
        exact (text e1 x e2).
        exact t.
    (* case f = tfield *)
    destruct (rcd_field_tm' x i) eqn:h2.
    exact t1.
    exact t.
    (* case tlet *)
    destruct (value_dec bind).

    exact (subst i bind body).
    exact (tlet i T h (one_step bind) body).

    (* case tleft*)
    destruct (value_dec lt).
    exact t.
    exact (tleft (one_step lt) RT h).

    (* case tright *)
    destruct (value_dec rt).
    exact t.
    exact (tright LT h (one_step rt)).

    (* case tcase *)

    destruct (value_dec crit);
    try (
        match goal with
        | h : ~value crit |- _ => exact (tcase (one_step crit) lb rb)
        end
    ).
    destruct (value_dec lb);
    try (
        match goal with
        | h : ~value lb |- _ => exact (tcase crit (one_step lb) rb)
        end
    ).
    destruct (value_dec rb);
    try (
        match goal with
        | h : ~value rb |- _ => exact (tcase crit lb (one_step rb))
        end
    ).
    destruct crit eqn:h0;
    match goal with
    | h : crit = tleft ?t _ _ |- _ => exact (tapp lb t)
    | h : crit = tright _ _ ?t |- _ => exact (tapp rb t)
    | h : crit = text _ _ _ |- _ => idtac
    | |- _ => exact t
    end.
    destruct T eqn: h1;
    match goal with
    | h : T = ETSum _ _ |- _ => idtac
    | |- _ => exact t
    end.
    destruct (ExttmSumResolver e0_1 e0_2 t1 e) eqn:h2.
    destruct s. exact (tapp lb (text e0_1 x e0)).
    destruct s. exact (tapp rb (text e0_2 x e0)).

    destruct (value_dec head);
    try (
        match goal with
        | h : ~value head |- _ => exact (trcons i (one_step head) tail)
        end
    ).
    destruct (value_dec tail);
    try (
        match goal with
        | h : ~value tail |- _ => exact (trcons i head (one_step tail))
        end
    ).
    exact t.
Defined.

Theorem one_step_value_id:
    forall x,
        value x ->
        one_step x = x.

    intros x; induction x;
    intros; subst; cbn in *; eauto; try discriminate;
    repeat (
        match goal with
        | |- (if ?x then _ else _) = _ => 
            let c := fresh c in
                destruct x eqn:c; try contradiction; try discriminate; eauto
        | h : value (_ _) |- _ => inversion h; subst; eauto;try contradiction; try discriminate; clear h

        end
    ).
Qed.

Axiom eq_is_only_eq:
    forall (X:Set) (x: X) (y: x = x), y = eq_refl.

Theorem one_step_step:
    forall t t',
        step t t' ->
        one_step t = t'.

    intros t t' h.
    induction h; intros; subst; cbn in *; eauto; try discriminate;
    repeat (
        match goal with
        | |- (if ?x then _ else _) = _ => 
            let c := fresh c in
                destruct x eqn:c; try contradiction; try discriminate; eauto
        | |- (match ?x with _ => _ end) = _ =>
            let c := fresh c in
            destruct x eqn:c; try contradiction; try discriminate; eauto
        | |- (match ?x with _ => _ end) _ = _ =>
            let c := fresh c in
            destruct x eqn:c; try contradiction; try discriminate; eauto
        | h : value (_ _) |- _ => inversion h; subst; eauto;try contradiction; try discriminate; clear h
        end
    );
    try tac_value_no_step;
    try (
        match goal with
        | h : ~ (value (?x)) |- _ =>
            assert (value x); eauto
        end; try contradiction
    ).

    (* case tcase *)
    inversion H1; subst; eauto.
    rewrite (Exteqeq _ _ e h'); eauto.
    inversion H1; subst; eauto.
    rewrite (Exteqeq _ _ e h'); eauto.
    (* case tfield *)
    inversion H0; subst; eauto.

    (* case tapp *)
    
    compute. 
    rewrite (eq_is_only_eq _ _ e).
    destruct (eintp i O f x h0 h1). eauto.
Qed.


End SmallCoreAlg.



