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

Fixpoint progress' (t: tm) : tm.
    refine (
        match t with
        | tapp f x => _
        | tlet i T h bind body => subst i bind body
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
    destruct (value_dec x).

    destruct f eqn:h0;
    (
        match goal with
        | h: f = (tfun _ _)
    )


    


Definition one_step_interpret (t : tm) : option tm.
    destruct (check_type empty t) eqn:h0;
    NotNoneInCtx.

    forwards*: typing_alg_leg.
    forwards*: progress.
    destruct H0.






