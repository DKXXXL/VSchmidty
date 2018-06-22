Add LoadPath "src".
Require Import Maps.
Require Import Context.

Import Context.Context.
Require Import Coq.Lists.List.
Require Import LibTactics.
Require Import SmallCore.

Import SmallCore.SmallCore.
Import Context.Context.

Module SmallCoreProp.

Ltac forwardALL :=
    repeat (
        match goal with
        | h0 : _ -> _ |- _ =>
            forwards*: h0; generalize dependent h0
        end
    ); intros.


Lemma subty_TVar_inver0:
    forall i x,
        subty (TVar i) x ->
        x = TVar i.

intros i x h0.
remember (TVar i) as y. generalize dependent Heqy.
induction h0; intros;subst; eauto; try discriminate.
forwardALL; eauto; subst.
eauto.
Qed.

Lemma subty_TVar_inver1:
    forall i x,
    subty x (TVar i)->
    x = TVar i.

    intros i x h0.
    remember (TVar i) as y. generalize dependent Heqy.
    induction h0; intros;subst; eauto; try discriminate.
    inversion H2.
    forwardALL; eauto; subst.
    eauto.
Qed.




Theorem subty_dec_compl: 
forall T1 T2,
{subty T1 T2 /\ subty T2 T1} +
{subty T1 T2 /\ ~subty T2 T1} +
{~subty T1 T2 /\ subty T2 T1} +
{~subty T1 T2 /\ ~subty T2 T1}.

intros T1;
induction T1;
intros T2;
induction T2; intros; subst; try discriminate; eauto.
