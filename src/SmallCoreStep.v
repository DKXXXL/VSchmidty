Add LoadPath "src".
Require Import Maps.
Require Import Context.

Import Context.Context.
Require Import Coq.Lists.List.
Require Import LibTactics.
Require Import SmallCore.
Require Import Coq.ZArith.ZArith.
Require Import SmallCorePropSubty.

Import SmallCore.SmallCore.
Import SmallCorePropSubty.SmallCorePropSubty.
Import Context.Context.


Module SmallCoreStep.


Inductive value : tm -> Prop :=
    | vNone : value tnone
    | vRcons : forall i t0 t1,
                value t0 ->
                value t1 ->
                value (trcons i t0 t1)
    | vfun : forall i T wft body,
                value (tfun i T wft body)
    | vleft : forall t T wft,
                value t ->
                value (tleft t T wft)
    | vright : forall T wft t,
                value t ->
                value (tright T wft t)
    | vfield : forall T ort wft id,
                value (tfield T ort wft id).

Hint Constructors value.

(* subst (i:id) (rep: tm) (org: tm) : tm *)
Fixpoint subst (i : id) (rep : tm) (org : tm) : tm :=
    let rp' := subst i rep
    in
    match org with

    | trcons i t0 t1 => trcons i (rp' t0) (rp' t1)
    | tvar i0 => if (eq_id_dec i i0) then rep else org

    | tfun i0 T w body =>
        if (eq_id_dec i i0) then org else tfun i0 T w (rp' body)
    | tapp p q => tapp (rp' p) (rp' q)
    | tlet i0 T w bind body =>
        if (eq_id_dec i i0) then tlet i0 T w (rp' bind) body else tlet i0 T w (rp' bind) (rp' body)
    | tfixApp i0 T w body =>
        if (eq_id_dec i i0) then org else tfixApp i0 T w (rp' body)
    | tleft l R w => tleft (rp' l) R w
    | tright L w r => tright L w (rp' r)
    | tcase a b c => tcase (rp' a) (rp' b) (rp' c)
    | _ => org
    end.




(* Open Scope Int_scope. *)
(*Check Nat.eqb.*)



Inductive step : tm -> tm -> Prop :=
    | strcons0:
        forall i t0 t0' t1,
            step t0 t0' ->
            step (trcons i t0 t1) (trcons i t0' t1)
    | strcons1 :
        forall i t0 t1 t1',
            value t0 ->
            step t1 t1' ->
            step (trcons i t0 t1) (trcons i t0 t1')
    | stapp0 :
        forall f f' x,
            step f f' ->
            step (tapp f x) (tapp f' x)
    | stapp1:
        forall f x x',
            value f ->
            step x x' ->
            step (tapp f x) (tapp f x')
    | stapp2 :
        forall i T h body x,
            value x ->
            step (tapp (tfun i T h body) x) (subst i x body)
    | stlet0 :
        forall i T w bind bind' body,
            step bind bind' ->
            step (tlet i T w bind body) (tlet i T w bind' body)
    | stlet1 :
        forall i T w bind body,
            value bind ->
            step (tlet i T w bind body) (subst i bind body)
    | stfixApp :
        forall i T w fixbody,
            step (tfixApp i T w fixbody) (subst i (tfixApp i T w fixbody) fixbody)
    | stleft :
        forall l l' w R,
            step l l' ->
            step (tleft l w R) (tleft l' w R)
    | stright :
        forall w L r r',
            step r r' ->
            step (tright w L r) (tright w L r')
    | stcase0 :
        forall crit crit' lb rb,
            step crit crit' ->
            step (tcase crit lb rb) (tcase crit' lb rb)
    | stcase1 :
        forall crit lb lb' rb,
            value crit ->
            step lb lb' ->
            step (tcase crit lb rb) (tcase crit lb' rb)
    | stcase2 :
        forall crit lb rb rb',
            value crit ->
            value lb ->
            step rb rb' ->
            step (tcase crit lb rb) (tcase crit lb rb')
    | stcase3 :
        forall lt RT w1 lb rb,
            value lt ->
            value lb ->
            value rb ->
            step (tcase (tleft lt RT w1) lb rb)
                    (tapp lb lt)
    | stcase4 :
        forall rt LT w0 lb rb,
            value rt ->
            value lb ->
            value rb ->
            step (tcase (tright LT w0 rt) lb rb)
                    (tapp rb rt)
    | stfield0 :
        forall T orcd w i j head tail,
            value (trcons j head tail) ->
            i <> j ->
            step (tapp (tfield T orcd w i) (trcons j head tail)) (tapp (tfield T orcd w i) tail)  
    | stfield1 :
        forall T orcd w i head tail,
            value (trcons i head tail) ->
            step (tapp (tfield T orcd w i) (trcons i head tail)) head.
    Hint Constructors step.


    Ltac eli_dupli_wf_ty :=
    repeat (
        match goal with
        | w1 : wf_ty ?t, w2 : wf_ty ?t |- _ =>
            poses' (wf_ty_indistinct t w1 w2);
            subst
        end
    ).
Ltac eli_dupli_orcd :=
    repeat (
        match goal with
        | w1 : only_rcd ?t, w2 : only_rcd ?t |- _ =>
            poses' (orcd_indistinct t w1 w2);
            subst
        end
    ).

Ltac eli_dupli_wf_ty_orcd := eli_dupli_wf_ty; eli_dupli_orcd.


Lemma value_no_step :
    forall t,
        value t ->
        (forall t',
            ~step t t'
        ) .
    intros t h.
    induction h; intros; intro; subst; eauto;
    match goal with
    | h0 : step _ _ |- _ => inversion h0; subst; eauto;
        try match goal with
        | h0 : step ?X1 _, h1 : forall _ : tm, ~ step ?X1 _ |- _ => destruct (h1 _ h0)
        end;
    fail
    | _ => idtac
    end.
Qed.

Ltac tac_value_no_step :=
    match goal with
    | h0 : value ?X1, h1 : step ?X1 _ |- _ => 
        destruct (value_no_step _ h0 _ h1)
    end.

Ltac forwards_ALL_det:=
    match goal with
    | h0 : forall _:_, _ -> ?X1 = _, 
      h1 : step _ ?X1,
      h2 : step _ _|- _ =>
        poses' (h0 _ h2);
        generalize dependent h0;
        forwards_ALL_det
    | _ => intros
    end.


Theorem step_deterministic:
    forall t t1 t2,
        step t t1 ->
        step t t2 ->
        t1 = t2.
    intros t t1 t2 h1.
    generalize dependent t2.
    induction h1;intros; eauto;
    match goal with
    | h0 : step _ _ |- _ => 
        inversion h0
    end; subst; eauto;
    try(forwards_ALL_det; subst; eauto);
    try 
    (
    try 
    match goal with
        | h0 : step (tfun ?i ?T ?wft ?body) _ |- _ => poses' (vfun i T wft body)
    end;
    try 
    match goal with
        | h0 : step (tfield ?T ?ort ?wft ?i) _ |- _ =>
            poses' (vfield T ort wft i)
    end;
    
    try (match goal with
        | h0 : ?x <> ?x |- _ => destruct (h0 eq_refl)
        end
    );
    try 
    match goal with
        | h0 : step (tleft ?lt ?RT ?w1) _, h1: value ?lt |- _ =>
            poses' (vleft lt RT w1 h1)
    end;
    try 
    match goal with
        | h0 : step (tright ?LT ?w0 ?rt) _, h1: value ?rt |- _ =>
            poses' (vright LT w0 rt h1)
    end;
    try tac_value_no_step; 
    fail
    );
    try (
        eli_dupli_wf_ty_orcd; eauto
    ).

Qed.




