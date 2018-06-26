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

Import SmallCore.SmallCore.
Import SmallCoreStep.SmallCoreStep.
Import SmallCorePropSubty.SmallCorePropSubty.
Import Context.Context.

Module SmallCoreTyping.


Inductive has_type : Context (type := {x : ty | wf_ty x}) -> tm -> ty -> Prop :=
| ht_none : 
    forall ctx,
        has_type ctx tnone TNone
| ht_rcd :
    forall ctx i t0 t1 T T',
        has_type ctx t0 T ->
        has_type ctx t1 T' ->
        only_rcd T' ->
        has_type ctx (trcons i t0 t1) (TRcons i T T')
| ht_var: forall ctx T i (h: wf_ty T),
    byContext ctx i = Some (exist _ T h) ->
    has_type ctx (tvar i) T
| ht_fun : forall ctx i T body TO (h: wf_ty T),
    has_type (update i (exist _ T h) ctx) body TO ->
    has_type ctx (tfun i T h body) (TFun T TO)
| ht_app : forall ctx t0 t1 T0 T1,
    has_type ctx t0 (TFun T0 T1) ->
    has_type ctx t1 T0 ->
    has_type ctx (tapp t0 t1) T1
| ht_let : forall ctx i T bind body T' (h: wf_ty T),
    has_type ctx bind T ->
    has_type (update i (exist _ T h) ctx) body T' ->
    has_type ctx (tlet i T h bind body) T'
| ht_fix : forall ctx i body T (h:wf_ty T),
    has_type (update i (exist _ T h) ctx) body T ->
    has_type ctx (tfixApp i T h body) T
| ht_left : forall ctx t0 TL TR (h: wf_ty TR),
    has_type ctx t0 TL ->
    has_type ctx (tleft t0 TR h) (TSum TL TR)
| ht_right : forall ctx t0 TL TR (h: wf_ty TL),
    has_type ctx t0 TR ->
    has_type ctx (tright TL h t0) (TSum TL TR)
| ht_case : forall ctx crit tl tr TL TR TO,
    has_type ctx crit (TSum TL TR) ->
    has_type ctx tl (TFun TL TO) ->
    has_type ctx tr (TFun TR TO) ->
    has_type ctx (tcase crit tl tr) TO
| ht_field : forall ctx i T0 T (h0: only_rcd T0) (h1: wf_ty T0),
    rcd_field_ty T0 h0 h1 i = Some T ->
    has_type ctx (tfield T0 h0 h1 i) (TFun T0 T)
| ht_subty: forall ctx t T0 T1,
    has_type ctx t T0 ->
    subty T0 T1 ->
    RFU T0 ->
    T0 <> T1 ->
    has_type ctx t T1.



Hint Constructors has_type.


Inductive free_occur_in : id -> tm -> Prop :=
    | fo_rcons0 : forall i j t0 t1,
                free_occur_in i t0 ->
                free_occur_in i (trcons j t0 t1)
    | fo_rcons1 : forall i j t0 t1,
                free_occur_in i t1 ->
                free_occur_in i (trcons j t0 t1)
    | fo_var : forall i,
                free_occur_in i (tvar i)

    | fo_fun : forall i j T h body,
                i <> j ->
                free_occur_in i body ->
                free_occur_in i (tfun j T h body)
    | fo_app0 : forall i t0 t1,
                free_occur_in i t0 ->
                free_occur_in i (tapp t0 t1)
    | fo_app1 : forall i t0 t1,
                free_occur_in i t1 ->
                free_occur_in i (tapp t0 t1)
    | fo_let0 : forall i j T h t0 t1,
                free_occur_in i t0 ->
                free_occur_in i (tlet j T h t0 t1)
    | fo_let1 : forall i j T h t0 t1,
                i <> j ->
                free_occur_in i t1 ->
                free_occur_in i (tlet j T h t0 t1)
    | fo_fixApp : forall i j T h t0,
                i <> j ->
                free_occur_in i t0 ->
                free_occur_in i (tfixApp j T h t0)
    | fo_left : forall i t0 T h,
                free_occur_in i t0 ->
                free_occur_in i (tleft t0 T h)
    | fo_right: forall i t0 T h,
                free_occur_in i t0 ->
                free_occur_in i (tright T h t0)
    | fo_case0: forall i t0 t1 t2,
                free_occur_in i t0 ->
                free_occur_in i (tcase t0 t1 t2)
    | fo_case1: forall i t0 t1 t2,
                free_occur_in i t1 ->
                free_occur_in i (tcase t0 t1 t2)
    | fo_case2: forall i t0 t1 t2,
                free_occur_in i t2 ->
                free_occur_in i (tcase t0 t1 t2).

Hint Constructors free_occur_in.
        
(*Lemma closed_no_free_occur:
    forall t T,
        has_type empty t T ->
        forall i, ~ free_occur_in i t.
    intros t T h0.
    remember empty as ctx0.
    glize Heqctx0 0.
    induction h0; intros; subst; intro; 
    repeat (
        match goal with
        | h : ?x = ?x -> _ |- _ => poses' (h eq_refl); clear h
        end
    );
    try (
    repeat (
        match goal with
        | h : forall _ : id, _ |- _ => poses' (h i); glize h 0
        end); 
    intros;
    try match goal with
    | h1 : free_occur_in _ _ |- _ => inversion h1; subst; eauto; fail
    | h1 : free_occur_in _ _ |- _ => inversion h1; subst;
        match goal with
        | h2 : free_occur_in ?ii ?t, h3: forall _:id, ~free_occur_in _ ?t |- _ => 
            poses' (h3 ii); eauto
        end; fail 
    end; 
    fail
    ).

    (* case tvar *)
    cbn in H. inversion H.
    (* case tfun *)
    inversion H; subst; eauto.  
    Abort.
    *)
Definition relative_ctx_eq (t : tm) (ctx0 ctx1: Context) :=
    (forall i, free_occur_in i t ->  
                byContext (type := {x : ty | wf_ty x}) ctx0 i = byContext ctx1 i).

Theorem rce_refl:
    forall t x,
    relative_ctx_eq t x x.
    unfold relative_ctx_eq.
    eauto.
Qed.

Theorem rce_symm:
    forall t x y,
        relative_ctx_eq t x y ->
        relative_ctx_eq t y x.
    unfold relative_ctx_eq.
    intros; eauto. symmetry. eauto.
Qed.

Theorem rce_trans:
    forall t x y z,
        relative_ctx_eq t x y ->
        relative_ctx_eq t y z ->
        relative_ctx_eq t x z.
    unfold relative_ctx_eq.
    intros. poses' (H _ H1); poses' (H0 _ H1).
    rewrite H2; rewrite H3.
    auto.
Qed.
    
Hint Unfold relative_ctx_eq.



Theorem ctx_change:
    forall ctx0 ctx1 t T,
    has_type ctx0 t T ->
    relative_ctx_eq t ctx0 ctx1 ->
    has_type ctx1 t T.

    intros ctx0 ctx1 t T h0. glize ctx1 0.
    unfold relative_ctx_eq.
    induction h0; intros; subst; eauto;
    try(
    repeat (
        match goal with
        | h1: forall _: Context, _ |- _ => poses' (h1 ctx1); glize h1 0
        end
    );
    intros;
    repeat (
        match goal with
        | h0 :  _ -> has_type _ _ _ |- _ => forwards: h0; glize h0 0
        end
    );
    intros;
    eauto;
    fail).

    (* case tvar*)
    poses' (H0 i). forwards: H1; eauto.
    pattern (byContext ctx i) in H.
    rewrite H2 in H. eauto.

    (* case tfun*)
    eapply ht_fun.
    eapply IHh0. 
    intros. cbn. destruct (eq_id_dec i0 i); subst; eauto.

    (* case tlet*)
    eapply ht_let. eapply IHh0_1.
    intros. eauto.
    eapply IHh0_2. intros; eauto.
    cbn. destruct (eq_id_dec i0 i); subst; eauto.

    (* case tfix *)
    eapply ht_fix. eapply IHh0. intros; cbn.
    destruct (eq_id_dec i0 i); subst; eauto.
Qed.

Lemma ctx_typed_fv_exists:
    forall ctx t T,
        has_type ctx t T ->
        (forall i, free_occur_in i t -> exists h, byContext ctx i = Some h).

    intros ctx t T h0.
    induction h0 ; subst; eauto; intros;
    try (
        match goal with
        | h: free_occur_in _ _ |- _ =>
            inversion h; subst; eauto; fail
        end
    );
    try (
        (* Eliminate all cases that depends inductibly and no special cases *)
    match goal with
    | h : free_occur_in ?ii (_ _) |- _ => 
            inversion h; subst; eauto;
            
                match goal with
                | h : forall _:id, _ , h0 : free_occur_in ?ii _ |- _ -> _ =>
                        destruct (h ii h0); glize h 0
                end
    end;
    intros; eauto
    ).
    

    (* case tfun *)
    inversion H; subst; eauto.
    destruct (IHh0 i0 H5); subst; eauto.
    cbn in H0. destruct (eq_id_dec i0 i); subst; eauto; try contradiction.
    
    (* case tlet *)
    inversion H; subst; eauto. destruct (IHh0_2 i0 H6); subst; eauto.
    cbn in H0; subst; eauto. destruct (eq_id_dec i0 i); subst; eauto; try contradiction.

    (* case tfix*)
    inversion H; subst; eauto. destruct (IHh0 i0 H5); subst; eauto.
    cbn in H0; subst; eauto. destruct (eq_id_dec i0 i); subst; eauto; try contradiction.

Qed.


Theorem typed_closed :
    forall t T,
        has_type empty t T ->
        (forall i, ~ free_occur_in i t).

    intros t T h0. remember empty as ctx0.
    glize Heqctx0 0.
    induction h0; intros; subst; intro;
    repeat (
        match goal with
        | h : ?x = ?x -> _ |- _ => poses' (h eq_refl); clear h
        end
    );
    try (
        match goal with
        | h : free_occur_in _ _ |- _ => 
            inversion h; subst; eauto;
            match goal with
            | h0 : free_occur_in ?ii ?tt, h1 : forall _:id, ~ free_occur_in _ ?tt |- _ =>
                destruct (h1 ii h0)
            end
        end; fail
    ).

    (* case tvar *)
    inversion H.
    (* case tfun*)
    inversion H; subst; eauto.
    destruct 
    (ctx_typed_fv_exists 
    (update i (exist wf_ty T h) empty) 
    body TO h0 i0 H5).
    cbn in H0. destruct (eq_id_dec i0 i); subst; eauto; try contradiction.
    inversion H0.

    (* case tlet *)
    inversion H; subst; eauto.
    destruct (H0 _ H3).
    destruct 
    (ctx_typed_fv_exists 
    (update i (exist (fun x => wf_ty x) T h) empty)
    body T' h0_2 i0 H7
    ).
    cbn in H1. destruct (eq_id_dec i0 i); subst; eauto; try contradiction.
    inversion H1.

    (* case tfix *)
    inversion H; subst; eauto.
    destruct 
    (ctx_typed_fv_exists 
    (update i (exist wf_ty T h) empty)
    body T h0 i0 H5
    ).
    cbn in H0. destruct (eq_id_dec i0 i); subst; eauto; try contradiction.
    inversion H0.
Qed.




Theorem typed_relative_closed:
    forall t T,
        has_type empty t T ->
        forall ctx,
            relative_ctx_eq t ctx empty.
    intros t T h0.
    poses' (typed_closed t T h0).
    unfold relative_ctx_eq.
    intros. destruct (H _ H0).
Qed.

Theorem ctx_eq_rewrite:
    forall U V t T,
        has_type U t T ->
        CtxEq U V ->
        has_type V t T.
    intros U V t T h0;
    glize V 0.
    induction h0; subst; eauto.
    intros. poses' (CtxEq_byCtxEq _ _ H0).
    eapply ht_var. rewrite <- H1. eauto.
Qed.


Lemma empty_typed_ctx_typed:
    forall t T,
        has_type empty t T ->
        forall ctx,
            has_type ctx t T.
    
    intros t T h0 ctx.
    poses' (typed_relative_closed _ _ h0 ctx) .
    eapply ctx_change; eauto.
    eapply rce_symm; eauto.
Qed.


