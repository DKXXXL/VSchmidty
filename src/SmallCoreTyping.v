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

Import SmallCore.SmallCore.
Import SmallCoreORFU.SmallCoreORFU.
Import SmallCoreStep.SmallCoreStep.
Import SmallCorePropSubty.SmallCorePropSubty.
Import Context.Context.

Module SmallCoreTyping.

Fixpoint extty_to_ty (extty : Extty) : ty.
    destruct extty.
    exact (TVar t).
    exact (TFun (TVar t) (extty_to_ty extty)).
Defined.

Print extty_to_ty.

Theorem extty_orfu:
    forall T,
        orfu (extty_to_ty T).

    induction T; intros; simpl in *; eauto.
Qed.

Inductive has_type : Context (type := {x : ty | wf_ty x}) -> tm -> ty -> Prop :=
| ht_none : 
    forall ctx,
        has_type ctx tnone TNone
| ht_rcd :
    forall ctx i t0 t1 T T',
        has_type ctx t0 T ->
        has_type ctx t1 T' ->
        orfu T' ->
        only_rcd T' ->
        rcd_field_ty' T' i = None ->
        has_type ctx (trcons i t0 t1) (TRcons i T T')
| ht_var: forall ctx T i (h: wf_ty T),
    byContext ctx i = Some (exist _ T h) ->
    orfu T ->
    has_type ctx (tvar i) T
| ht_fun : forall ctx i T body TO (h: wf_ty T),
    has_type (update i (exist _ T h) ctx) body TO ->
    orfu T ->
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
    orfu TR ->
    has_type ctx (tleft t0 TR h) (TSum TL TR)
| ht_right : forall ctx t0 TL TR (h: wf_ty TL),
    has_type ctx t0 TR ->
    orfu TL ->
    has_type ctx (tright TL h t0) (TSum TL TR)
| ht_case : forall ctx crit tl tr TL TR TO,
    has_type ctx crit (TSum TL TR) ->
    has_type ctx tl (TFun TL TO) ->
    has_type ctx tr (TFun TR TO) ->
    has_type ctx (tcase crit tl tr) TO
| ht_field : forall ctx i T0 T (h0: only_rcd T0) (h1: wf_ty T0),
    rcd_field_ty T0 h0 h1 i = Some T ->
    orfu T0 ->
    orfu T ->
    has_type ctx (tfield T0 h0 h1 i) (TFun T0 T)
| ht_ext : forall ctx T t h,
    has_type ctx (text T t h) (extty_to_ty T)
| ht_subty: forall ctx t T0 T1,
    has_type ctx t T0 ->
    subty T0 T1 ->
    orfu T0 ->
    orfu T1 ->
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
    forwards: H1; eauto.
    pattern (byContext ctx i) in H.
    rewrite H2 in H. eauto.

    (* case tfun*)
    eapply ht_fun.
    eapply IHh0. 
    intros. cbn. destruct (eq_id_dec i0 i); subst; eauto.
    eauto.

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
    inversion H0; subst; eauto.
    destruct (IHh0 i0 H6); subst; eauto.
    cbn in *. destruct (eq_id_dec i0 i); subst; eauto; try contradiction.
    
    (* case tlet *)
    inversion H; subst; eauto.
    destruct (IHh0_2 i0 H6); subst; eauto. 
    (* destruct (IHh0_2 i0 H6); subst; eauto. *)
    cbn in *; subst; eauto. destruct (eq_id_dec i0 i); subst; eauto; try contradiction.

    (* case tfix*)
    inversion H; subst; eauto. destruct (IHh0 i0 H5); subst; eauto.
    cbn in *; subst; eauto. destruct (eq_id_dec i0 i); subst; eauto; try contradiction.

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
    inversion H0; subst; eauto.
    destruct 
    (ctx_typed_fv_exists 
    (update i (exist wf_ty T h) empty) 
    body TO h0 i0 H6).
    cbn in *. destruct (eq_id_dec i0 i); subst; eauto; try contradiction.
    try discriminate.

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
    intros. poses' (CtxEq_byCtxEq _ _ H1).
    eapply ht_var. rewrite <- H2. eauto. eauto.
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



Ltac forwardALL :=
    repeat (
        match goal with
        | h0 : _ -> _ |- _ =>
            forwards*: h0; generalize dependent h0
        end
    ); intros.

Lemma Extty_well_formed:
    forall T,
        wf_ty (extty_to_ty T).
    induction T; intros; simpl in *; eauto; subst.
Qed.

Theorem has_type_orfu:
    forall ctx t T,
        has_type ctx t T ->
        orfu T.

    intros ctx t T h.
    induction h; intros; try intro; subst; 
    try match goal with
        | h : only_rcd _ |- _ => inversion h; subst; eauto; try discriminate; try contradiction; fail
    end; 
    try match goal with
    | h : orfu (_ _) |- _ => inversion h; subst; eauto; try discriminate; try contradiction; fail
    end; 
    eauto.
    (* case extty_to_ty *)
    eapply extty_orfu.
Qed.


Theorem has_type_well_formed:
    forall ctx t T,
        has_type ctx t T ->
        wf_ty T.
    intros t T ctx h.
    
    induction h; try (intros; subst; eauto 10; fail); intros; subst;
    try (
        match goal with
        | h: wf_ty (_ _ ) |- _ => inversion h; subst; eauto
        end; fail
    ).

    unfold rcd_field_ty in *.
    eapply wfFun; eauto.
    eapply rcd_field_ty'_wf_is_wf; eauto.
    (* case EXTTY *)
    eapply Extty_well_formed.
    cut (wf_ty T0 /\ wf_ty T1); try tauto; eauto.
    eapply subty_wf; eauto.
Qed.





Lemma value_has_type_inver_tnone0:
    forall T,
        has_type empty tnone T ->
        T = TNone.
    intros T h.
    remember empty as ctx.
    remember tnone as t.
    glize Heqctx Heqt 0.
    induction h; intros; subst; eauto; try discriminate.
    forwards*:IHh; subst.
    eapply subty_onlyrefl_tnone0; eauto.
Qed.


Lemma value_has_type_inver_trcons0:
    forall i t0 t1 T,
        has_type empty (trcons i t0 t1) T ->
        only_rcd T.
    intros i t0 t1 T h.
    remember empty as ctx.
    remember (trcons i t0 t1) as t.
    glize i t0 t1 Heqctx 0.
    induction h; intros; subst; eauto; try discriminate.
    forwards: IHh; eauto. 
    eapply subty_rcd1; eauto.
Qed.


Lemma value_has_type_inver_tsum0:
    forall ctx lt RT w T,
        has_type ctx (tleft lt RT w) T ->
        exists TL TR,
            T = TSum TL TR.

    intros ctx lt RT w T h0.
    remember (tleft lt RT w) as t.
    glize lt RT 0.
    induction h0; intros;subst; eauto;
    try discriminate; try contradiction.
    forwards :IHh0; subst; eauto.
    destructALL; subst; eauto.
    forwards: subty_extrac_tsum0; eauto; subst.
Qed.

Lemma value_has_type_inver_tsum1:
    forall ctx LT w rt T,
        has_type ctx (tright LT w rt) T ->
        exists TL TR,
            T = TSum TL TR.

    intros ctx LT w rt T h0.
    remember (tright LT w rt) as t.
    glize LT rt 0.
    induction h0; intros;subst; eauto;
    try discriminate; try contradiction.
    forwards :IHh0; subst; eauto.
    destructALL; subst; eauto.
    forwards: subty_extrac_tsum0; eauto; subst.
Qed.

Lemma extty_inver:
    forall T,
    (exists i, (extty_to_ty T) = TVar i )\/(exists I O, extty_to_ty T  = TFun I O).
    intros T; destruct T; simpl in *; eauto.
Qed.


Lemma value_has_type_inver_tsum11:
    forall t,
        value t ->
        forall TL TR,
        has_type empty t (TSum TL TR) ->
        (exists w tl tr, t = tleft tl w tr) \/
        (exists w tl tr, t = tright w tl tr).
      
    intros t h0 TL TR h.
    remember empty as ctx;
    remember (TSum TL TR) as H.
    glize h0 Heqctx TL TR 0.
    induction h; intros; subst; eauto; try discriminate;
    try (
        match goal with
        | h : value _ |- _ =>
            inversion h
        end; fail
    ).
    (* case extty *)
    destruct (extty_inver T); destructALL; subst; rewrite HeqH in *; try discriminate.

    forwards*: subty_extrac_tsum1.
Qed.

Lemma value_has_type_inver_tfun1:
    forall t,
        value t ->
        forall iT oT,
        has_type empty t (TFun iT oT) ->
        (exists i T w body, t = tfun i T w body /\ subty iT T /\ orfu T) 
        \/ (exists T o w i, t = tfield T o w i)
        \/ (exists T x h, t = text T x h).

    intros t h0 iT oT H.
    remember empty as ctx;
    remember (TFun iT oT) as T'.
    glize iT oT Heqctx h0 0.
    induction H;intros; subst; eauto; try discriminate;
    try (
        match goal with
        | h : value (_ _) |- _ =>
            inversion h; subst; eauto
        end; fail
    ).

    inversion HeqT'; subst; eauto. left; eauto. exists i. exists iT. exists h. eauto.
    inversion HeqT'; subst; eauto. right; left; eauto.
    right;right; eauto.
    forwards*:subty_extrac_tfun1. destructALL; subst; eauto.
    forwards*:subty_extra_tfun; destructALL; subst.
    
    forwards*:IHhas_type; destructALL; subst; eauto.
    assert (subty iT x2); eauto.
    left. repeat eexists; eauto.
    right; left; eauto.
    right; right; eauto.
    
Qed.

Lemma value_has_type_inver_tfield0:
    forall ctx T0 ort wft i T,
        has_type ctx (tfield T0 ort wft i) T ->
        (exists Ti To, 
            T = TFun Ti To /\ only_rcd Ti /\ subty Ti T0).
    intros ctx T0 ort wft i T h0.
    remember (tfield T0 ort wft i) as t.
    glize T0 i 0.
    induction h0; intros;subst; eauto;
    try discriminate; try contradiction.
    inversion Heqt; subst; eauto.
    repeat eexists; eauto.
    forwards :IHh0; subst; eauto.
    destructALL; subst; eauto.
    forwards: subty_extrac_tfun0; eauto; subst.
    destructALL; subst. forwards*: subty_extra_tfun;destructALL; subst; eauto. 
    repeat exists. repeat split; eauto. eapply subty_rcd; eauto.
Qed.

Lemma value_has_type_inver_tfield0':
    forall ctx T0 ort wft i T,
        has_type ctx (tfield T0 ort wft i) T ->
        (exists Ti To, 
            (T = TFun Ti To 
            /\ only_rcd Ti 
            /\ subty Ti T0
            /\ exists T', rcd_field_ty' T0 i = Some T' /\ subty T' To)
        /\ orfu T0
        ).
    intros ctx T0 ort wft i T h0.
    remember (tfield T0 ort wft i) as t.
    glize T0 i 0.
    induction h0; intros;subst; eauto;
    try discriminate; try contradiction.
    inversion Heqt; subst; eauto.
    repeat eexists; eauto. eapply subRefl.
    unfold rcd_field_ty in *. eapply rcd_field_ty'_wf_is_wf; eauto.
    forwards :IHh0; subst; eauto.
    destructALL; subst; eauto.
    forwards: subty_extrac_tfun0; eauto; subst.
    destructALL; subst. forwards*: subty_extra_tfun;destructALL; subst; eauto. 
    repeat exists. repeat split; eauto. eapply subty_rcd; eauto.
Qed.




Lemma value_has_type_inver_trcd1:
    forall t,
        value t ->
        forall T,
        has_type empty t T ->
        only_rcd T ->
        wf_ty T ->
        t = tnone \/ exists i th tt, t = trcons i th tt.
    intros t h T H.
    remember empty as ctx.
    glize h Heqctx 0.
    induction H; intros; subst; eauto;
    try discriminate;
    try (
        match goal with
        | h: value _ |- _ =>
            inversion h; subst; eauto; fail
        | h: only_rcd _ |- _ =>
            inversion h; subst; eauto
        end;
        fail
    ).
    destruct (extty_inver T); destructALL; 
        match goal with
        | h : extty_to_ty _ = _ |- _ => rewrite h in *
        end; inversion H.
    forwards*:IHhas_type. eapply subty_rcd; eauto.
    destruct (subty_wf _ _ H0); eauto.
Qed.

Lemma tfield_never_none:
    forall ctx x y z T,
        ~has_type ctx (tfield TNone x y z) T.
    
    intros ctx x y z T h.
    remember (tfield TNone x y z) as t.
    glize x y z 0.
    induction h; intros; subst; eauto ;try discriminate.
    inversion Heqt; subst; eauto.
    unfold rcd_field_ty in H. simpl in H; try discriminate.
Qed.


Lemma subty_onlyrefl_text:
    forall T T',
        (subty (extty_to_ty T) T') \/ subty T' (extty_to_ty T) ->
        T' = extty_to_ty T.


    induction T; intros; subst; simpl in *; eauto;
    destructALL.
    (* case TVar *)
    forwards*: subty_onlyrefl_TVar0; eauto.
    forwards*: subty_onlyrefl_TVar1; eauto.
    (* case TFun *)
    forwards*: subty_extrac_tfun0; eauto; destructALL; subst; eauto.
        forwards*: subty_extra_tfun; destructALL; subst; eauto.
        forwards*: subty_onlyrefl_TVar1; eauto.
        forwardALL; subst; eauto.
    forwards*: subty_extrac_tfun1; eauto; destructALL; subst; eauto.
        forwards*: subty_extra_tfun; destructALL; subst; eauto.
        forwards*: subty_onlyrefl_TVar0; eauto.
        forwardALL; subst; eauto.
Qed.

    



Lemma value_has_type_inver_text0:
    forall T t h T',
        has_type empty (text T t h) T' ->
        T' = extty_to_ty T.

    intros T t h0 T' h.
    remember empty as ctx.
    remember (text T t h0) as x.
    glize T t Heqctx 0.
    induction h; intros; subst; eauto; try discriminate.

    inversion Heqx; subst; eauto.
    edestruct H2.
    forwards*: IHh; subst; eauto.
    symmetry. eapply subty_onlyrefl_text; eauto.
Qed.

Lemma value_has_type_inver_text1:
    forall t T,
        has_type empty t (extty_to_ty T) ->
        exists x h0, t = text T x h0.

    intros t T.
    glize t 0.
    induction T; intros; simpl in *; subst; eauto.
    Focus 2.


Abort.
    
Lemma value_has_type_inver_TVar1:  
    forall t I,
        has_type empty t (TVar I) ->
        value t ->
        exists x h0, t = text (ETVar I) x h0.

    intros t I h.
    remember empty as ctx.
    remember (TVar I) as T.
    glize I Heqctx 0.
    induction h; intros; subst; eauto; try discriminate;
    try (match goal with
        | h : value _ |- _ => inversion h; subst; eauto; try discriminate; fail
        end
    ).
    destruct T; simpl in *; try discriminate.
    inversion HeqT; subst; eauto.
    
    edestruct H2. eapply subty_onlyrefl_TVar1; eauto.
Qed.




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

Ltac construct_orcd :=
repeat match goal with
| h0 : subty ?x ?y, h1 : only_rcd ?x |- _ => 
    poses' (subty_rcd1 _ _ h1 h0);
    glize h0 0
| h0 : subty ?x ?y, h1 : only_rcd ?y |- _ =>
    poses' (subty_rcd _ _ h1 h0);
    glize h0 0
end; intros.

Ltac construct_wf_ty_and_orcd :=
repeat match goal with
| h0 : subty _ _ |- _ =>
    destruct (subty_wf _ _ h0);
    destructALL; glize h0 0
| h0 : has_type _ _ ?T |- _ => 
    poses' (has_type_well_formed _ _ _ h0);
    destructALL; glize h0 0
end; intros;construct_orcd.

Lemma value_has_type_inver_tfun3:
    forall ctx i T h body T0 T1,
        has_type ctx (tfun i T h body) (TFun T0 T1) ->
        has_type (update i (exist wf_ty T h) ctx) body T1.

    intros. remember (tfun i T h body) as tm.
    remember (TFun T0 T1) as Ty.
    glize T0 T T1 i body 0.

    induction H; intros; subst; eauto; try discriminate.
    inversion Heqtm; inversion HeqTy; subst; eauto.
    eli_dupli_wf_ty_orcd. eauto.

    forwards*: subty_extrac_tfun1. destructALL; subst; eauto.
    forwards*: IHhas_type.
    destruct (eq_ty_dec x0 T2); subst; eauto.
    inversion H1; inversion H2; subst; eauto.
    eapply ht_subty; eauto.
    forwards*: subty_extra_tfun; eauto.
Qed.



Lemma record_has_type_has_field:
    forall t T i T',
        has_type empty t T ->
        value t ->
        rcd_field_ty' T i = Some T' ->
        exists t', rcd_field_tm' t i = Some t'.

    intros t T i T' h.
    remember empty as ctx.
    glize  T' i Heqctx 0.
    induction h; subst; eauto;intros;subst; try discriminate;
    try match goal with
        | h : value _ |- _ => inversion h; subst; eauto; try discriminate; fail
        end;
    repeat match goal with
            | h: ?x = ?x -> _ |- _ => poses' (h eq_refl); clear h
            end.
    (* case ht_rcd *)
    simpl in *.
    destruct (eq_id_dec i i0); subst; eauto; try discriminate.
    inversion H2; subst; eauto.

    (* case ht_ext*)
    destruct (extty_inver T);destructALL; 
    try match goal with | ho : extty_to_ty _ = _ |- _ => rewrite ho in * end;
    simpl in *; try discriminate; eauto.

    (* case ht_sub*)
    
    poses' (subty_defined_well_strong_orfu _ _ H H0 _ _ H4); destructALL.
    eapply H5; eauto.


Qed.

    
Lemma record_has_type_has_field_with_type:
    forall i t t' T T',
        has_type empty t T ->
        value t ->
        rcd_field_ty' T i = Some T' ->
        rcd_field_tm' t i = Some t' ->
        exists T'', has_type empty t' T'' /\ subty T'' T'.
    intros i t t' T T' h.
    remember empty as ctx.
    glize i Heqctx t' T' 0.
    induction h; intros; cbn in *; subst; eauto; try discriminate;
    try (
        match goal with
        | h : value (_ _) |- _ => inversion h; subst; eauto
        end
    ).
    destruct (eq_id_dec i i0); subst; eauto. inversion H3; inversion H4; subst; eauto.
    eexists; split; eauto. eapply subRefl. eapply has_type_well_formed; eauto.

    forwards*: subty_defined_well_strong_orfu. destructALL; eauto.
    
    forwards* : IHh; eauto.
Qed.
    

    



Theorem progress:
    forall t T,
        has_type empty t T ->
        value t \/ (exists t', step t t').

intros t T h.
remember empty as ctx.
glize Heqctx 0.
induction h; intros; subst; eauto; try discriminate;
repeat ( (* Remove Unnecessary assumption*)
    match goal with
    | h0 : ?x = ?x -> _ |- _ => 
        poses' (h0 eq_refl); clear h0
    end 
);
try (
    destructALL;
    forwardALL;
    try (
        left; eauto; fail
    );
    try (
        right; eexists; eauto; fail
    ); fail
).


    (* case tapp *)
    destructALL;
    forwardALL;
    try (
        left; eauto; fail
    );
    try (
        right; eexists; eauto; fail
    ).
    poses' (value_has_type_inver_tfun1 _ H _ _ h1);
    destructALL; subst; eauto.
        (* case tfield*)
        right.
        forwards*: value_has_type_inver_tfield0'; destructALL; subst; eauto.
        inversion H1; subst; eauto.
        assert (orfu x3); eauto. eapply has_type_orfu; eauto.
        assert (has_type empty t1 x); eauto.
            destruct (eq_ty_dec x x3); subst; eauto.
        forwards*: (record_has_type_has_field); destructALL. 

        (* case text *)
        right.
        forwards*: value_has_type_inver_text0; eauto.
        destruct x; subst; eauto; try discriminate.
        simpl in *; eauto.
        inversion H1; subst; eauto.
        forwards*: value_has_type_inver_TVar1; eauto; destructALL; subst; eauto.
    (* case tlet *)
    clear IHh2.
    destructALL;
    forwardALL; eauto.

    (* case tcase *)
    destructALL;
    forwardALL;
    try (
        left; eauto; fail
    );
    try (
        right; eexists; eauto; fail
    ).
    right.

    forwards*: (value_has_type_inver_tsum11 _ H); eauto.
    destructALL;subst; eauto;
    try (
        match goal with
        | h : value (_ _) |- _ => inversion h; subst; eauto; fail
        end
    ).
Qed.

Lemma subst_type_preserve:
    forall i Ti h ctx' ctx t body T,
        has_type ctx' body T ->
        ctx' -=- (update i (exist wf_ty Ti h) ctx) ->
        has_type ctx t Ti ->
        has_type ctx (subst i t body) T.
    intros i Ti h0 ctx' ctx t body T h h'.
    assert (ctx' =-= (update i (exist wf_ty Ti h0) ctx)); eauto.
    eapply CtxEq_byCtxEq; eauto.
    glize Ti t  ctx i 0. 
    induction h; intros; subst; cbn in *; try discriminate; eauto.

    (* case tvar *)
    destruct (eq_id_dec i i0); subst; eauto.
    assert (byContext (update i0 (exist wf_ty Ti h0) ctx0) i0 = byContext ctx i0).
    eapply CtxEq_byCtxEq; eauto.
    rewrite H in *; cbn in *. rewrite eq_id_dec_id in *.
    inversion H3; subst; eauto.

    eli_dupli_wf_ty_orcd.
    eapply ht_var; eauto. 
    assert (byContext (update i0 (exist wf_ty Ti h0) ctx0) i = Some (exist wf_ty T h)).
    rewrite <- H. symmetry. eapply H1. cbn in *; eauto. destruct (eq_id_dec i i0); subst; eauto; try contradiction.


    (* case tfun *)
    destruct (eq_id_dec i i0); subst; eauto.
    eapply ht_fun; eauto. 
    assert (has_type (update i0 (exist wf_ty T h) (update i0 (exist wf_ty Ti h1) ctx0)) body TO).
    eapply ctx_eq_rewrite; eauto.
    assert (has_type (update i0 (exist wf_ty T h) ( ctx0)) body TO).
    eapply ctx_eq_rewrite; eauto. eauto.
    eapply ht_fun; eauto.

    eapply ctx_eq_rewrite.  
    eapply IHh; eauto. eapply CtxEq_byCtxEq.
    eapply eqSymm. eapply eqTrans. eapply eqPermute; eauto.
    eapply eqUpdate. eapply eqSymm; eauto.
    
Abort.

(* Why ?! Why is cannot be proved ?! *)
Lemma subst_type_preserve:
    forall i Ti h ctx' ctx t body T,
        has_type ctx' body T ->
        ctx' -=- (update i (exist wf_ty Ti h) ctx) ->
        has_type empty t Ti ->
        has_type ctx (subst i t body) T.

    intros i Ti h0 ctx' ctx t body T h h'.
    assert (ctx' =-= (update i (exist wf_ty Ti h0) ctx)); eauto.
    eapply CtxEq_byCtxEq; eauto.
    glize Ti t  ctx i 0. 
    induction h; intros; subst; cbn in *; try discriminate; eauto.
    
        (* case tvar *)
        destruct (eq_id_dec i i0); subst; eauto.
        assert (byContext (update i0 (exist wf_ty Ti h0) ctx0) i0 = byContext ctx i0).
        eapply CtxEq_byCtxEq; eauto.
        rewrite H in *; cbn in *. rewrite eq_id_dec_id in *.
        inversion H3; subst; eauto. eapply empty_typed_ctx_typed; eauto.
    
        eli_dupli_wf_ty_orcd.
        eapply ht_var; eauto. 
        assert (byContext (update i0 (exist wf_ty Ti h0) ctx0) i = Some (exist wf_ty T h)).
        rewrite <- H. symmetry. eapply H1. cbn in *; eauto. destruct (eq_id_dec i i0); subst; eauto; try contradiction.
    
        (* case tfun *)
        destruct (eq_id_dec i i0); subst; eauto.
    eapply ht_fun; eauto. 
    assert (has_type (update i0 (exist wf_ty T h) (update i0 (exist wf_ty Ti h1) ctx0)) body TO).
    eapply ctx_eq_rewrite; eauto.
    assert (has_type (update i0 (exist wf_ty T h) ( ctx0)) body TO).
    eapply ctx_eq_rewrite; eauto. eauto.
    eapply ht_fun; eauto.

    eapply ctx_eq_rewrite.  
    eapply IHh; eauto. eapply CtxEq_byCtxEq.
    eapply eqSymm. eapply eqTrans. eapply eqPermute; eauto.
    eapply eqUpdate. eapply eqSymm; eauto. eapply CtxeqId.

    (* case tlet *)
    destruct (eq_id_dec i i0); subst; eauto.
    eapply ht_let; eauto. 
    assert (has_type (update i0 (exist (fun x : ty => wf_ty x) T h1) (update i0 (exist wf_ty Ti h0) ctx0)) body T').
    eapply ctx_eq_rewrite; eauto.
    eapply ctx_eq_rewrite; eauto.
    eapply ht_let; eauto.
    eapply IHh2; eauto. eapply CtxEq_byCtxEq.
    eapply eqSymm. eapply eqTrans. eapply eqPermute. eauto.
    intro. subst; try contradiction. eapply eqUpdate. eapply eqSymm; eauto.

    (* case tfixApp *)
    destruct (eq_id_dec i i0); subst; eauto.
    eapply ht_fix.
    assert (has_type (update i0 (exist (fun x : ty => wf_ty x) T h) (update i0 (exist wf_ty Ti h1) ctx0)) body T).
    eapply ctx_eq_rewrite; eauto.
    eapply ctx_eq_rewrite; eauto.
    eapply ht_fix; eauto.
    eapply IHh; eauto. eapply CtxEq_byCtxEq.
    eapply eqSymm. eapply eqTrans. eapply eqPermute. eauto.
    intro. subst; try contradiction. eapply eqUpdate. eapply eqSymm; eauto.
Qed.



Theorem preservation:
    forall t t' T,
        has_type empty t T ->
        step t t' ->
        has_type empty t' T.


    intros t t' T h.
    remember empty as ctx.
    glize t' Heqctx 0.
    induction h;intros; subst; eauto; try discriminate;
    repeat (
        match goal with
        | hh : ?x = ?x -> _ |- _ => poses' (hh eq_refl); clear hh
        end
    );
    try (
        match goal with
        | h : step _ _ |- _ => 
            inversion h; subst; eauto;
            try (
                match goal with
                | HH : _ -> _ |- _=> 
                    forwards*: HH; destructALL; eexists;split; subst;  eauto; fail
                end
            )
        end
    );
    construct_wf_ty_and_orcd;
    eli_dupli_wf_ty_orcd;
    try (
        match goal with
        | h0 : forall _, step ?x _ -> _, h1 : step ?x _ |- _ =>
            forwards*: h0; subst; eauto; destructALL;  eauto
        end
    );
    construct_wf_ty_and_orcd;
    construct_orcd;
    eli_dupli_wf_ty_orcd;
    eauto;
    
    try (eapply subst_type_preserve; eauto; fail).

    (* case tfun *)

    forwards*: (value_has_type_inver_tfun1 ((tfun i T h body)));
    destructALL; subst; try discriminate. inversion H2; subst; eauto.
    forwards*: value_has_type_inver_tfun3. eauto.
    eapply subst_type_preserve; eauto.
    destruct (eq_ty_dec T0 x0); subst; eauto.
    eapply ht_subty; eauto.
    eapply has_type_orfu; eauto.

    (* case tfield *)
    forwards*: (value_has_type_inver_tfield0');
    destructALL; subst; eauto. inversion H2; subst; eauto.
    assert (has_type empty t1 T); eauto. 
        destruct (eq_ty_dec T x); subst; eauto.
        eapply ht_subty; eauto. eapply has_type_orfu; eauto.
    forwards*: record_has_type_has_field_with_type; destructALL; eauto.
    forwards*: has_type_orfu.
    forwards*: rcd_field_ty'_orfu_is_orfu.
    assert (orfu (TFun x x0)); eauto; try eapply has_type_orfu; eauto.
    inversion H17; subst; eauto.
    assert (has_type empty t' x1); eauto.
        destruct (eq_ty_dec x2 x1); subst; eauto.
    destruct (eq_ty_dec x1 x0); subst; eauto.

    (* case text*)
    destruct (eintp i O f x h0 h3).
    forwards* : value_has_type_inver_text0. cbn in *. inversion H2; subst; eauto.
    

    (* case tleft *)
    


    



