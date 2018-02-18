Add LoadPath "src".
Require Import Maps.
Require Import Context.
Require Import Coq.ZArith.ZArith.
Import Context.Context.
Require Import Coq.Lists.List.

Module SSmty.

Definition tyid := id.

(* Structual Typing *)

Inductive ty : Set :=
    | TNat : ty 
    | TChr : ty
    | TFun : ty -> ty -> ty
    | TBool : ty
    | TSum : ty -> ty -> ty
    | TNone : ty
    (* There won't be any variable. *)
    | TRcons : id -> ty -> ty -> ty.

    Hint Constructors ty.

Inductive only_rcd : ty -> Set :=
    | odNone : only_rcd TNone
    | odRcd : forall i T T',
        only_rcd T' ->
        only_rcd (TRcons i T T').

    Hint Constructors only_rcd.

Inductive wf_ty : ty -> Prop :=
    | wfNat : wf_ty TNat
    | wfBool : wf_ty TBool
    | wfChr : wf_ty TChr
    | wfFun : forall i o, wf_ty i -> wf_ty o -> wf_ty (TFun i o)
    | wfSum : forall l r, wf_ty l -> wf_ty r -> wf_ty (TSum l r)
    | wfNone : wf_ty TNone
    | wfRcd : forall i T T',
        wf_ty T ->
        wf_ty T' ->
        only_rcd T' ->
        wf_ty (TRcons i T T').

    Hint Constructors wf_ty.
    

Inductive tm : Set :=
    | tnone : tm 
    | trcons : id -> tm -> tm -> tm
    | tif: tm -> tm -> tm -> tm 
    | tvar : id -> tm
    | tint : Z -> tm
    | tsuc : tm -> tm 
    | tdec : tm -> tm
    | tngt : tm -> tm -> tm 
    | tnlt : tm -> tm -> tm 
    | tneq : tm -> tm -> tm
    | tchr : nat -> tm 
    | tceq : tm -> tm -> tm 
    | tfun : id -> forall (T: ty),  wf_ty T -> tm -> tm 
    | tapp : tm -> tm -> tm
    | tlet : id -> forall (T: ty),  wf_ty T -> tm -> tm -> tm
    (*
        it's acutally normal let.
    *)
    | tfix : id -> forall (T: ty),  wf_ty T -> tm -> tm
    | ttrue : tm
    | tfalse : tm 
    | tbeq : tm -> tm -> tm 
    | tleft : tm -> forall (T: ty),  wf_ty T -> tm 
    | tright: forall (T : ty),  wf_ty T -> tm -> tm
    | tcase : tm -> tm -> tm -> tm 
        (*
            tcase (\ x -> x) (\ y -> y)
        *)
        (*
            type information is 
            lexical scoped
        *)
    | tfield : forall (T: ty), only_rcd T ->  wf_ty T -> id -> tm 
        (*
            TypeA.a :: TypeA -> Int
        *)
    | tseq : tm -> tm -> tm.
        (* 
            Maybe one day I will add side effect.
            Then it is useful.
            But it is definitely useful in FFI.
        *)

    Hint Constructors tm.



Inductive subty  : ty -> ty -> Prop :=
| stfun : forall x x' y y',
            subty x' x ->
            subty y y' ->
            subty (TFun x y) (TFun x' y')
| stsum : forall x x' y y',
            subty x x' ->
            subty y y' ->
            subty (TSum x y) (TSum x' y')
| strcdd : forall i p1 p2 q,
            wf_ty q ->
            only_rcd q ->
            subty p1 p2 ->
            subty (TRcons i p1 q) (TRcons i p2 q)
| strcdw : forall i p q1 q2,
            wf_ty q1 ->
            only_rcd q1 ->
            wf_ty q2 ->
            only_rcd q2 ->
            wf_ty p ->
            subty q1 q2 ->
            subty (TRcons i p q1) q2
| st_refl : forall t,
            wf_ty t ->
            subty t t
| st_trans : forall t0 t1 t2,
            subty t0 t1 ->
            subty t1 t2 ->
            subty t0 t2.

    Hint Constructors subty.

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

Theorem subty_wf:
    forall a b,
        subty a b ->
        wf_ty a /\ wf_ty b.
    
    intros.
    induction H; intros; subst;
    try (destructALL; subst; eauto;fail).
Qed.

    
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

Lemma type_not_rec_fun0:
    forall T1 T2,
        T1 <> TFun T1 T2.
    intros T1;
    induction T1; intros;
    try (intro hh;  subst; eauto; inversion hh; subst; eauto; try discriminate; try contradiction; fail).
    intro. inversion H; subst; eauto. eapply IHT1_1; eauto.
Qed.

Lemma type_not_rec_fun1:
    forall T2 T1,
        T2 <> TFun T1 T2.
    intros T2;
    induction T2; intros;
    try (intro hh;  subst; eauto; inversion hh; subst; eauto; try discriminate; try contradiction; fail).
    intro. inversion H; subst; eauto. eapply IHT2_2; eauto.
Qed.

Lemma type_not_rec_sum0:
forall T1 T2,
        T1 <> TSum T1 T2.
    intros T1;
    induction T1; intros;
    try (intro hh;  subst; eauto; inversion hh; subst; eauto; try discriminate; try contradiction; fail).
    intro. inversion H; subst; eauto. eapply IHT1_1; eauto.
Qed.

Lemma type_not_rec_sum1:
    forall T2 T1,
        T2 <> TSum T1 T2.
    intros T2;
    induction T2; intros;
    try (intro hh;  subst; eauto; inversion hh; subst; eauto; try discriminate; try contradiction; fail).
    intro. inversion H; subst; eauto. eapply IHT2_2; eauto.
Qed.

Lemma type_not_rec_rcons0:
forall T1 T2 i,
        T1 <> TRcons i T1 T2.
    intros T1;
    induction T1; intros;
    try (intro hh;  subst; eauto; inversion hh; subst; eauto; try discriminate; try contradiction; fail).
    intro. inversion H; subst; eauto. eapply IHT1_1; eauto.
Qed.

Lemma type_not_rec_rcons1:
    forall T2 T1 i,
        T2 <> TRcons i T1 T2.
    intros T2;
    induction T2; intros;
    try (intro hh;  subst; eauto; inversion hh; subst; eauto; try discriminate; try contradiction; fail).
    intro. inversion H; subst; eauto. eapply IHT2_2; eauto.
Qed.


Theorem eq_ty_dec:
    forall (T T' : ty),
        {T = T'} + {T <> T'}.
    intros T;
    induction T;
    intros T';
    induction T'; subst; eauto;
    try(
    repeat (
        match goal with
        | h0 : {_}+{_} |- _ => destruct h0; subst; eauto
        end
    );
    try
    (left; eauto; fail);
    try
    (right; intro CCC; inversion CCC; eauto; fail);
    fail
    ).

    (* case TFun *)
    destruct IHT'1; destruct IHT'2; subst; eauto;
    try (
        right; 
        try eapply type_not_rec_fun0;
        try eapply type_not_rec_fun1;
        fail
    ).
    destruct (IHT1 T'1); destruct (IHT2 T'2);
    subst; eauto;
    try (left; eauto; fail);
    try (right; intro hhhh; inversion hhhh; subst; eauto).

    (* case TSum*)
    destruct IHT'1; destruct IHT'2; subst; eauto;
    try (
        right; 
        try eapply type_not_rec_sum0;
        try eapply type_not_rec_sum1;
        fail
    ).
    destruct (IHT1 T'1); destruct (IHT2 T'2);
    subst; eauto;
    try (left; eauto; fail);
    try (right; intro hhhh; inversion hhhh; subst; eauto).

    (* case TRcd *)
    destruct IHT'1; destruct IHT'2; subst; eauto;
    try (
        right; 
        try eapply type_not_rec_rcons0;
        try eapply type_not_rec_rcons1;
        fail
    ).
    destruct (IHT1 T'1); destruct (IHT2 T'2); destruct (eq_id_dec i i0);
    subst; eauto;
    try (left; eauto; fail);
    try (right; intro hhhh; inversion hhhh; subst; eauto; fail).
Qed.

Definition eq_ty_bool (T1 T2: ty) : bool.
    destruct (eq_ty_dec T1 T2).
    apply true.
    apply false.
Defined.


(*Fixpoint subty_dec_alg (T1 T2 : ty) {struct T1}: bool :=
    orb (eq_ty_bool T1 T2)
        (
            match T1, T2 with
            | (TFun x0 y0), (TFun x1 y1) =>
            andb (subty_dec_alg x1 x0) (subty_dec_alg y0 y1)
            | (TSum x0 y0), (TSum x1 y1) => 
            andb (subty_dec_alg x0 x1) (subty_dec_alg y0 y1)
            | TRcons _ _ _, TNone => true
            | (TRcons _ x0 y0), (TRcons i x1 y1) => 
            orb (andb (subty_dec_alg x0 x1) (subty_dec_alg y0 y1))
                (subty_dec_alg y0 (TRcons i x1 y1))
            | _, _ => false
            end
).*)

Lemma subty_onlyrefl_tnat1:
    forall T,
        subty T TNat ->
        T = TNat.
    intros T h1.
    remember TNat as Y.
    generalize dependent HeqY.
    induction h1; intros; subst; eauto;
    try discriminate; try contradiction.
    inversion H2.
    rewrite IHh1_1; eauto.
Qed.

Lemma subty_onlyrefl_tnat0:
    forall T,
        subty TNat T ->
        T = TNat.
    intros T h1.
    remember TNat as Y.
    generalize dependent HeqY.
    induction h1; intros; subst; eauto;
    try discriminate; try contradiction.
    rewrite IHh1_2; eauto.
Qed.

Lemma subty_onlyrefl_tchr1:
    forall T,
        subty T TChr ->
        T = TChr.
    intros T h1.
    remember TChr as Y.
    generalize dependent HeqY.
    induction h1; intros; subst; eauto;
    try discriminate; try contradiction.
    inversion H2.
    rewrite IHh1_1; eauto.
Qed.

Lemma subty_onlyrefl_tchr0:
    forall T,
        subty TChr T ->
        T = TChr.
    intros T h1.
    remember TChr as Y.
    generalize dependent HeqY.
    induction h1; intros; subst; eauto;
    try discriminate; try contradiction.
    rewrite IHh1_2; eauto.
Qed.

Lemma subty_onlyrefl_tbool1:
    forall T,
        subty T TBool ->
        T = TBool.
    intros T h1.
    remember TBool as Y.
    generalize dependent HeqY.
    induction h1; intros; subst; eauto;
    try discriminate; try contradiction.
    inversion H2.
    rewrite IHh1_1; eauto.
Qed.

Lemma subty_onlyrefl_tbool0:
    forall T,
        subty TBool T ->
        T = TBool.
    intros T h1.
    remember TBool as Y.
    generalize dependent HeqY.
    induction h1; intros; subst; eauto;
    try discriminate; try contradiction.
    rewrite IHh1_2; eauto.
Qed.

Lemma subty_onlyrefl_tnone0:
    forall T,
        subty TNone T ->
        T = TNone.
    intros T h1.
    remember TNone as Y.
    generalize dependent HeqY.
    induction h1; intros; subst; eauto;
    try discriminate; try contradiction.
    rewrite IHh1_2; eauto.
Qed.
        

Lemma subty_extrac_tfun0:
    forall T0 T1 T,
        subty (TFun T0 T1) T ->
        (exists (T0' T1': ty), T = TFun T0' T1').
    intros T0 T1 T h.
    remember (TFun T0 T1) as TT.
    generalize dependent T0. 
    generalize dependent T1.
    induction h; 
    try(
        intros T1 T0 hh;
        subst; inversion hh; subst; eauto; fail
    ).
    intros. exists T0; exists T1; eauto.
    intros.  destruct (IHh1 _ _ HeqTT).
    destruct H; subst. eauto.
Qed.

Lemma subty_extrac_tfun1:
    forall T0 T1 T,
        subty T (TFun T0 T1) ->
        (exists (T0' T1': ty), T = TFun T0' T1').
    intros T0 T1 T h.
    remember (TFun T0 T1) as TT.
    generalize dependent T0. 
    generalize dependent T1.
    induction h; 
    try(
        intros T1 T0 hh;
        subst; inversion hh; subst; eauto; fail
    );
    try (intros; eauto; fail).
    intros; subst. inversion H2.
    intros.  
    destruct (IHh2 _ _ HeqTT).
    destruct H. eauto.
Qed.

Lemma subty_extrac_tsum0:
    forall T0 T1 T,
        subty (TSum T0 T1) T ->
        (exists (T0' T1': ty), T = TSum T0' T1').
    intros T0 T1 T h.
    remember (TSum T0 T1) as TT.
    generalize dependent T0. 
    generalize dependent T1.
    induction h; 
    try(
        intros T1 T0 hh;
        subst; inversion hh; subst; eauto; fail
    ).
    intros. exists T0; exists T1; eauto.
    intros.  destruct (IHh1 _ _ HeqTT).
    destruct H; subst. eauto.
Qed.

Lemma subty_extrac_tsum1:
    forall T0 T1 T,
        subty T (TSum T0 T1) ->
        (exists (T0' T1': ty), T = TSum T0' T1').
    intros T0 T1 T h.
    remember (TSum T0 T1) as TT.
    generalize dependent T0. 
    generalize dependent T1.
    induction h; 
    try(
        intros T1 T0 hh;
        subst; inversion hh; subst; eauto; fail
    );
    try (intros; eauto; fail).
    intros; subst. inversion H2.
    intros.  
    destruct (IHh2 _ _ HeqTT).
    destruct H. eauto.
Qed.



Lemma subty_extra_tfun:
    forall x y x' y',
        subty (TFun x y) (TFun x' y') ->
        subty x' x /\ subty y y'.
    
    intros.
    remember (TFun x y) as T.
    remember (TFun x' y') as T'.
    generalize dependent x.
    generalize dependent y.
    generalize dependent x'.
    generalize dependent y'.
    induction H; intros; subst;
    try discriminate;
    try (split; eauto; fail).
    inversion HeqT';
    inversion HeqT; subst. tauto.
    inversion HeqT; inversion H; subst; eauto.
    destruct (subty_extrac_tfun0 _ _ _ H).
    destruct (subty_extrac_tfun1 _ _ _ H0).
    destructALL. subst. inversion H2; subst; eauto.
    destruct (IHsubty1 _ _ eq_refl _ _ eq_refl).
    destruct (IHsubty2 _ _ eq_refl _ _ eq_refl).
    split; eauto.
Qed.

Lemma subty_extra_tsum:
    forall x y x' y',
        subty (TSum x y) (TSum x' y') ->
        subty x x' /\ subty y y'.
    
    intros.
    remember (TSum x y) as T.
    remember (TSum x' y') as T'.
    generalize dependent x.
    generalize dependent y.
    generalize dependent x'.
    generalize dependent y'.
    induction H; intros; subst;
    try discriminate;
    try (split; eauto; fail).
    inversion HeqT';
    inversion HeqT; subst. tauto.
    inversion HeqT; inversion H; subst; eauto.
    destruct (subty_extrac_tsum0 _ _ _ H).
    destruct (subty_extrac_tsum1 _ _ _ H0).
    destructALL. subst. inversion H2; subst; eauto.
    destruct (IHsubty1 _ _ eq_refl _ _ eq_refl).
    destruct (IHsubty2 _ _ eq_refl _ _ eq_refl).
    split; eauto.
Qed.

Ltac general_val_ X u v :=
    match v with
      | 0 => X;(generalize dependent u)
      | _ => general_val_ ltac:(X; generalize dependent u) v
    end.

Ltac glize :=
    general_val_ idtac.

Lemma subty_rcons_none:
    forall i head tail T,
        T = TRcons i head tail ->
        wf_ty T ->
        only_rcd T ->
        subty T TNone.
    intros i head tail T h0 h1 h2.
    glize i head tail h1 0.
    induction h2; subst; eauto.
    intros. inversion h0; subst; eauto; inversion h1; subst; eauto.
    eapply strcdw;eauto.
    destruct h2; eauto.
Qed.

  

Axiom wf_ty_rcons_rcd:
    forall i T1 T2,
        wf_ty (TRcons i T1 T2) ->
        only_rcd T2.
(* I don't know how the fuck this is happening
    I will try to make only_rcd into prop again.
*)

Theorem subty_dec_compl:
    forall T1 T2,
        {subty T1 T2 /\ subty T2 T1} +
        {subty T1 T2 /\ ~subty T2 T1} +
        {~subty T1 T2 /\ subty T2 T1} +
        {~subty T1 T2 /\ ~subty T2 T1}.

    Ltac fst := left; left; left.
    Ltac snd := left; left; right.
    Ltac trd := left; right.
    Ltac fth := right.

    intros T1;
    induction T1;
    intros T2; induction T2;
    try (
        fth; split; intro;
        match goal with
        | h0 : subty TNat _ |- _ =>
            poses' (subty_onlyrefl_tnat0 _ h0); eauto
        | h0 : subty _ TNat |- _ =>
            poses' (subty_onlyrefl_tnat1 _ h0); eauto
        | h0 : subty TChr _ |- _ =>
            poses' (subty_onlyrefl_tchr0 _ h0); eauto
        | h0 : subty _ TChr |- _ =>
            poses' (subty_onlyrefl_tchr1 _ h0); eauto
        | h0 : subty TBool _ |- _ =>
            poses' (subty_onlyrefl_tbool0 _ h0); eauto
        | h0 : subty _ TBool |- _ =>
            poses' (subty_onlyrefl_tbool1 _ h0); eauto
        | h0 : subty TNone _ |- _ =>
            poses' (subty_onlyrefl_tnone0 _ h0); eauto
        | h0 : subty (TFun _ _) _ |- _ =>
            poses' (subty_extrac_tfun0 _ _ _ h0); destructALL; eauto
        | h0 : subty _ (TFun _ _) |- _ =>
            poses' (subty_extrac_tfun1 _ _ _ h0); destructALL; eauto
        | h0 : subty (TSum _ _) _ |- _ =>
            poses' (subty_extrac_tsum0 _ _ _ h0); destructALL; eauto
        | h0 : subty _ (TSum _ _) |- _ =>
            poses' (subty_extrac_tsum1 _ _ _ h0); destructALL; eauto
        end; try discriminate; fail
    );
    try (
        fst; eauto; fail
    ).
    
    
    Ltac extra_tcombine :=
        repeat (match goal with
        | h0 : subty (TFun _ _) (TFun _ _) |- _ =>
            poses' (subty_extra_tfun _ _ _ _ h0);
            generalize dependent h0;
            destructALL
        | h0 : subty (TSum _ _) (TSum _ _) |- _ =>
            poses' (subty_extra_tsum _ _ _ _ h0);
            generalize dependent h0;
            destructALL
        end); intros.
    (* case tfun *)
    clear IHT2_1. clear IHT2_2.
    poses' (IHT1_1 T2_1);
    poses' (IHT1_2 T2_2);
    destructALL;
    try (fst; split; eauto; fail);
    try (snd; split; eauto; 
        try (intro h0; extra_tcombine; subst; eauto; fail);
        fail);
    try (trd; split; eauto;
        try (intro h0; extra_tcombine; subst; eauto; fail);
        fail);
    try (fth; split; eauto;
        try (intro h0; extra_tcombine; subst; eauto; fail);
        fail).

    (* case tsum *)

    clear IHT2_1. clear IHT2_2.
    poses' (IHT1_1 T2_1);
    poses' (IHT1_2 T2_2);
    destructALL;
    try (fst; split; eauto; fail);
    try (snd; split; eauto; 
        try (intro h0; extra_tcombine; subst; eauto; fail);
        fail);
    try (trd; split; eauto;
        try (intro h0; extra_tcombine; subst; eauto; fail);
        fail);
    try (fth; split; eauto;
        try (intro h0; extra_tcombine; subst; eauto; fail);
        fail).

    (* case TRcons *)
    destruct (wf_ty_dec (TRcons i T2_1 T2_2)).
    trd; eauto. split. intro. poses' (subty_onlyrefl_tnone0 _ H). try discriminate.
    eapply  subty_rcons_none; eauto.
    poses' (wf_ty_rcons_rcd _ _ _ w).
    eauto.
    fth; split; intro; eauto. poses' (subty_onlyrefl_tnone0 _ H). try discriminate.
    destruct (subty_wf _ _ H); eauto.
    destruct (wf_ty_dec (TRcons i T1_1 T1_2)).
    snd; eauto. split. eapply subty_rcons_none; eauto.
    poses' (wf_ty_rcons_rcd _ _ _ w). eauto.
    intro. poses' (subty_onlyrefl_tnone0 _ H). try discriminate.
    fth; split; intro; eauto. destruct (subty_wf _ _ H); eauto.
    poses' (subty_onlyrefl_tnone0 _ H). try discriminate.

    clear IHT2_1. clear IHT2_2.
    poses' (IHT1_1 T2_1);
    poses' (IHT1_2 T2_2);
    poses' (IHT1_2 (TRcons ))
    destructALL;
    try (fst; split; eauto; fail);
    try (snd; split; eauto; 
        try (intro h0; extra_tcombine; subst; eauto; fail);
        fail);
    try (trd; split; eauto;
        try (intro h0; extra_tcombine; subst; eauto; fail);
        fail);
    try (fth; split; eauto;
        try (intro h0; extra_tcombine; subst; eauto; fail);
        fail).
    






End SSmty.
