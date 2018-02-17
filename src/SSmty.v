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



Inductive subty  : ty -> ty -> Set :=
| stfun : forall x x' y y',
            subty x x' ->
            subty y' y ->
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




End SSmty.
