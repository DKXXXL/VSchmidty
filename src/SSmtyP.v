Add LoadPath "src".
Require Import Maps.
Require Import Context.

Require Import Coq.ZArith.Int.

Import Coq.ZArith.BinInt.



Import Context.Context.
Require Import Coq.Lists.List.
Require Import SSmty.
Require Import LibTactics.

Import SSmty.SSmty.


Module SSmtyP.
(* Structual Typing *)

(*
Fixpoint rcd_cons_ty (rcd : list (id * ty)) (retty : ty) : ty :=
    match rcd with
    | nil => retty
    | (_, h)::t => TFun h (rcd_cons_ty t retty)
    end. 
*)
Ltac general_val_ X u v :=
    match v with
      | 0 => X;(generalize dependent u)
      | _ => general_val_ ltac:(X; generalize dependent u) v
    end.

Ltac glize :=
    general_val_ idtac.

    Ltac destructALL :=
    repeat (
        match goal with
        | h0: _ \/ _ |- _ => destruct h0
        | h0: _ /\ _ |- _ => destruct h0
        | h0: exists _, _ |- _ => destruct h0
        end
    ).


Definition rcd_field_ty (rcd: ty) (h : only_rcd rcd) (h' : wf_ty rcd) (field : id) : option ty.
remember rcd as r.
generalize dependent h'. generalize dependent field. generalize dependent Heqr. generalize dependent rcd.
induction h; intros. apply None.
destruct (eq_id_dec i field) eqn:h2.
apply (Some T).
apply (IHh T' eq_refl field).
inversion h'; subst; eauto.
Defined.

Theorem rcd_field_ty_well_formed:
    forall rcd h h' i T,
        rcd_field_ty rcd h h' i = Some T->
        wf_ty T.
    intros rcd h.
    induction h; intros; eauto.
    inversion H.
    cbn in H. destruct (eq_id_dec i i0); subst; eauto.
    inversion H; subst; eauto.
    inversion h'; subst; eauto.
Qed.

Theorem rcd_field_ty_not_TNone:
    forall rcd h h' i T,
        rcd_field_ty rcd h h' i = Some T ->
        rcd <> TNone.
    intros rcd h. induction h; intros; intro; subst; eauto.
    inversion H; subst; eauto.
    inversion H0.
Qed.

Theorem subty_wf:
    forall a b,
        subty a b ->
        wf_ty a /\ wf_ty b.
    
    intros.
    induction H; intros; subst;
    try (destructALL; subst; eauto;fail).
Qed.


Lemma subty_rcd:
    forall a b,
        only_rcd b ->
        subty a b ->
        only_rcd a.
    
    intros a b h0 h2.
    induction h2; subst; eauto; intros;
    try match goal with
    | h0 : only_rcd (_ _) |- _ => inversion h0; subst; eauto; fail
    end.
Qed.

Lemma subty_none_a_a__none:
    forall a,
        subty TNone a ->
        a = TNone.
    
        intros. 
        remember TNone as a'. glize Heqa' 0.
        induction H; subst; eauto; intros; try discriminate.
        subst. poses' (IHsubty1 eq_refl); subst. eapply (IHsubty2). eauto.
Qed.


Lemma subty_rcd_not_none:
    forall a b,
        only_rcd b ->
        b <> TNone ->
        subty a b ->
        a <> TNone.

    intros; 
    assert (only_rcd a).
    eapply (subty_rcd a b H H1).
    intro; subst.
    poses' (subty_none_a_a__none _ H1).
    destruct (H0 H3).
Qed.


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
| ht_if : 
    forall ctx crit tb fb T,
    has_type ctx crit TBool ->
    has_type ctx tb T ->
    has_type ctx fb T ->
    has_type ctx (tif crit tb fb) T
| ht_var: forall ctx T i (h: wf_ty T),
    byContext ctx i = Some (exist _ T h) ->
    has_type ctx (tvar i) T
| ht_int : forall ctx n,
    has_type ctx (tint n) TNat
| ht_suc : forall ctx t,
    has_type ctx t TNat ->
    has_type ctx (tsuc t) TNat
| ht_dec : forall ctx t,
    has_type ctx t TNat ->
    has_type ctx (tdec t) TNat
| ht_ngt : forall ctx t0 t1,
    has_type ctx t0 TNat ->
    has_type ctx t1 TNat ->
    has_type ctx (tngt t0 t1) TBool
| ht_nlt : forall ctx t0 t1,
    has_type ctx t0 TNat ->
    has_type ctx t1 TNat ->
    has_type ctx (tnlt t0 t1) TBool
| ht_neq : forall ctx t0 t1,
    has_type ctx t0 TNat ->
    has_type ctx t1 TNat ->
    has_type ctx (tneq t0 t1) TBool

| ht_chr : forall ctx n,
    has_type ctx (tchr n) TChr
| ht_ceq : forall ctx t0 t1,
    has_type ctx t0 TChr ->
    has_type ctx t1 TChr ->
    has_type ctx (tceq t0 t1) TBool
| ht_fun : forall ctx i T body TO (h: wf_ty T),
    has_type (update i (exist _ T h) ctx) body TO ->
    has_type ctx (tfun i T h body) (TFun T TO)
| ht_app : forall ctx t0 t1 T0' T0 T1,
    has_type ctx t0 (TFun T0 T1) ->
    has_type ctx t1 T0' ->
    subty T0' T0 ->
    has_type ctx (tapp t0 t1) T1
| ht_let : forall ctx i T bind body T' (h: wf_ty T),
    has_type ctx bind T ->
    has_type (update i (exist _ T h) ctx) body T' ->
    has_type ctx (tlet i T h bind body) T'
| ht_fix : forall ctx i body T (h:wf_ty T),
    has_type (update i (exist _ T h) ctx) body T ->
    has_type ctx (tfix i T h body) T
| ht_true : forall ctx,
    has_type ctx ttrue TBool
| ht_false : forall ctx,
    has_type ctx tfalse TBool
| ht_beq : forall ctx t0 t1,
    has_type ctx t0 TBool ->
    has_type ctx t1 TBool ->
    has_type ctx (tbeq t0 t1) TBool
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
| ht_seq : forall ctx t0 t1 T0 T1,
    has_type ctx t0 T0 ->
    has_type ctx t1 T1 ->
    has_type ctx (tseq t0 t1) T1.

Hint Constructors has_type.

Theorem has_type_well_formed:
    forall ctx t T,
        has_type ctx t T ->
        wf_ty T.
    intros t T ctx h.
    
    induction h; try (intros; subst; eauto 10; fail); intros; subst.
    inversion IHh1; subst; eauto.
    inversion IHh3; subst; eauto.
    poses' (rcd_field_ty_well_formed _ _ _ _ _ H).
    eauto.
Qed.

Inductive value : tm -> Prop :=
    | vNone : value tnone
    | vRcons : forall i t0 t1,
                value t0 ->
                value t1 ->
                value (trcons i t0 t1)
    | vInt : forall n,
                value (tint n)
    | vfun : forall i T wft body,
                value (tfun i T wft body)
    | vChr : forall k,
                value (tchr k)
    | vtrue : value ttrue
    | vfalse : value tfalse
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
Definition subst : id -> tm -> tm -> tm.
intros i rep org. remember org as org'.
generalize dependent i. generalize dependent org'. 
induction org; intros;
    match goal with
    | E : eq _ (?P ?X1 ?X2 ?X3 ?X4 ?X5 ?X6) |- _ =>
        match goal with
        | 
        i: id, 
        h0 : forall x:_, eq _ ?X1 -> _, 
        h1 : forall x:_, eq _ ?X2 -> _, 
        h2 : forall x:_, eq _ ?X3 -> _,
        h3 : forall x:_, eq _ ?X4 -> _, 
        h4 : forall x:_, eq _ ?X5 -> _,
        h5 : forall x:_, eq _ ?X6 -> _  |- _=> 
            try apply (P (h0 X1 eq_refl i) (h1 X2 eq_refl i) (h2 X3 eq_refl i) (h3 X4 eq_refl i) (h4 X5 eq_refl i) (h5 X6 eq_refl i))
        | _ => idtac
        end
    | E : eq _ (?P ?X1 ?X2 ?X3 ?X4 ?X5) |- _ =>
        match goal with
        | 
        i: id, 
        h0 : forall x:_, eq _ ?X1 -> _, 
        h1 : forall x:_, eq _ ?X2 -> _, 
        h2 : forall x:_, eq _ ?X3 -> _,
        h3 : forall x:_, eq _ ?X4 -> _, 
        h4 : forall x:_, eq _ ?X5 -> _  |- _=> 
            try apply (P (h0 X1 eq_refl i) (h1 X2 eq_refl i) (h2 X3 eq_refl i) (h3 X4 eq_refl i) (h4 X5 eq_refl i))
        | _ => idtac
        end
    | E : eq _ (?P ?X1 ?X2 ?X3 ?X4) |- _ =>
        match goal with
        | 
        i: id, 
        h0 : forall x:_, eq _ ?X1 -> _, 
        h1 : forall x:_, eq _ ?X2 -> _, 
        h2 : forall x:_, eq _ ?X3 -> _,
        h3 : forall x:_, eq _ ?X4 -> _|- _=> 
            try apply (P (h0 X1 eq_refl i) (h1 X2 eq_refl i) (h2 X3 eq_refl i) (h3 X4 eq_refl i))
        | _ => idtac
        end
    | E : eq _ (?P ?X1 ?X2 ?X3) |- _ =>
        match goal with
        | 
        i: id, 
        h0 : forall x:_, eq _ ?X1 -> _, 
        h1 : forall x:_, eq _ ?X2 -> _, 
        h2 : forall x:_, eq _ ?X3 -> _|- _=> 
            try apply (P (h0 X1 eq_refl i) (h1 X2 eq_refl i) (h2 X3 eq_refl i))
        | _ => idtac 
        end
    | E : eq _ (?P ?X1 ?X2) |- _ =>
        match goal with
        | 
        i: id, 
        h0 : forall x:_, eq _ ?X1 -> _, 
        h1 : forall x:_, eq _ ?X2 -> _|- _=> 
            try apply (P (h0 X1 eq_refl i) (h1 X2 eq_refl i))
        | _ => idtac
        end
    | E : eq _ (?P ?X1) |- _ =>
        match goal with
        |
        i: id, 
        h0 : forall x:_, eq _ ?X1 -> _|- _=> 
            try apply (P (h0 X1 eq_refl i))
        | _ => idtac
        end
    | E: eq _ (?P) |- _ =>
        apply org'
    | _  => idtac
    end.

    (* trcons *)
    apply (trcons i (IHorg1 _ eq_refl i0) (IHorg2 _ eq_refl i0)).
    (* tvar *)
    destruct (eq_id_dec i i0). 
    apply rep.
    apply org'.
    (* tint *)
    apply org'.
    (* tchr *)
    apply org'.
    (* tfun *)
    destruct (eq_id_dec i i0).
    apply org'.
    apply (tfun i T w (IHorg _ eq_refl i0)).
    (* tlet *)
    destruct (eq_id_dec i i0).
    apply (tlet i T w (IHorg1 _ eq_refl i0) org2).
    apply (tlet i T w (IHorg1 _ eq_refl i0) (IHorg2 _ eq_refl i0)).
    (* tfix(app) *)
    destruct (eq_id_dec i i0).
    apply org'.
    apply (tfix i T w (IHorg _ eq_refl i0)).
    (* tleft *)
    apply (tleft (IHorg _ eq_refl i) T w).
    (* tright *)
    apply (tright T w (IHorg _ eq_refl i)).
    (* tfield *)
    apply org'.
Defined.


Open Scope Int_scope.
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
    | stif0 :
        forall t0 t0' t1 t2, 
            step t0 t0' ->
            step (tif t0 t1 t2) (tif t0' t1 t2)
    | stif1 :
        forall t1 t2,
            step (tif ttrue t1 t2) t1
    | stif2 :
        forall t1 t2,
            step (tif tfalse t1 t2) t2
    | stsuc0 :
        forall t0 t0',
            step t0 t0' ->
            step (tsuc t0) (tsuc t0')
    | stsuc1 :
        forall n0,
            step (tsuc (tint n0)) (tint (n0 + 1))
    | stdec0 :
        forall t0 t0',
            step t0 t0' ->
            step (tdec t0) (tdec t0')
    | stdec1 :
        forall n0,
            step (tdec (tint n0)) (tint (n0 - 1))
    | stngt0 :
        forall t0 t0' t1,
            step t0 t0' ->
            step (tngt t0 t1) (tngt t0' t1)
    | stngt1 :
        forall t0 t1 t1',
            value t0 ->
            step t1 t1' ->
            step (tngt t0 t1) (tngt t0 t1')
    | stngt2 :
        forall n1 n2,
            step (tngt (tint n1) (tint n2)) (if Z.ltb n2 n1 then ttrue else tfalse)
    | stnlt0 :
        forall t0 t0' t1,
            step t0 t0' ->
            step (tnlt t0 t1) (tnlt t0' t1)
    | stnlt1 :
        forall t0 t1 t1',
            value t0 ->
            step t1 t1' ->
            step (tnlt t0 t1) (tnlt t0 t1')
    | stnlt2 :
        forall n1 n2,
            step (tnlt (tint n1) (tint n2)) (if Z.ltb n1 n2 then ttrue else tfalse)
    | stneq0 :
        forall t0 t0' t1,
            step t0 t0' ->
            step (tneq t0 t1) (tneq t0' t1)
    | stneq1 :
        forall t0 t1 t1',
            value t0 ->
            step t1 t1' ->
            step (tneq t0 t1) (tneq t0 t1')
    | stneq2 :
        forall n1 n2,
            step (tneq (tint n1) (tint n2)) (if Z.eqb n1 n2 then ttrue else tfalse)
    | stceq0 :
        forall t0 t0' t1,
            step t0 t0' ->
            step (tceq t0 t1) (tceq t0' t1)
    | stceq1 :
        forall t0 t1 t1',
            value t0 ->
            step t1 t1' ->
            step (tceq t0 t1) (tceq t0 t1')
    | stceq2 :
        forall n1 n2,
            step (tceq (tchr n1) (tchr n2)) (if Nat.eqb n1 n2 then ttrue else tfalse)
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
    | stfix :
        forall i T w fixbody,
            step (tfix i T w fixbody) (subst i (tfix i T w fixbody) fixbody)
    | stbeq0 :
        forall a a' b,
            step a a' ->
            step (tbeq a b) (tbeq a' b)
    | stbeq1 :
        forall a b b',
            value a ->
            step b b' ->
            step (tbeq a b) (tbeq a b')
    | stbeq2:
        forall x,
            value x ->
            step (tbeq x x) ttrue
    | stbeq3:
        forall x y,
            value x ->
            value y ->
            x <> y ->
            step (tbeq x y) tfalse
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
            step (tapp (tfield T orcd w i) (trcons i head tail)) head
    | stseq0 :
        forall A A' B,
            step A A' ->
            step (tseq A B) (tseq A' B)
    | stseq1 :
        forall A B,
            value A ->
            step (tseq A B) B.

    Hint Constructors step.

Axiom wf_ty_indistinct:
    forall T (t1 t2: wf_ty T),
        t1 = t2.

Axiom orcd_indistinct:
    forall T (t1 t2: only_rcd T),
        t1 = t2.



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
    (poses' vNone;
    poses' vInt;
    poses' vtrue;
    poses' vfalse;
    try 
    match goal with
        | h0 : step (tchr ?k) _ |- _ => poses' (vChr k)
    end;
    try
    match goal with
        | h0 : step (tint ?k) _ |- _ => poses' (vInt k)
    end;
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
    ).

    (* tlet, wf_ty difference *)
    erewrite (wf_ty_indistinct T w w1); eauto.
    (* tfix, wf_ty difference *)
    erewrite (wf_ty_indistinct T w w1); eauto.

    (* tbeq, contradiction *)
    (* tleft, wf_ty difference *)
    erewrite (wf_ty_indistinct w R R1); eauto.
    (* tright, wf_ty difference *)
    erewrite (wf_ty_indistinct w L L1); eauto.

(*
    (* tcase , wf_ty orcd difference*)
    erewrite (wf_ty_indistinct LT w0 w5); eauto.

    (* tcase , wf_ty orcd difference*)
    erewrite (wf_ty_indistinct RT w1 w5); eauto.*)
    (*tfield, wf_ty orcd difference*)
    erewrite (orcd_indistinct T orcd orcd1); eauto.
    erewrite (wf_ty_indistinct T w w1); eauto.
Qed.



Lemma ext_type_tnat:
    forall t,
        value t ->
        has_type empty t TNat ->
        exists n, t = tint n.

    intros t h0;
    induction h0; intros; subst; eauto; try discriminate;
    try (match goal with
            | H0 : has_type _ _ _ |- _ => inversion H0; subst; eauto
        end
    ).
Qed.
    
Lemma ext_type_tchr:
    forall t,
        value t ->
        has_type empty t TChr ->
        exists n, t = tchr n.

        intros t h0;
    induction h0; intros; subst; eauto; try discriminate;
    try (match goal with
            | H0 : has_type _ _ _ |- _ => inversion H0; subst; eauto
        end
    ).
Qed.

Lemma ext_type_tfun:
    forall t,
        value t ->
        forall iT oT,
        has_type empty t (TFun iT oT) ->
        (exists i T w body, t = tfun i T w body) \/ (exists T o w i, t = tfield T o w i).
        intros t h0;
    induction h0; intros; subst; eauto; try discriminate;
    try (match goal with
            | H0 : has_type _ _ _ |- _ => inversion H0; subst; eauto
        end
    ); [left | right]; eexists; eauto.
Qed.


Lemma ext_type_tbool:
    forall t,
        value t ->
        has_type empty t TBool ->
        t = ttrue \/ t = tfalse.
    
    intros t h0;
    induction h0; intros; subst; eauto; try discriminate;
    try (match goal with
            | H0 : has_type _ _ _ |- _ => inversion H0; subst; eauto
        end
    ).
Qed.

Lemma ext_type_tsum:
    forall t,
        value t ->
        forall TL TR,
        has_type empty t (TSum TL TR) ->
        (exists w tl tr, t = tleft tl w tr) \/
        (exists w tl tr, t = tright w tl tr).
        
        intros t h0;
    induction h0; intros; subst; eauto; try discriminate;
    try (match goal with
            | H0 : has_type _ _ _ |- _ => inversion H0; subst; eauto
        end
    ).
Qed.

Lemma ext_type_tnone:
    forall t,
        value t ->
        has_type empty t TNone ->
        t = tnone.
    intros t h0;
    induction h0; intros; subst; eauto; try discriminate;
    try (match goal with
            | H0 : has_type _ _ _ |- _ => inversion H0; subst; eauto
        end
    ).
Qed.

Lemma ext_type_trcd:
    forall t,
        value t ->
        forall T,
        has_type empty t T ->
        T <> TNone ->
        only_rcd T ->
        wf_ty T ->
        exists i th tt, t = trcons i th tt.
    intros t h0;
    induction h0; intros; subst; eauto; try discriminate;
    try (match goal with
            | H0 : has_type _ _ _ |- _ => inversion H0; subst; eauto
        end;
        match goal with
            | h: only_rcd (TFun _ _) |- _ => inversion h; subst; eauto
            | H0 : only_rcd _ |- _ => inversion H0; subst; eauto
        end;
        try discriminate
    ).
    (* Case: TNone*)
    destruct (H0 eq_refl).
Qed.




Theorem progress:
    forall t T,
        has_type empty t T ->
        value t \/ (exists t', step t t').
    intros t T h1.
    remember empty as ctx0.
    glize Heqctx0 0.
    induction h1; intros; subst; eauto; 
    try discriminate;
    try(
    poses' vNone;
    poses' vInt;
    poses' vtrue;
    poses' vfalse;
    try 
    match goal with
        | |- value (tchr ?k) \/ _ => poses' (vChr k)
    end;
    try
    match goal with
        | |- value (tint ?k) \/ _ => poses' (vInt k)
    end;
    try 
    match goal with
        | |- value (tfun ?i ?T ?wft ?body) \/ _ => poses' (vfun i T wft body)
    end;
    try 
    match goal with
        | |- value (tfield ?T ?ort ?wft ?i) \/ _ =>
            poses' (vfield T ort wft i)
    end;
    left; eauto; fail
    );
    repeat (match goal with
    | h0: ?X = ?X -> _ |- _ => poses' (h0 eq_refl); clear h0
    end);
    try (
    assert(ttrue <> tfalse); try (intro; discriminate);eauto;
    assert(tfalse <> ttrue); try (intro; discriminate);eauto;
    right; 
    destructALL;
            (repeat (match goal with
                | h0 : value ?X, h1: has_type empty ?X TNat |- _=> 
                    destruct (ext_type_tnat _ h0 h1); subst; eauto; generalize dependent h0; generalize dependent h1
                | h0 : value ?X, h1: has_type empty ?X TChr |- _=> 
                    destruct (ext_type_tchr _ h0 h1); subst; eauto  ; generalize dependent h0; generalize dependent h1             
                | h0 : value ?X, h1: has_type empty ?X TBool |- _=> 
                    destruct (ext_type_tbool _ h0 h1); subst; eauto; generalize dependent h0; generalize dependent h1
                | h0 : value ?X, h1: has_type empty ?X TSum |- _=> 
                    destruct (ext_type_tsum _ h0 h1); subst; eauto; generalize dependent h0; generalize dependent h1
                | h0 : value ?X, h1: has_type empty ?X TNone |- _=> 
                    destruct (ext_type_tnone _ h0 h1); subst; eauto; generalize dependent h0; generalize dependent h1
                | h0 : value ?X, h1: has_type empty ?X (TFun _ _) |- _=> 
                    destruct (ext_type_tfun _ h0 _ _ h1); destructALL; subst; eauto; generalize dependent h0; generalize dependent h1
                | h0 : value ?X, h1: has_type empty ?X (TSum _ _) |- _=> 
                    destruct (ext_type_tsum _ h0 _ _ h1); destructALL; subst; eauto; generalize dependent h0; generalize dependent h1
            end));intros;
    eexists; eauto; fail
    ).

    (* case: trcons *)
    destructALL;
    match goal with
    | h0 : value ?t0, h1: value ?t1 |- _ => left; eauto
    | |- _ => right; eexists; eauto
    end.

    (* case: tapp*)
    right; 
    destructALL;
            (repeat (match goal with
                 | h0 : value ?X, h1: has_type empty ?X (TFun _ _) |- _=> 
                    destruct (ext_type_tfun _ h0 _ _ h1); destructALL; subst; eauto; generalize dependent h0; generalize dependent h1
                  end));intros;
    try(eexists; eauto; fail).
        (* case: tapp: tfield*)
        inversion h1_1; subst; eauto. 
        poses' (rcd_field_ty_not_TNone _ _ _ _ _ H4).
        poses' (subty_rcd_not_none _ _ x0 H2 H).
        destruct (subty_wf _ _ H).
        poses' (subty_rcd _ _ x0 H).
        poses' (ext_type_trcd _ H1 _ h1_2 H3 H8 H6); destructALL; subst; eauto.
        inversion h1_2; subst; eauto. destruct (eq_id_dec x x2); subst; eauto; try discriminate.
    (* case: tleft*)
    destructALL;
    match goal with
    | h0 : value ?x |- (value (tleft ?x _ _)) \/ _ => left; eauto
    | |- _ => right; eauto
    end.

    (* case : tright*)
    destructALL;
    match goal with
    | h0 : value ?x |- (value (tright _ _ ?x)) \/ _ => left; eauto
    | |- _ => right; eauto
    end.

    (* case : tcase*)
    right; destructALL; eauto.
    poses' (ext_type_tsum _ H _ _ h1_1); destructALL; subst; eauto.
    inversion H; subst; eauto.
    inversion H; subst; eauto.
Qed.


Theorem has_type_unique:
    forall ctx t T0 T1,
        has_type ctx t T0 ->
        has_type ctx t T1 ->
        T0 = T1.

    intros ctx t T0 T1 h0.
    glize T1 0.
    induction h0; intros; subst; eauto;
    try match goal with
    | h0 : has_type _ (_ _) _ |- _ => 
        repeat (
            match goal with
            | h2 : has_type _ (_ _) _ |- _ => inversion h2; try glize h2 0
            end
        ); intros; subst; eauto;
        try(repeat (
            match goal with
            | h1 : forall _:_, _ |- _=> forwards: h1; eauto; try glize h1 0
            end);
        intros ; subst; eauto;fail)
    | h0 : has_type _ _ _ |- _ => inversion h0; subst; eauto; fail
    end.
    (* case : tvar*)
    rewrite H in H3. inversion H3; subst; eauto.
    (* case tfun*)
    rewrite (wf_ty_indistinct _ h2 h) in H5. erewrite IHh0; eauto.
    (* case tapp*)
    forwards:IHh0_1. apply H3. inversion H1; subst; eauto.
    (* case tlet*)
    eapply IHh0_2; eauto. rewrite (wf_ty_indistinct _ h h1). eauto.
    (* case tcase*)
    poses' (IHh0_2 _ H6). inversion H0; subst; eauto.
    (* case tfield*)
    erewrite (wf_ty_indistinct _ h1 h5) in H.
    erewrite (orcd_indistinct _ h0 h4) in H.
    rewrite H in H6. inversion H6; subst; eauto.
Qed.

Inductive free_occur_in : id -> tm -> Prop :=
    | fo_rcons0 : forall i j t0 t1,
                free_occur_in i t0 ->
                free_occur_in i (trcons j t0 t1)
    | fo_rcons1 : forall i j t0 t1,
                free_occur_in i t1 ->
                free_occur_in i (trcons j t0 t1)
    | fo_if0 : forall i t0 t1 t2,
                free_occur_in i t0 ->
                free_occur_in i (tif t0 t1 t2)
    | fo_if1 : forall i t0 t1 t2,
                free_occur_in i t1 ->
                free_occur_in i (tif t0 t1 t2)
    | fo_if2 : forall i t0 t1 t2,
                free_occur_in i t2 ->
                free_occur_in i (tif t0 t1 t2)
    | fo_var : forall i,
                free_occur_in i (tvar i)
    | fo_suc : forall i t0,
                free_occur_in i t0 ->
                free_occur_in i (tsuc t0)
    | fo_dec : forall i t0,
                free_occur_in i t0 ->
                free_occur_in i (tdec t0)
    | fo_ngt0 : forall i t0 t1,
                free_occur_in i t0 ->
                free_occur_in i (tngt t0 t1)
    | fo_ngt1 : forall i t0 t1,
                free_occur_in i t1 ->
                free_occur_in i (tngt t0 t1)
    | fo_nlt0 : forall i t0 t1,
                free_occur_in i t0 ->
                free_occur_in i (tnlt t0 t1)
    | fo_nlt1 : forall i t0 t1,
                free_occur_in i t1 ->
                free_occur_in i (tnlt t0 t1)
    | fo_neq0 : forall i t0 t1,
                free_occur_in i t0 ->
                free_occur_in i (tneq t0 t1)
    | fo_neq1 : forall i t0 t1,
                free_occur_in i t1 ->
                free_occur_in i (tneq t0 t1)
    | fo_ceq0 : forall i t0 t1,
                free_occur_in i t0 ->
                free_occur_in i (tceq t0 t1)
    | fo_ceq1 : forall i t0 t1,
                free_occur_in i t1 ->
                free_occur_in i (tceq t0 t1)
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
    | fo_fix : forall i j T h t0,
                i <> j ->
                free_occur_in i t0 ->
                free_occur_in i (tfix j T h t0)
    | fo_beq0 : forall i t0 t1,
                free_occur_in i t0 ->
                free_occur_in i (tbeq t0 t1)
    | fo_beq1 : forall i t0 t1,
                free_occur_in i t1 ->
                free_occur_in i (tbeq t0 t1)
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
                free_occur_in i (tcase t0 t1 t2)
    | fo_seq0 : forall i t0 t1,
                free_occur_in i t0 ->
                free_occur_in i (tseq t0 t1)
    | fo_seq1 : forall i t0 t1,
                free_occur_in i t1 ->
                free_occur_in i (tseq t0 t1).

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

Hint Unfold relative_ctx_eq.

Lemma ctx_change:
    forall ctx0 ctx1 t T,
    has_type ctx0 t T ->
    relative_ctx_eq t ctx0 ctx1 ->
    has_type ctx1 t T.

    intros ctx0 ctx1 t T h0. unfold relative_ctx_eq.
    induction h0; intros; subst; eauto;
    repeat (
        match goal with
        | h0 : _ -> has_type _ _ _ |- _ => forwards: h0; glize h0 0
        end
    );
    intros;
    eauto.

    (* case tvar *)
    
intros i k t ctx T h0
    

Lemma preservation_on_subst0:
    forall i t T0 w body T1,
        has_type empty t T0 ->
        has_type empty (tfun i T0 w body) (TFun T0 T1) ->
        has_type empty (subst i t body) T1.

        intros i t T0 w body.
        glize i t T0 0.
        induction body; intros; subst; eauto.
        inversion H0; subst; eauto.

        (*remember empty as ctx0.
        remember (tfun i T0 w body) as f.
        remember (TFun T0 T1) as Tf.
        glize i t T0 body Heqctx0 T1 0.
        induction h1; intros; subst; eauto; try discriminate.
        *)



Theorem preservation:
    forall t t' T,
        has_type empty t T ->
        step t t' ->
        has_type empty t' T.

    intros t t' T h0.
    remember empty as ctx0.
    glize t' Heqctx0 0.
    induction h0; intros; subst; eauto;
    (* Eliminate value & step contradiction*)
    (try 
    (poses' vNone;
    poses' vInt;
    poses' vtrue;
    poses' vfalse;
    try 
    match goal with
        | h0 : step (tchr ?k) _ |- _ => poses' (vChr k)
    end;
    try
    match goal with
        | h0 : step (tint ?k) _ |- _ => poses' (vInt k)
    end;
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
    fail));
    (* remove trivial condition in hypothesis of assumption*)
    repeat (
        match goal with
        | h0 : ?x = ?x -> _ |- _=> poses' (h0 eq_refl); clear h0
        end 
    );
    try match goal with
    | h0 : step (_ _) _ |- _ =>
        inversion h0; subst; eauto;
            try (match goal with
            | h1: step ?t0 ?t1, h2: forall _:_, step ?t0 _ -> _ |- _ =>
                forwards: h2; eauto
            end);
            (* ngt, nlt introduce calculation, destruct them*)
            try (match goal with
            | H: step _ (if ?crit then _ else _) |- _ => destruct crit; subst; eauto; fail
            end); fail
    end.
    Focus 4.


Definition  stuck (t : tm) := 
    ~ value t /\ ~ (exists t', step t t').

Inductive multi {T : Type} (r : T -> T -> Prop) : T -> T -> Prop :=
    | mo : forall x, multi r x x
    | ms : forall x y z,
                multi r x y ->
                r y z ->
                multi r x z.
    
Definition mstep := multi step.

Theorem soundness :
    forall t t' T,
        has_type empty t T ->
        mstep t t' ->
        ~ stuck t'.

Abort.

Fixpoint check_type (ctx : Context) (t : tm) : option ty.
Abort.

Theorem check_type_sound:   
    forall t T,
        check_type empty t = Some T ->
        has_type empty t T.
Abort.
Theorem check_type_complete:
    forall t T,
        has_type empty t T ->
        check_type empty t = Some T.
Abort.

Fixpoint rsinterpreter (gas : nat) (i : tm) : tm.
Abort.
(* Doubt them. *)
Theorem rsinterpreter_sound:
    forall t t',
        rsinterpreter 1 t = Some t' ->
        step t t'.
Abort.

Theorem rsinterpreter_complete:
    forall t t',
        step t t' ->
        rsinterpreter 1 t = Some t'.
Abort.
        


End SSmtyP.