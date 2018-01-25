Add LoadPath "src".
Require Import Maps.
Require Import Context.
Require Import Coq.ZArith.Int.

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
| ht_app : forall ctx t0 t1 T0 T1,
    has_type ctx t0 (TFun T0 T1) ->
    has_type ctx t1 T0 ->
    has_type ctx (tapp t0 t1) T1
| ht_let : forall ctx i T bind body T' (h: wf_ty T),
    has_type (update i (exist _ T h) ctx) bind T ->
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
            try apply (P (h0 X1 eq_refl i) (h1 X2 eq_refl i) (h2 X3 eq_refl i) (h3 X4 eq_refl i) (h4 X5 eq_refl i) (h5 X6 eq_refl i)); idtac 1
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
            try apply (P (h0 X1 eq_refl i) (h1 X2 eq_refl i) (h2 X3 eq_refl i) (h3 X4 eq_refl i) (h4 X5 eq_refl i)); idtac 2
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
            try apply (P (h0 X1 eq_refl i) (h1 X2 eq_refl i) (h2 X3 eq_refl i) (h3 X4 eq_refl i)); idtac 3
        | _ => idtac
        end
    | E : eq _ (?P ?X1 ?X2 ?X3) |- _ =>
        match goal with
        | 
        i: id, 
        h0 : forall x:_, eq _ ?X1 -> _, 
        h1 : forall x:_, eq _ ?X2 -> _, 
        h2 : forall x:_, eq _ ?X3 -> _|- _=> 
            try apply (P (h0 X1 eq_refl i) (h1 X2 eq_refl i) (h2 X3 eq_refl i)); idtac 4
        | _ => idtac 
        end
    | E : eq _ (?P ?X1 ?X2) |- _ =>
        match goal with
        | 
        i: id, 
        h0 : forall x:_, eq _ ?X1 -> _, 
        h1 : forall x:_, eq _ ?X2 -> _|- _=> 
            try apply (P (h0 X1 eq_refl i) (h1 X2 eq_refl i)); idtac 5
        | _ => idtac
        end
    | E : eq _ (?P ?X1) |- _ =>
        match goal with
        |
        i: id, 
        h0 : forall x:_, eq _ ?X1 -> _|- _=> 
            try apply (P (h0 X1 eq_refl i)); idtac 6
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
            step (tngt (tint n1) (tint n2)) (if ltb n2 n1 then ttrue else tfalse)
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
            step (tnlt (tint n1) (tint n2)) (if ltb n1 n2 then ttrue else tfalse)
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
            step (tneq (tint n1) (tint n2)) (if eqb n1 n2 then ttrue else tfalse)
    | stceq0 :
        forall t0 t0' t1,
            step t0 t0' ->
            step (tneq t0 t1) (tneq t0' t1)
    | stceq1 :
        forall t0 t1 t1',
            value t0 ->
            step t1 t1' ->
            step (tneq t0 t1) (tneq t0 t1')
    | stceq2 :
        forall n1 n2,
            step (tneq (tchr n1) (tchr n2)) (if eqb n1 n2 then ttrue else tfalse)
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
            step (tfun i T h body) x ->


End SSmtyP.