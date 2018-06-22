Add LoadPath "src".
Require Import Maps.
Require Import Context.

Import Context.Context.
Require Import Coq.Lists.List.
Require Import LibTactics.

Module SmallCore.

Definition  tyId := id.
Definition  tyBase := id.
Definition  fieldId := id.


Inductive ty : Set :=
    | TFun : ty -> ty -> ty
    | TSum : ty -> ty -> ty
    | TVar : tyId -> ty
    | TNone : ty
    (* 
        TVar represents primitive type variable
    *)
    | TRcons : fieldId -> ty -> ty -> ty.

Hint Constructors ty.

Inductive only_rcd : ty -> Prop :=
    | orcdBase : only_rcd TNone
    | orcdRcd : forall i T T',
        only_rcd T' ->
        only_rcd (TRcons i T T').

Hint Constructors only_rcd.

Inductive wf_ty : ty -> Prop :=
    | wfFun : forall i o, wf_ty i -> wf_ty o -> wf_ty (TFun i o)
    | wfSum : forall l r, wf_ty l -> wf_ty r -> wf_ty (TSum l r)
    | wfNone :  wf_ty TNone
    | wfRcd : forall i T T',
        wf_ty T ->
        wf_ty T' ->
        only_rcd T' ->
        wf_ty (TRcons i T T')
    | wfVar : forall i,
        wf_ty (TVar i).

    Hint Constructors wf_ty.

Inductive tm : Set :=
    | tvar : id -> tm
    | tnone : tm
(* 
    | tbox : tm -> tyId -> tm
    | tunbox : tm -> tm
    (* Primitivize and unprimitivize, key to Recursive type *)
     *)


    | tfun : id -> ty -> tm -> tm 
    | tapp : tm -> tm -> tm
    | tlet : id -> ty -> tm -> tm -> tm
    | tfixApp : id -> ty -> tm -> tm -> tm
    | tleft : tm -> ty -> tm 
    | tright : ty -> tm -> tm
    | tcase : tm -> tm -> tm -> tm 
        (*
            tcase (\ x -> x) (\ y -> y)
        *)
        (*
            type information is 
            lexical scoped
        *)
    | tletrcd : id -> tyId -> ty -> list (id* ty) -> tm -> tm
        (*
            letRcd (contructorA TypeA ParentType ((a, Int) (b, Int))
            in ... 
                 TypeA <: ParentType
            then constructorA :: Int -> Int -> TypeA
                 TypeA.a :: TypeA -> Int

            letRcd (i J (Nat Nat))
            then i :: Int -> Int -> J
        *)
    | tfield : ty -> id -> tm.

Fixpoint rcd_field_ty' (rcd: ty) (field : id) : option ty :=
    match rcd with
    | TRcons i head tail => if (eq_id_dec i field) then Some head else rcd_field_ty' tail field
    | _ => None
    end.

Definition rcd_field_ty (rcd: ty) (h : only_rcd rcd) (h' : wf_ty rcd) (field : id) : option ty :=
    rcd_field_ty' rcd field.    


Definition subty_prop_weak (x y : ty) := 
    forall T fid,
        rcd_field_ty' y fid = Some T ->
        exists T', rcd_field_ty' x fid = Some T'.


Inductive subty  : ty -> ty -> Prop :=
    | subFun : forall x x' y y',
                subty x' x ->
                subty y y' ->
                subty (TFun x y) (TFun x' y')
    | subSum : forall x x' y y',
                subty x x' ->
                subty y y' ->
                subty (TSum x y) (TSum x' y')
    | subRcdd : forall i p1 p2 q1 q2,
                wf_ty q1 ->
                only_rcd q1 ->
                wf_ty q2 ->
                only_rcd q2 ->
                subty p1 p2 ->
                subty q1 q2 ->
                subty (TRcons i p1 q1) (TRcons i p2 q2)
    | subRcdw : forall i p q1 q2,
                wf_ty q1 ->
                only_rcd q1 ->
                wf_ty q2 ->
                only_rcd q2 ->
                subty q1 q2 ->
                wf_ty p ->
                subty (TRcons i p q1) q2
    | subRefl : forall t,
                wf_ty t ->
                subty t t
    | subTrans : forall t0 t1 t2,
                subty t0 t1 ->
                subty t1 t2 ->
                subty t0 t2.
    
Hint Constructors subty.

Theorem subty_defined_well_weak :
    forall x y,
        subty x y ->
        subty_prop_weak x y.

    intros x y h. unfold subty_prop_weak.
    induction h; intros; subst; eauto;
    simpl in *;

    try(destruct (eq_id_dec i fid); subst; eauto; fail).
    destruct (IHh2 _ _ H); eauto.
Qed.

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
    forall x y,
        subty x y ->
        wf_ty x /\ wf_ty y.
    
intros x y h;
induction h; destructALL; subst; split; eauto.
Qed.

End SmallCore.

