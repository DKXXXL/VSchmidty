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
    | TBase : tyBase -> ty
    | TVar : tyId -> ty
    (* 
        TVar is only used for recursive type
    *)
    | TRcons : fieldID -> ty -> ty -> ty
    | TRec : tyId -> ty -> ty.

    Hint Constructors ty.

Inductive only_rcd : ty -> Prop :=
    | orcdBase : forall n, only_rcd (TBase n)
    | orcdRcd : forall i T T',
        only_rcd T' ->
        only_rcd (TRcons i T T').

    Hint Constructors only_rcd.

Inductive wf_ty : ty -> Prop :=
    | wfFun : forall i o, wf_ty i -> wf_ty o -> wf_ty (TFun i o)
    | wfSum : forall l r, wf_ty l -> wf_ty r -> wf_ty (TSum l r)
    | wfBase : forall n, wf_ty (TBase n)
    | wfRcd : forall i T T',
        wf_ty T ->
        wf_ty T' ->
        only_rcd T' ->
        wf_ty (TRcons i T T')
    | wfRec : forall i T,
        wf_ty T ->
        wf_ty (TRec i T)

    Hint Constructors wf_ty.

Inductive tm : Set :=
    | tvar : id -> tm
    | tnone : tyBase -> tm
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
    | tletrcd : id -> tyid -> ty -> list (id* ty) -> tm -> tm
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
    
