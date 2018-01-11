Add LoadPath "src".
Require Import Maps.
Require Import Context.
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

Inductive tm : Set :=
    | tnone : tm 
    | trcons : tm -> tm -> tm
    | tif: tm -> tm -> tm -> tm 
    | tvar : id -> tm
    | tzero : tm
    | tsuc : tm -> tm 
    | tdec : tm -> tm
    | tngt : tm -> tm -> tm 
    | tnlt : tm -> tm -> tm 
    | tneq : tm -> tm -> tm
    | tchr : nat -> tm 
    | tceq : tm -> tm -> tm 
    | tfun : id -> ty -> tm -> tm 
    | tapp : tm -> tm -> tm
    | tlet : id -> ty -> tm -> tm -> tm
    (*
        it's acutally letrec.
    *)
    | ttrue : tm
    | tfalse : tm 
    | tbeq : tm -> tm -> tm 
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
    | tfield : ty -> id -> tm 
        (*
            TypeA.a :: TypeA -> Int
        *)
    | tseq : tm -> tm.




Inductive subty  : ty -> ty -> Prop :=
| stfun : forall x x' y y',
            subty x x' ->
            subty y' y ->
            subty (TFun x y) (TFun x' y')
| stsum : forall x x' y y',
            subty x x' ->
            subty y y' ->
            subty (TSum x y) (TSum x' y')
| strcd
| st_refl : forall t,
            subty t t
| st_trans : forall t0 t1 t2,
            subty t0 t1 ->
            subty t1 t2 ->
            subty t0 t2.

End SSmty.
