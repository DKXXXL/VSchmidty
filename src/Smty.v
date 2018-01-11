Add LoadPath "src".
Require Import Maps.
Require Import Context.
Import Context.Context.
Require Import Coq.Lists.List.

Module Smty.

Definition tyid := id.

(* Nominal Typing *)

Inductive ty : Set :=
    | TNat : ty 
    | TChr : ty
    | TFun : ty -> ty -> ty
    | TBool : ty
    | TSum : ty -> ty -> ty
    | TNone : ty
    (*| TVar : tyid -> ty *)
    (* 
        Everything as TVar would be substitue to 
        Corresponding record type.
        So I will just erase it since
        it add complexity.
    *)
    | TRcd : tyid -> ty -> list (id* ty) -> ty.

Inductive tm : Set :=
    | tnone : tm 
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
    | tfield : ty -> id -> tm 
        (*
            TypeA.a :: TypeA -> Int
        *)
    | tseq : tm -> tm.



Inductive inheritable : ty -> Prop :=
| inh_n : inheritable TNone
| inh_r : forall c suty l,
            inheritable (TRcd c suty l).

(* Structual Information will not be checked until 
    type name elimination. *)

(*
    Inductive subrcd : (list (id * ty)) -> (list (id * ty)) -> Prop :=
    | srn: forall x, subrcd x []
    | srS: forall i t0 t1 rcd0 rcd1,
            subty t0 t1 ->
            subrcd rcd0 rcd1 ->
            subrcd ((i, t0): rcd0) ((i, t1): rcd1).
            *)

Inductive subty  : ty -> ty -> Prop :=
| stfun : forall x x' y y',
            subty x x' ->
            subty y' y ->
            subty (TFun x y) (TFun x' y')
| stsum : forall x x' y y',
            subty x x' ->
            subty y y' ->
            subty (TSum x y) (TSum x' y')
| strcds : forall tid suty rcd,
            inheritable suty ->
            subty (TRcd tid suty rcd) suty
| st_refl : forall t,
            subty t t
| st_trans : forall t0 t1 t2,
            subty t0 t1 ->
            subty t1 t2 ->
            subty t0 t2.

End Smty.
