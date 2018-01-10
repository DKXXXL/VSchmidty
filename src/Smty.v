Add LoadPath "src".
Require Import Maps.
Require Import Context.
Import Context.Context.
Require Import Coq.Lists.List.

Module Smty.

Definition tyid := id.

Inductive ty : Set :=
    | TNat : ty 
    | TChr : ty
    | TFun : ty -> ty -> ty
    | TBool : ty
    | TSum : ty -> ty -> ty
    | TNone : ty
    | TVar : tyid -> ty
    (* TRcd won't appear. Shouldn't appear. 
        It will only appear in Structual Mode.
        But at first, at type checking stage, it's 
        Nominal Mode.
    *)
    | TRcd : ty -> list (id* ty) -> ty.

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

Definition Rcd : Set := ty * (list (id * ty)).

Definition directSubty (ctx : Context (type := Rcd)) (i : tyid) : option ty :=
    match (byContext ctx i) with
    | None => None
    | Some (a, _) => Some a
    end.
    

Inductive subty (ctx : Context (type := Rcd)) : ty -> ty -> Prop :=
| stfun : forall x x' y y',
            subty ctx x x' ->
            subty ctx y' y ->
            subty ctx (TFun x y) (TFun x' y')
| stsum : forall x x' y y',
            subty ctx x x' ->
            subty ctx y y' ->
            subty ctx (TSum x y) (TSum x' y')
| strcdn : forall i,
            subty ctx (TVar i) TNone
| strcdc : forall i x,
            directSubty ctx i = Some x ->
            subty ctx (TVar i) x
| strcd_refl : forall t,
            subty ctx t t
| strcd_trans : forall t0 t1 t2,
            subty ctx t0 t1 ->
            subty ctx t1 t2 ->
            subty ctx t0 t2.

End Smty.
