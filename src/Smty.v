Add LoadPath "src".
Require Import Maps.
Require Import Context.
Import Context.Context.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.


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

Axiom nominal_eq : 
    forall tid su0 su1 rcd0 rcd1,
        TRcd tid su0 rcd0 = TRcd tid su1 rcd1. 

(* Scheme Equality for ty. is not working. *)
Theorem eq_ty_dec (T0 T1:ty) : {T0 = T1} + {T0 <> T1}.
generalize dependent T1.
induction T0; intro T1; induction T1;

try 
(match goal with
| [|- {?X = ?X} + {_}] => left; auto; fail
| [|- {_} + {?X <> ?Y}] => right; intro; discriminate
end).
    destruct (IHT0_1 T1_1); destruct (IHT0_2 T1_2); subst; try tauto;
    right; intro K; injection K; subst; auto.
    destruct (IHT0_1 T1_1); destruct (IHT0_2 T1_2); subst; try tauto;
    right; intro K; injection K; subst; auto.
    destruct (eq_id_dec t t0);subst; eauto using nominal_eq.
    right; intro K; injection K; subst; auto.

Qed.

Definition eq_ty_dec_bool (T0 T1: ty) : bool :=
    if (eq_ty_dec T0 T1) then true else false.


Theorem eq_ty_dec_id:
    forall t (A: Set) (a b : A),
        (if eq_ty_dec t t then a else b) = a.
    intro t. destruct (eq_ty_dec t t); eauto. 
    destruct (n eq_refl).
Qed.

Theorem eq_ty_dec_nid:
    forall t0 t1 (A: Set) (a b : A),
        t0 <> t1 ->
        (if eq_ty_dec t0 t1 then a else b) = b.

    intros t0 t1. destruct (eq_ty_dec t0 t1); subst; eauto; try discriminate.
    intros. destruct (H eq_refl).
Qed.

Theorem eq_ty_dec_bool_true:
    forall t ,
        eq_ty_dec_bool t t = true.
    unfold eq_ty_dec_bool. intro. eapply eq_ty_dec_id.
Qed.

Theorem eq_ty_dec_bool_false:
    forall t0 t1,
    t0 <> t1 ->
    eq_ty_dec_bool t0 t1 = false.

    intros t0 t1. eapply eq_ty_dec_nid.
Qed.

Theorem true_eq_ty_dec_bool:
    forall t0 t1,
        eq_ty_dec_bool t0 t1 = true ->
        t0 = t1.
    unfold eq_ty_dec_bool. intros.
    destruct (eq_ty_dec t0 t1); subst; auto; try discriminate.
Qed.

Theorem false_eq_ty_dec_bool:
    forall t0 t1,
        eq_ty_dec_bool t0 t1 = false ->
        t0 <> t1.
    unfold eq_ty_dec_bool. intros.
    destruct (eq_ty_dec t0 t1); subst; auto; try discriminate.
Qed.


    


Inductive tm : Set :=
    | tnone : tm 
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
    | tseq : tm -> tm -> tm.

Hint Constructors tm.


Inductive inheritable : ty -> Prop :=
| inh_n : inheritable TNone
| inh_r : forall c suty l,
            inheritable (TRcd c suty l).

Hint Constructors inheritable.

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

Hint Constructors subty.

End Smty.
