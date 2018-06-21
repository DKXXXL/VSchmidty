Add LoadPath "src".
Require Import Maps.
Require Import Coq.Relations.Relation_Definitions.
Require Import LibTactics.
Require Import Context.

Import Context.Context.

Module Subcontext.

Parameter targetT : Set.
Parameter rel : targetT -> targetT -> Prop.

Parameter is_trans : forall x y z, rel x y -> rel y z -> rel x z.



Definition context_sub  :=
    fun (x y : Context (type := targetT)) => 
        forall X i,
            byContext x i = Some X ->
            exists Y, byContext y i = Some Y /\ rel X Y.

(* Parameter is_refl : forall x, rel x x.



Theorem asymm_context_sub :
    forall (x y : Context (type := targetT)),
        x y ->
        y =- x ->
        x =-= y.

unfold context_sub. unfold context_equivalence. 
intros; eauto.
destruct (byContext x i) eqn: h0; subst; eauto.
rewrite (H _ _ h0); eauto.
destruct (byContext y i) eqn: h1; subst; eauto.
poses' (H0 _ _ h1).
rewrite h0 in H1; discriminate.
Qed.

Theorem context_equivalence__context_sub :
    forall (x y : Context (type := targetT)),
        x =-= y ->
        context_sub x y.
        unfold context_sub. unfold context_equivalence. 
        intros; exists X; split; eauto.
        rewrite <- H. eauto.
        apply is_refl.
Qed. *)

Theorem refl_ctx_sub :
    forall (x : Context (type := targetT)),
        (forall y, rel y y) ->
        context_sub x x.

unfold context_sub. intros; exists X; split; eauto.

Qed.

End Module.
