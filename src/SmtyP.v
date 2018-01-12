Add LoadPath "src".
Require Import Maps.
Require Import Context.

Import Context.Context.
Require Import Coq.Lists.List.
Require Import Smty.
Require Import LibTactics.

Import Smty.Smty.



Module SmtyP.
(* Nominal Typing. *)

Fixpoint rcd_cons_ty (rcd : list (id * ty)) (retty : ty) : ty :=
    match rcd with
    | nil => retty
    | (_, h)::t => TFun h (rcd_cons_ty t retty)
    end. 

Fixpoint rcd_field_ty (rcd: list (id * ty)) (field : id) : option ty :=
    match rcd with
    | nil => None
    | (i, ret)::t  => if (eq_id_dec i field) 
                        then Some ret 
                        else rcd_field_ty t field
    end.



Inductive has_type : Context -> tm -> ty -> Prop :=
| ht_none : 
    forall ctx,
        has_type ctx tnone TNone
| ht_if : 
    forall vctx crit tb fb T,
    has_type vctx crit TBool ->
    has_type vctx tb T ->
    has_type vctx fb T ->
    has_type vctx (tif crit tb fb) T
| ht_var: forall ctx T i,
    byContext ctx i = Some T ->
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
| ht_fun : forall ctx i T body TO,
    has_type (update i T ctx) body TO ->
    has_type ctx (tfun i T body) (TFun T TO)
| ht_app : forall ctx t0 t1 T0 T1,
    has_type ctx t0 (TFun T0 T1) ->
    has_type ctx t1 T0 ->
    has_type ctx (tapp t0 t1) T1
| ht_let : forall ctx i T bind body T',
    has_type (update i T ctx) bind T ->
    has_type (update i T ctx) body T' ->
    has_type ctx (tlet i T bind body) T'
| ht_true : forall ctx,
    has_type ctx ttrue TBool
| ht_false : forall ctx,
    has_type ctx tfalse TBool
| ht_beq : forall ctx t0 t1,
    has_type ctx t0 TBool ->
    has_type ctx t1 TBool ->
    has_type ctx (tbeq t0 t1) TBool
| ht_left : forall ctx t0 TL TR,
    has_type ctx t0 TL ->
    has_type ctx (tleft t0 TR) (TSum TL TR)
| ht_right : forall ctx t0 TL TR,
    has_type ctx t0 TR ->
    has_type ctx (tright TL t0) (TSum TL TR)
| ht_case : forall ctx crit tl tr TL TR TO,
    has_type ctx crit (TSum TL TR) ->
    has_type ctx tl (TFun TL TO) ->
    has_type ctx tr (TFun TR TO) ->
    has_type ctx (tcase crit tl tr) TO
| ht_letrcd : forall ctx cons rcd tid suty body TO,
    subty (TRcd tid suty rcd) suty ->
    has_type (update cons (rcd_cons_ty rcd (TRcd tid suty rcd)) ctx) body TO ->
    has_type ctx (tletrcd cons tid suty rcd body) TO
| ht_field : forall ctx rcd i tid suty T,
    rcd_field_ty rcd i = Some T ->
    has_type ctx (tfield (TRcd tid suty rcd) i) (TFun (TRcd tid suty rcd) T)
| ht_seq : forall ctx t0 t1 T0 T1,
    has_type ctx t0 T0 ->
    has_type ctx t1 T1 ->
    has_type ctx (tseq t0 t1) T1.

Hint Constructors has_type.


Fixpoint nominal_typed (ctx: Context) (t : tm) : option ty :=
    match t with
    | tnone => Some TNone
    | tif crit tb fb => 
        match (nominal_typed ctx crit) with
            | Some TBool => match (nominal_typed ctx tb), (nominal_typed ctx fb) with
                            | Some a, Some b => if(eq_ty_dec a b) then Some a else None
                            | _, _ => None
                            end
            | _ => None
        end
    | tvar i => byContext ctx i
    | tint _ => Some TNat
    | tsuc n => 
        match (nominal_typed ctx n) with
            | Some TNat => Some TNat
            | _ => None
        end
    | tdec n =>
        match (nominal_typed ctx n) with
            | Some TNat => Some TNat
            | _ => None
        end
    | tngt a b => 
        match (nominal_typed ctx a), (nominal_typed ctx b) with
            | Some TNat, Some TNat => Some TBool
            | _, _ => None
        end
    | tnlt a b =>
        match (nominal_typed ctx a), (nominal_typed ctx b) with
            | Some TNat, Some TNat => Some TBool
            | _, _ => None
        end
    | tneq a b =>
        match (nominal_typed ctx a), (nominal_typed ctx b) with
            | Some TNat, Some TNat => Some TBool
            | _, _ => None
        end
    | tchr _ => Some TChr
    | tceq a b =>
        match (nominal_typed ctx a), (nominal_typed ctx b) with
            | Some TChr, Some TChr => Some TBool
            | _, _ => None
        end   
    | tfun i T body =>
        match nominal_typed (update i T ctx) body with
            | Some TO => Some (TFun T TO)
            | _ => None
        end
    | tapp a b =>
        match (nominal_typed ctx a), (nominal_typed ctx b) with
            | Some (TFun i o), Some Ti => if(eq_ty_dec i Ti) then Some o else None
            | _, _ => None
        end
    | tlet i T bind body =>
        match (nominal_typed (update i T ctx) bind) with
        | Some Tbind => if (eq_ty_dec T Tbind) then nominal_typed (update i T ctx) body else None
        | _ => None
        end
    | ttrue => Some TBool
    | tfalse => Some TBool
    | tbeq a b=>
        match (nominal_typed ctx a), (nominal_typed ctx b) with
            | Some TBool, Some TBool => Some TBool
            | _, _ => None
        end   
    | tleft t T =>
        match (nominal_typed ctx t) with
            | Some TL => Some (TSum TL T)
            | _ => None
        end
    | tright T t =>
        match (nominal_typed ctx t) with
            | Some TR => Some (TSum T TR)
            | _ => None
        end
    | tcase crit lb rb =>
        match (nominal_typed ctx crit), (nominal_typed ctx lb), (nominal_typed ctx rb) with
        | Some (TSum TL TR), Some (TFun TL0 TO0), Some (TFun TR0 TO1) =>
            if (andb (eq_ty_dec_bool TL TL0) (andb (eq_ty_dec_bool TR TR0) (eq_ty_dec_bool TO0 TO1)) )
            then Some TO0 else None
        | _, _, _ => None
        end
    | tletrcd cons' T suTy rcd body =>
        nominal_typed (update cons' (rcd_cons_ty rcd (TRcd T suTy rcd)) ctx) body
    | tfield (TRcd a b rcd) i => 
        match (rcd_field_ty rcd i) with
        | Some TO => Some (TFun (TRcd a b rcd) TO)
        | _ => None
        end
    | tfield _ _ => None
    | tseq pre post =>
        match nominal_typed ctx pre with
        | Some _ => nominal_typed ctx post
        | _ => None
        end
    end.

Ltac keep_rewrite :=
    match goal with
    | h: _ = _ |- _ => rewrite h; clear h; keep_rewrite
    | h: _ = _ |- _ => try rewrite <- h; clear h; keep_rewrite
    | _ => idtac
    end.

Theorem typed__nominal_typed :
    forall t T, 
    has_type empty t T -> 
    nominal_typed empty t = Some T.

    intros t T h;
    induction h; try (eauto; fail);

    cbn; 
    keep_rewrite; eauto using eq_ty_dec_id.

    repeat (rewrite eq_ty_dec_bool_true). cbn. auto.
Qed.

Ltac destruct_match :=
    match goal with
    | h: match ?A with  _ => _  end = _ |- _ => destruct A; destruct_match; subst; eauto
    | _ => idtac
    end.

Ltac apply_ctx ctx :=
    match goal with
    | h: forall x, _ |- _ => 
        let x := fresh "h" in
        (pose (h ctx) as x); generalize x; clear x; clear h; apply_ctx ctx
    | _ => idtac
    end; intros.

Ltac destruct_match_keep :=
    match goal with
    | h: match ?A with  _ => _  end = _ |- _ => 
        let k:= fresh in
        destruct A eqn: k; destruct_match_keep
    | _ => idtac
    end.

Ltac true_AND_has_to_be_true :=
    match goal with
    | h: (andb ?A  ?B) = true |- _ => 
    let a := fresh "A" in
    let b := fresh "B" in
    destruct A eqn:a; 
    destruct B eqn:b; 
    try rewrite a in h; 
    try rewrite b in h; 
    eauto; cbn in h; 
    try discriminate; 
    generalize dependent h; true_AND_has_to_be_true
    | _ => idtac
    end; intros.

Theorem nominal_typed__typed:
    forall t ctx T, 
    nominal_typed ctx t = Some T ->
    has_type ctx t T.

    intros t.
    induction t; intros; eauto;
    try (cbn in H;
    apply_ctx ctx;
        destruct_match;
        try discriminate;
        match goal with
        | h : Some _ = Some _ |- _ => injection h; intros; subst; eauto
        | _ => idtac
        end; fail).
    (* Case TFun. I am lazy with abstraction... *)
    cbn in H.
    poses' (IHt (update i t ctx)).
    destruct_match.
    injection H;intros ;subst;eauto.
    try discriminate.

    (* Case tlet *)
    cbn in H.
    poses' (IHt1 (update i t1 ctx)).
    poses' (IHt2 (update i t1 ctx)).
    destruct_match; try discriminate.

    (* Case tcase *)
    apply_ctx ctx.
    cbn in H.
    destruct_match_keep; subst; eauto;
    try discriminate.
    forwards: h;
    forwards: h0;
    forwards: h1; eauto.
(*    let a := fresh "A" in
    let b := fresh "B" in
    destruct (eq_ty_dec_bool t0_1 t4_1) eqn:a; 
    destruct (eq_ty_dec_bool t0_2 t5_1) eqn:b.
    rewrite a in H6; 
    rewrite b in H6; 
    eauto; cbn in H6; 
    try discriminate; 
    generalize dependent H6.*)
    true_AND_has_to_be_true.
    
    

    
    


End SmtyP.