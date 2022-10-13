Require Import BinNums BinInt BinPos.
Require Import Lia.
(* Require Import FMapPositive. *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.

Import ListNotations.

Require Import BValues Ops Types Syntax Typing BUtils.
Require Import BEnv BMemory Validity SemanticsBlocking.

From compcert Require Import Integers Maps.

Local Open Scope option_bool_monad_scope.

(* Definition state := unit. *)

Section SAFETY.

Fixpoint expr_constraints (f: function) (e: expr) : option (list expr) :=
  match e with
  | Evar _ | Econst _ => Some []
  | Ecast e _ _ => expr_constraints f e
  | Eunop _ _ e => expr_constraints f e
  | Ebinop_arith _ _ e1 e2 | Ebinop_logical _ e1 e2
  | Ebinop_cmp _ _ e1 e2 | Ebinop_cmpu _ _ e1 e2 =>
      do c1 <- expr_constraints f e1;
      do c2 <- expr_constraints f e2;
      Some (c1 ++ c2)
  | Earr_access id idx =>
      do size <- list_assoc_pos f.(fn_arrszvar) id;
      do cidx <- expr_constraints f idx;
      Some (Ebinop_cmpu Oltu OInt64 idx (Evar size) :: cidx)
  end.

Fixpoint exprlist_constraints f l :=
  match l with
  | [] => Some []
  | e :: l =>
      do constrs <- expr_constraints f e;
      do lconstrs <- exprlist_constraints f l;
      Some (constrs ++ lconstrs)
  end.

Fixpoint guard_stmt_with_constraints_list (constrs: list expr) (s: stmt)
  : stmt :=
  match constrs with
  | [] => s
  | c :: constrs =>
      Sifthenelse c (guard_stmt_with_constraints_list constrs s) Serror
  end.

Definition guard_stmt_with_expr f e s :=
  do c <- expr_constraints f e;
  Some (guard_stmt_with_constraints_list (nodup expr_eq_dec c) s).

Section SAFETY_EXPR.

Section SAFETY_STMT.

Fixpoint call_constraints_rec (caller: function)   (arrszvar: list (ident * ident))
                              (params: list ident) (args: list ident) : option (list expr) :=
  match arrszvar with
  | [] => Some []
  | (id, sz) :: arrszvar =>
      do i <- index_of Pos.eq_dec params id;
      do j <- index_of Pos.eq_dec params sz;
      do id0 <- nth_error args i;
      do sz0 <- nth_error args j;
      do sz1 <- list_assoc_pos caller.(fn_arrszvar) id0;
      do constrs <- call_constraints_rec caller arrszvar params args;
      Some (Ebinop_cmpu Oleu OInt64 (Evar sz0) (Evar sz1) :: constrs)
  end.

Definition call_constraints (caller callee: function) (args: list ident) :=
  call_constraints_rec caller callee.(fn_arrszvar) callee.(fn_params) args.

End SAFETY_STMT.


Variable ge: genv.
Variable m: mem.
Variable f: function.
(* Variable te: tenv. *)
Variable e: env.
(* Variable arrszvar: list (ident * ident). *)

Fixpoint constraints_verified (constrs: list expr) : Prop :=
  match constrs with
  | [] => True
  | c :: constrs =>
      eval_expr m e f c Vtrue /\ constraints_verified constrs
  end.

(* Theorem expr_subject_reduction (exp: expr):
     forall t v,
       type_expression te exp = Some t ->
       eval_expr m e arrszvar te exp v ->
       well_typed_value v t.
   Proof.
     induction exp; simpl; intros.
     + inversion H0. congruence.
     + destruct c; inversion H0; revert H; intros [= <-]; eauto with typing.
     + destruct type_expression; try discriminate.
       destruct t1, t; try discriminate; revert H; intros [= <-];
         inversion H0; specialize (IHexp _ _ eq_refl H2);
         destruct v1; try discriminate;
         simpl in H4;
         try destruct s0;
         try destruct (Floats.Float32.to_int f); try destruct (Floats.Float32.to_int f0);
         try destruct (Floats.Float.to_int f); try destruct (Floats.Float.to_int f0);
         try destruct (Floats.Float32.to_long f); try destruct (Floats.Float32.to_long f0);
         try destruct (Floats.Float.to_long f); try destruct (Floats.Float.to_long f0);
         try destruct (f: floatsize); try destruct (f0: floatsize); try destruct s;
         try discriminate;
         try (revert H4; intros [= <-]; eauto with typing).
     + destruct u; simpl in H; destruct type_expression; try discriminate;
         destruct t0; try discriminate;
         try destruct i, s; try destruct o; try discriminate;
         try destruct (f: floatsize); try discriminate;
         revert H; intros [= <-];
         inversion H0; (specialize (IHexp _ _ eq_refl H4) || specialize (IHexp _ _ eq_refl H5));
         destruct v1; try discriminate;
         try (revert H5; intros [= <-]); try (revert H6; intros [= <-]); eauto with typing;
         inversion IHexp; eauto with typing.
     + destruct b; simpl in H;
         destruct type_expression, type_expression; try discriminate;
         destruct t0; try destruct t1; try discriminate;
         try destruct i0; try destruct s0; try destruct i; try destruct s; try discriminate;
         try destruct (f: floatsize); try destruct (f0: floatsize); try discriminate;
         try destruct o; try discriminate;
         revert H; intros [= <-];
         inversion H0;
         specialize (IHexp1 _ _ eq_refl H5); specialize (IHexp2 _ _ eq_refl H6);
         revert H7; inversion_clear IHexp1; inversion_clear IHexp2; try intros [= <-].
       Abort. *)
    (* 55: { simpl. }
       inversion IHexp1 as [injection]. revert H8 H10 H11; intros [= <-] [= ->] [= ->].
         destruct v1, v2; try discriminate.
       inversion IHexp1.
         try destruct i
       simpl in H7.
       destruct t1, t; try discriminate; revert H; intros [= <-];
         inversion H0; specialize (IHexp _ _ eq_refl H2);
         destruct v1; try discriminate;
         simpl in H4;
         try destruct s0;
         try destruct (Floats.Float32.to_int f); try destruct (Floats.Float32.to_int f0);
         try destruct (Floats.Float.to_int f); try destruct (Floats.Float.to_int f0);
         try destruct (Floats.Float32.to_long f); try destruct (Floats.Float32.to_long f0);
         try destruct (Floats.Float.to_long f); try destruct (Floats.Float.to_long f0);
         try destruct (f: floatsize); try destruct (f0: floatsize); try destruct s;
         try discriminate;
         try (revert H4; intros [= <-]; eauto with typing).
       simpl in H4.
       try destruct (f: floatsize).
       simpl in H4.
       revert H4; intros [= <-]. eauto with typing.
       revert H4; intros [= <-]. eauto with typing.
       simpl in H4;
         try destruct (Floats.Float32.to_int f);
         try destruct (Floats.Float.to_int f);
         try destruct (Floats.Float32.to_long f);
         try destruct (Floats.Float.to_long f);
         try discriminate;
         revert H4; intros [= <-]; eauto with typing.
       simpl in H4;
         try destruct (Floats.Float32.to_int f);
         try destruct (Floats.Float.to_int f);
         try destruct (Floats.Float32.to_long f);
         try destruct (Floats.Float.to_long f);
         try discriminate;
         revert H4; intros [= <-]; eauto with typing.
       simpl in H4;
         try destruct s0;
         try destruct (Floats.Float32.to_int f);
         try destruct (Floats.Float.to_int f);
         try destruct (Floats.Float32.to_long f);
         try destruct (Floats.Float.to_long f);
         try discriminate;
         revert H4; intros [= <-]; eauto with typing.
       simpl in H4;
         try destruct s0;
         try destruct (Floats.Float32.to_int f);
         try destruct (Floats.Float.to_int f);
         try destruct (Floats.Float32.to_long f);
         try destruct (Floats.Float.to_long f);
         try discriminate;
         revert H4; intros [= <-]; eauto with typing.
       simpl in H4;
         try destruct s0;
         try destruct (Floats.Float32.to_int f);
         try destruct (Floats.Float.to_int f);
         try destruct (Floats.Float32.to_long f);
         try destruct (Floats.Float.to_long f);
         try discriminate;
         revert H4; intros [= <-]; eauto with typing.
       simpl in H4;
         try destruct s0;
         try destruct (Floats.Float32.to_int f);
         try destruct (Floats.Float.to_int f);
         try destruct (Floats.Float32.to_long f);
         try destruct (Floats.Float.to_long f);
         try discriminate;
         revert H4; intros [= <-]; eauto with typing.
       simpl in H4;
         try destruct Floats.Float32.to_int;
         try destruct Floats.Float.to_int;
         try destruct Floats.Float32.to_long;
         try destruct Floats.Float.to_long;
         try discriminate;
         revert H4; intros [= <-]; eauto with typing.
       simpl in H4.
       revert H4; intros [= <-]. eauto with typing. *)


(* Lemma constraints_verified_app (c1 c2: list expr):
     constraints_verified c1 ->
     constraints_verified c2 ->
     constraints_verified (c1 ++ c2).
   Proof.
     induction c1; intros.
     + assumption.
     + simpl. destruct H. split; tauto.
   Qed. *)

(*

Lemma expr_subject_reduction (exp: expr):
  valid_expr m e se te exp ->
  valid_memory m e se ->
  forall t v,
    type_expression te exp = Some t ->
    eval_expr m e se exp v ->
    well_typed_value v t.
Proof.
  induction exp.
  + intros. simpl in H1. revert H1. intros [= <-].
    inversion_clear H2. apply well_typed_Vunit.
  + intros.
    inversion_clear H. inversion_clear H2. rewrite H3 in H. revert H. intros [= ->].
    simpl in H1, H5. rewrite H5 in H1. revert H1. intros [= ->]. assumption.
  + intros. induction c;
      inversion_clear H2; simpl in H1;
      [ case (Z.eqb (Int64.signed i) (Int64.unsigned i)) eqn:Hsig in H1 | | ];
      revert H1; intros [= <-];
      [ apply well_typed_Vint | apply well_typed_Vint |
        apply well_typed_Vfloat32 | apply well_typed_Vfloat64 ].
  + intros. inversion_clear H. induction u;
      (simpl in H1; destruct (type_expression te exp) eqn:H5; try easy;
       destruct t0 eqn:H6; try easy; clear H6;
       inversion_clear H2; specialize (IHexp H3 H0 t v1 H1 H));
       revert H1; intros [= <-]; inversion IHexp; rewrite <- H1 in H4;
       simpl in H4; revert H4; intros [= <-];
       (apply well_typed_Vbool || apply well_typed_Vint ||
        apply well_typed_Vfloat32 || apply well_typed_Vfloat64).
  + intros. inversion_clear H. inversion_clear H2. induction b, o;
      (simpl in H1;
      destruct (type_expression te exp1) eqn:H7; try easy; destruct t0 eqn:H8; try easy;
        destruct (type_expression te exp2) eqn:H9; try easy; destruct t1 eqn:H10; try easy;
       specialize (IHexp1 H3 H0 _ v1 (eq_refl _) H);
       specialize (IHexp2 H4 H0 _ v2 (eq_refl _) H5);
       (inversion IHexp1; inversion IHexp2)
       || inversion IHexp1; revert H2; intros [= <-];
          inversion IHexp2; revert H2; intros [= <-];
          (discriminate ||
             revert H6; intros [= <-];
             revert H1; intros [= <-];
            (apply well_typed_Vint || apply well_typed_Vfloat32 ||
             apply well_typed_Vfloat64))).
  + intros. inversion_clear H. inversion_clear H2. induction l;
      (simpl in H1;
      destruct (type_expression te exp1) eqn:H7; try easy; destruct t0 eqn:H8; try easy;
        destruct (type_expression te exp2) eqn:H9; try easy; destruct t1 eqn:H10; try easy;
       specialize (IHexp1 H3 H0 _ v1 (eq_refl _) H);
       specialize (IHexp2 H4 H0 _ v2 (eq_refl _) H5);
       inversion IHexp1; revert H2; intros [= <-];
       inversion IHexp2; revert H2; intros [= <-];
       revert H6; intros [= <-];
       revert H1; intros [= <-];
       apply well_typed_Vbool).
  + intros. inversion_clear H. inversion_clear H2. induction c, o;
      (simpl in H1;
      destruct (type_expression te exp1) eqn:H7; try easy; destruct t0 eqn:H8; try easy;
        destruct (type_expression te exp2) eqn:H9; try easy; destruct t1 eqn:H10; try easy;
       specialize (IHexp1 H3 H0 _ v1 (eq_refl _) H);
       specialize (IHexp2 H4 H0 _ v2 (eq_refl _) H5);
       inversion IHexp1; revert H2; intros [= <-];
       inversion IHexp2; revert H2; intros [= <-];
       (discriminate ||
         revert H6; intros [= <-];
         try (induction s, s0, i, i0; try discriminate);
         revert H1; intros [= <-]; apply well_typed_Vbool)).
  + intros. inversion_clear H. inversion_clear H2. induction c, o;
      (simpl in H1;
       destruct (type_expression te exp1) eqn:H7; try easy; destruct t0 eqn:H8; try easy;
      destruct s; try easy;
      destruct (type_expression te exp2) eqn:H9; try easy; destruct t1 eqn:H10; try easy;
      destruct s; try easy;
      specialize (IHexp1 H3 H0 _ v1 (eq_refl _) H);
      specialize (IHexp2 H4 H0 _ v2 (eq_refl _) H5);
      inversion IHexp1; revert H2; intros [= <-];
      inversion IHexp2; revert H2; intros [= <-];
      revert H6; intros [= <-];
      try (induction i, i0; try discriminate);
      revert H1; intros [= <-]; apply well_typed_Vbool).
  + intros. inversion_clear H. clear szvar n H6 H7. inversion_clear H2.
    unfold read_array in H10. rewrite H5 in H10.
    pose proof (nth_error_In lv (Z.to_nat (Int64.unsigned i0)) H10). clear H10.
    destruct (Forall_forall (fun v => well_typed_value v t0) lv) as [HForall _].
    pose proof (HForall H8 v H2). clear HForall H8 H2.
    cbn in H1.
    destruct (type_expression te exp) eqn:H11; try easy.
    destruct t1; try easy. destruct s; try easy. rewrite H4 in H1.
    revert H1. intros [= <-]. assumption.
Qed.

*)

Lemma constraints_verified_app (c1 c2: list expr):
  constraints_verified c1 /\ constraints_verified c2 <->
  constraints_verified (c1 ++ c2).
Proof.
  intros. split.
  + intros [H H0]. induction c1. assumption.
    destruct H. simpl. tauto.
  + intros. split; (induction c1; [easy | destruct H; simpl; tauto]).
Qed.

(*

Lemma expr_progress (exp: expr):
  valid_expr m e se te exp ->
  valid_memory m e se ->
  forall t constrs,
    type_expression te exp = Some t ->
    expr_constraints se exp = OK constrs ->
    constraints_verified constrs ->
    exists v, eval_expr m e se exp v /\ v <> Verr.
Proof.
  intros H H0. induction exp.
  + intros. exists Vunit. split. apply eval_Unit. discriminate.
  + intros. inversion_clear H. eexists. repeat split; try eassumption.
    apply eval_Var. assumption.
  + intros. induction c.
    - eexists; split. apply eval_Const_int. discriminate.
    - eexists; split. apply eval_Const_float32. discriminate.
    - eexists; split. apply eval_Const_float64. discriminate.
  + intros. inversion_clear H. simpl in H2. induction u;
    (simpl in H1; destruct (type_expression te exp) eqn:H5; try easy;
     destruct t0 eqn:H6; try easy;
     destruct (IHexp H4 _ _ H1 H2 H3) as [v [Hv1 Hv2]]; clear IHexp;
     pose proof expr_subject_reduction exp H4 H0 _ v H5 Hv1;
     inversion H; rewrite <- H7 in H, Hv1; clear H7;
     (eexists; split;
      [ apply (eval_Unop _ _ _ _ _ _ _ Hv1); reflexivity | discriminate ])).
  + intros. inversion_clear H. simpl in H2. unfold bind in H2.
    destruct (expr_constraints se exp1) eqn:H6; try easy.
    destruct (expr_constraints se exp2) eqn:H7; try easy.
    revert H2 H3. intros [= <-] H2.
    simpl in H1. apply constraints_verified_app in H2. destruct H2 as [Hl Hl0].
    induction b;
      ((idtac + (destruct o; try easy));
       destruct (type_expression te exp1) eqn:H8 in H1; try easy; destruct t0; try easy;
       destruct (type_expression te exp2) eqn:H9 in H1; try easy; destruct t0; try easy;
       (specialize (IHexp1 H4 _ _ H8 (eq_refl _) Hl);
        specialize (IHexp2 H5 _ _ H9 (eq_refl _) Hl0);
        destruct IHexp1 as [v1 [Hv1 Hv1']]; destruct IHexp2 as [v2 [Hv2 Hv2']];
        pose proof expr_subject_reduction _ H4 H0 _ _ H8 Hv1;
        pose proof expr_subject_reduction _ H5 H0 _ _ H9 Hv2;
        inversion H; inversion H2; rewrite <- H3 in Hv1; rewrite <- H10 in Hv2;
        unfold typ_corresp_opkind in H1;
        try (destruct o; try (discriminate || simpl in H1; destruct s; destruct s0; discriminate));
        eexists; split;
        [ apply (eval_Binop_arith _ _ _ _ _ _ _ _ _ _ Hv1 Hv2); reflexivity | discriminate ])).
  + intros. inversion_clear H. simpl in H2. unfold bind in H2.
    destruct (expr_constraints se exp1) eqn:H6; try easy.
    destruct (expr_constraints se exp2) eqn:H7; try easy.
    revert H2 H3. intros [= <-] H2.
    simpl in H1. apply constraints_verified_app in H2. destruct H2 as [Hl Hl0].
    destruct (type_expression te exp1) eqn:H8 in H1; try easy; destruct t0; try easy;
      destruct (type_expression te exp2) eqn:H9 in H1; try easy; destruct t0; try easy.
    specialize (IHexp1 H4 _ _ H8 (eq_refl _) Hl).
    specialize (IHexp2 H5 _ _ H9 (eq_refl _) Hl0).
    destruct IHexp1 as [v1 [Hv1 Hv1']]; destruct IHexp2 as [v2 [Hv2 Hv2']].
    pose proof expr_subject_reduction _ H4 H0 _ _ H8 Hv1.
    pose proof expr_subject_reduction _ H5 H0 _ _ H9 Hv2.
    inversion H; inversion H2; rewrite <- H3 in Hv1; rewrite <- H10 in Hv2.
    induction l;
      (eexists; split;
       [ apply (eval_Binop_logical _ _ _ _ _ _ _ _ _ Hv1 Hv2); reflexivity | discriminate ]).
  + intros. inversion_clear H. simpl in H2. unfold bind in H2.
    destruct (expr_constraints se exp1) eqn:H6; try easy.
    destruct (expr_constraints se exp2) eqn:H7; try easy.
    revert H2 H3. intros [= <-] H2.
    simpl in H1. apply constraints_verified_app in H2. destruct H2 as [Hl Hl0].
    induction c;
      (destruct (type_expression te exp1) eqn:H8 in H1; try easy; destruct t0; try easy;
       destruct (type_expression te exp2) eqn:H9 in H1; try easy; destruct t0; try easy;
       (specialize (IHexp1 H4 _ _ H8 (eq_refl _) Hl);
        specialize (IHexp2 H5 _ _ H9 (eq_refl _) Hl0);
        destruct IHexp1 as [v1 [Hv1 Hv1']]; destruct IHexp2 as [v2 [Hv2 Hv2']];
        pose proof expr_subject_reduction _ H4 H0 _ _ H8 Hv1;
        pose proof expr_subject_reduction _ H5 H0 _ _ H9 Hv2;
        inversion H; inversion H2; rewrite <- H3 in Hv1; rewrite <- H10 in Hv2;
        unfold typ_corresp_opkind in H1;
        destruct o; try (discriminate || simpl in H1; destruct s; destruct s0; discriminate);
        eexists; split;
        [ apply (eval_Binop_cmp _ _ _ _ _ _ _ _ _ _ Hv1 Hv2); reflexivity | discriminate ])).
  + intros. inversion_clear H. simpl in H2. unfold bind in H2.
    destruct (expr_constraints se exp1) eqn:H6; try easy.
    destruct (expr_constraints se exp2) eqn:H7; try easy.
    revert H2 H3. intros [= <-] H2.
    simpl in H1. apply constraints_verified_app in H2. destruct H2 as [Hl Hl0].
    induction c;
      (destruct (type_expression te exp1) eqn:H8 in H1; try easy; destruct t0; try easy;
       destruct s; try easy;
       destruct (type_expression te exp2) eqn:H9 in H1; try easy; destruct t0; try easy;
       destruct s; try easy;
       (specialize (IHexp1 H4 _ _ H8 (eq_refl _) Hl);
        specialize (IHexp2 H5 _ _ H9 (eq_refl _) Hl0);
        destruct IHexp1 as [v1 [Hv1 Hv1']]; destruct IHexp2 as [v2 [Hv2 Hv2']];
        pose proof expr_subject_reduction _ H4 H0 _ _ H8 Hv1;
        pose proof expr_subject_reduction _ H5 H0 _ _ H9 Hv2;
        inversion H; inversion H2; rewrite <- H3 in Hv1; rewrite <- H10 in Hv2;
        unfold typ_corresp_opkind in H1;
        destruct o; try (discriminate || simpl in H1; destruct s; destruct s0; discriminate);
        eexists; split;
        [ apply (eval_Binop_cmpu _ _ _ _ _ _ _ _ _ _ Hv1 Hv2); reflexivity | discriminate ])).
  + intros. inversion_clear H. clear szvar n H7 H8. simpl in H2. unfold bind in H2.
    destruct (find_sizevar se i) eqn:Hi0; try easy.
    unfold find_sizevar in Hi0. destruct se!i eqn:Hi0'; try easy.
    revert Hi0 Hi0'; intros [= ->] Hszvar.
    destruct (expr_constraints se exp) eqn:Hcexp; try easy.
    revert H2 H3; intros [= <-] Hconstrs. destruct Hconstrs.
    simpl in H1.
    destruct (type_expression te exp) eqn:Htexp; try easy. destruct t1; try easy.
    destruct s; try easy. destruct (te ! i) eqn:Htei; try easy. destruct t1; try easy.
    revert H1 H5 Htei; intros [= ->] _ Htei.
    specialize (IHexp H4 _ _ (eq_refl _) (eq_refl _) H2).
    destruct (H0 i lv i0 H6 Hszvar) as [ _ [ Hlv Hread ] ].
    inversion_clear H. inversion_clear H3.
    pose proof (expr_subject_reduction exp H4 H0 _ _ Htexp H1).
    inversion H3.
    pose proof Hlv as Hlv'.
    revert Hlv' H H7 H5. intros [= ->] [= <-] [= <-] Hidx.
    inversion Hidx. clear Hidx.
    specialize (Hread n H5).
    pose proof (read_not_None m e se H0 i lv i0 H6 Hszvar Hlv _ H5) as HreadNNone.
    apply option_not_none_exists in HreadNNone. destruct HreadNNone as [ v Hv ].
    rewrite Hv in Hread.
    eexists. split. apply (eval_Arr_access _ _ _ _ _ _ _ _ _ H1 Hszvar Hlv H5).
    eassumption. intro. rewrite H in Hread. contradiction.
Qed.

*)

End SAFETY_EXPR.

End SAFETY.
