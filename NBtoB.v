Require Import Coq.Lists.List.
Require Import BinNums BinInt.
Require Import Coq.Bool.Bool.
Require Import String.
Require Import Lia.

Import ListNotations.

Require Import BValues Types Syntax Typing Ops BUtils.
Require Import BEnv BMemory Validity SemanticsBlocking SemanticsNonBlocking.
Require Import Safety.

From compcert Require Import Integers Floats Maps Errors Smallstep.
From compcert Require Import Globalenvs.

Local Open Scope option_bool_monad_scope.
Local Open Scope error_monad_scope.

Create HintDb nbtob.

Section NonBlockingSemanticsToBlockingSemantics.

Fixpoint transl_stmt (ge: genv) (f: function) (s: stmt) : res stmt :=
  match s with
  | Sskip => OK s
  | Sassign id e =>
      do** g <- guard_stmt_with_expr f e s; OK g
  | Sarr_assign idarr idx e =>
      do** size <- list_assoc_pos f.(fn_arrszvar) idarr;
      do** idx_constrs <- expr_constraints f idx;
      do** constrs <- expr_constraints f e;
      let c := idx_constrs ++ constrs ++ [Ebinop_cmpu Oltu OInt64 idx (Evar size)] in
      OK (guard_stmt_with_constraints_list (nodup expr_eq_dec c) (Sarr_assign idarr idx e))
  | Scall _ fd args =>
      match ge!fd with
      | Some (Internal callee) =>
          do** constrs <- call_constraints f callee args;
          OK (guard_stmt_with_constraints_list (nodup expr_eq_dec constrs) s)
      | Some (External ef) => OK s
      | None => Error [MSG ""]
      end
  | Sreturn e =>
      do** g <- guard_stmt_with_expr f e s; OK g
  | Sseq s1 s2 =>
      do s1 <- transl_stmt ge f s1;
      do s2 <- transl_stmt ge f s2;
      OK (Sseq s1 s2)
  | Sifthenelse cond strue sfalse =>
      do strue <- transl_stmt ge f strue;
      do sfalse <- transl_stmt ge f sfalse;
      do** g <- guard_stmt_with_expr f cond (Sifthenelse cond strue sfalse); OK g
  | Sloop s =>
      do s <- transl_stmt ge f s;
      OK (Sloop s)
  | Scontinue | Sbreak | Serror => OK s
  end.

Definition transl_function (ge: genv) (f: function) : res function :=
  do tfn_body <- transl_stmt ge f f.(fn_body);
  OK (mk_function f.(fn_sig)
                  f.(fn_params)
                  f.(fn_arrszvar)
                  f.(fn_vars)
                  tfn_body
                  f.(fn_tenv)
                  f.(fn_nodup)
                  f.(fn_nodup_params)
                  f.(fn_disjoint)
                  f.(fn_tenv_arrszvar)
                  f.(fn_tenv_sig)
                  f.(fn_sig_arrszvar)).

Definition transl_fundef (ge: genv) (fd: fundef) : res fundef :=
  match fd with
  | External ef => OK (External ef)
  | Internal f =>
      do tf <- transl_function ge f;
      OK (Internal tf)
  end.

Fixpoint transl_cont (ge: genv) (f: option function) (k: SemanticsNonBlocking.cont)
    : res SemanticsBlocking.cont :=
  match k with
  | Kstop => OK SemanticsBlocking.Kstop
  | Kloop s k =>
      match f with
      | Some f' =>
          do s' <- transl_stmt ge f' s;
          do k' <- transl_cont ge f k;
          OK (SemanticsBlocking.Kloop s' k')
      | None => Error [ MSG "" ]
      end
  | Kseq s k =>
      match f with
      | Some f' =>
          do  s' <- transl_stmt ge f' s;
          do  k' <- transl_cont ge f k;
          OK (SemanticsBlocking.Kseq s' k')
      | None => Error [ MSG "" ]
      end
  | Kreturnto id e' f' _ k =>
      do k' <- transl_cont ge (Some f') k;
      do tf' <- transl_function ge f';
      OK (SemanticsBlocking.Kreturnto id e' tf' k')
  end.

Definition transl_genv (ge: genv) : res genv :=
  map_error (fun _ fd => transl_fundef ge fd) ge.

Definition transl_fundefs (ge: genv) (defs: list (ident * fundef))
    : res (list (ident * fundef)) :=
  list_map_error (fun x => do tfd <- transl_fundef ge (snd x); OK (fst x, tfd)) defs.

Lemma transl_fundefs_eq_map_fst:
  forall ge defs tdefs,
    transl_fundefs ge defs = OK tdefs ->
    map fst defs = map fst tdefs.
Proof.
  induction defs; simpl; intros.
  + revert H; intros [= <-]. reflexivity.
  + destruct a as [id fd].
    cbn in H.
    destruct (transl_fundef ge fd), list_map_error eqn:H0; try discriminate.
    revert H; intros [= <-]. rewrite IHdefs with (1 := H0). reflexivity.
Qed.

Lemma transl_cont_None_Some:
  forall ge f k tk,
    transl_cont ge None k = OK tk ->
    transl_cont ge (Some f) k = OK tk.
Proof. induction k; easy. Qed.

Hint Resolve transl_cont_None_Some : nbtob.

Lemma transl_fundefs_list_assoc_nodup:
     forall ge defs,
       list_assoc_nodup defs ->
       match transl_fundefs ge defs with
       | OK tdefs => list_assoc_nodup tdefs
       | _ => True
       end.
Proof.
  intros. unfold list_assoc_nodup.
  destruct (transl_fundefs ge defs) eqn:H0.
  erewrite <- transl_fundefs_eq_map_fst; eassumption.
  easy.
Qed.

Definition transl_program (p: program) : res program.
Proof.
 generalize (transl_fundefs_list_assoc_nodup (genv_of_program p) p.(prog_defs) p.(prog_nodup)).
 generalize (transl_fundefs_eq_map_fst (genv_of_program p) (prog_defs p)).
 destruct transl_fundefs; intros Hmapfst Hnodup.
 apply OK, (mk_program l p.(prog_main)). exact Hnodup.
 rewrite <- (Hmapfst l eq_refl). exact p.(prog_main_exists).
 exact (Error e).
Defined.

Lemma transl_genv_internal_preservation:
  forall ge ge' id f f' tfn_body,
    transl_genv ge = OK ge' ->
    ge ! id = Some (Internal f) ->
    ge' ! id = Some (Internal f') ->
    transl_stmt ge f (fn_body f) = OK tfn_body ->
    fn_body f' = tfn_body.
Proof.
  intros.
  unfold transl_genv in H.
  destruct (map_error_OK_f _ id ge ge' (Internal f) H H0) as [y Hy].
  pose proof (get_map_error_Some _ id ge ge' (Internal f) y H H0).
  simpl in Hy, H3. destruct (transl_function) eqn:Htfun; try discriminate.
  specialize (H3 Hy). rewrite H3 in H1. revert H1 Hy; intros [= ->] [= <-]. clear H H0.
  unfold transl_function in Htfun. rewrite H2 in Htfun. simpl in Htfun.
  revert Htfun; intros [= <-]. reflexivity.
Qed.

Lemma valid_expr_constraints:
  forall f exp,
    valid_expr f exp ->
    exists constrs,
      expr_constraints f exp = Some constrs.
Proof.
  intros. induction exp.
  + eexists; reflexivity.
  + eexists; reflexivity.
  + inversion_clear H. apply IHexp. assumption.
  + inversion_clear H. apply IHexp in H0. simpl. exact H0.
  + inversion_clear H. apply IHexp1 in H0. apply IHexp2 in H1.
    destruct H0 as [c1 Hc1]. destruct H1 as [c2 Hc2].
    eexists. simpl. rewrite Hc1. rewrite Hc2. simpl. reflexivity.
  + inversion_clear H. apply IHexp1 in H0. apply IHexp2 in H1.
    destruct H0 as [c1 Hc1]. destruct H1 as [c2 Hc2].
    eexists. simpl. rewrite Hc1. rewrite Hc2. simpl. reflexivity.
  + inversion_clear H. apply IHexp1 in H0. apply IHexp2 in H1.
    destruct H0 as [c1 Hc1]. destruct H1 as [c2 Hc2].
    eexists. simpl. rewrite Hc1. rewrite Hc2. simpl. reflexivity.
  + inversion_clear H. apply IHexp1 in H0. apply IHexp2 in H1.
    destruct H0 as [c1 Hc1]. destruct H1 as [c2 Hc2].
    eexists. simpl. rewrite Hc1. rewrite Hc2. simpl. reflexivity.
  + inversion_clear H. apply IHexp in H0. destruct H0 as [c Hc].
    simpl. destruct H2 as [szvar H2].
    apply list_assoc_pos_Some2 in H2. destruct H2 as [z H2].
    rewrite H2, Hc. eexists. reflexivity.
Qed.

Ltac destruct_tf f tf :=
  match goal with
  | Htf: (transl_function _ f = OK tf) |- _ =>
      unfold transl_function in Htf;
      destruct transl_stmt in Htf; try discriminate;
      revert Htf; intros [= <-]
  end.

Theorem transl_expr_sem_preservation:
  forall p m e f tf exp v
    (Htf: transl_function (genv_of_program p) f = OK tf),
    SemanticsNonBlocking.eval_expr m e f exp (Some v) ->
    SemanticsBlocking.eval_expr m e tf exp v.
Proof.
  intros until v. intro. destruct_tf f tf. revert m e f s exp v.
  induction exp; intros; inversion H; try inversion H7; eauto with semantics.
Qed.

Hint Resolve transl_expr_sem_preservation : nbtob.

Theorem transl_exprlist_sem_preservation:
  forall p m e f tf le lv
    (Htf: transl_function (genv_of_program p) f = OK tf),
    SemanticsNonBlocking.eval_exprlist m e f le (Some lv) ->
    SemanticsBlocking.eval_exprlist m e tf le lv.
Proof. induction le; intros; inversion H; eauto with nbtob semantics. Qed.

Hint Resolve transl_exprlist_sem_preservation : nbtob.

Theorem identlist_sem_preservation:
  forall p e f tf li lv
    (Htf: transl_function (genv_of_program p) f = OK tf),
    SemanticsNonBlocking.eval_identlist e f li (Some lv) ->
    SemanticsBlocking.eval_identlist e tf li lv.
Proof.
  intros until lv. intro. destruct_tf f tf. revert li lv.
  induction li; simpl; intros; inversion H; eauto with semantics. Qed.

Lemma eval_expr_injective:
  forall m e f exp v1 v2,
    list_assoc_nodup f.(fn_arrszvar) ->
    eval_expr m e f exp v1 ->
    eval_expr m e f exp v2 ->
    v1 = v2.
Proof.
  intros m e f exp v1 v2 Hnodup. revert v1 v2.
  induction exp; simpl; intros;
    try (inversion H; inversion H0; rewrite_equalities; easy);
    inversion_clear H; inversion_clear H0; try easy;
    try (specialize (IHexp _ _ H H1); discriminate || rewrite_equalities; easy);
    try destruct H as [[H H4] | [H H4]];
    try destruct H1 as [[H1 H4] | [H1 H4]];
    try (specialize (IHexp1 _ _ H H1);
         specialize (IHexp2 _ _ H2 H4); congruence).
  + specialize (IHexp _ _ H3 H12). congruence.
  + inversion_clear H5. inversion_clear H12.
    apply list_assoc_nodup_injective with (1 := Hnodup) (2 := H4) in H11.
    specialize (IHexp _ _ H H3). congruence.
  + inversion_clear H3. inversion_clear H8.
    apply list_assoc_nodup_injective with (1 := Hnodup) (2 := H2) in H7.
    specialize (IHexp _ _ H1 H6). congruence.
Qed.

Lemma eval_expr_Some_constraints_verified:
  forall p m e f tf exp v constrs,
    transl_function (genv_of_program p) f = OK tf ->
    list_assoc_nodup f.(fn_arrszvar) ->
    SemanticsNonBlocking.eval_expr m e f exp (Some v) ->
    Safety.expr_constraints f exp = Some constrs ->
    SemanticsBlocking.eval_exprlist m e tf constrs (map (fun _ => Vtrue) constrs).
Proof.
  induction exp; intros v constrs Htf Hnodup H H0.
  + revert H0; intros [= <-]. apply SemanticsBlocking.eval_Enil.
  + revert H0; intros [= <-]. apply SemanticsBlocking.eval_Enil.
  + inversion_clear H. eauto.
  + inversion_clear H. eauto.
  + inversion_clear H. simpl in H0.
    do 2 destruct expr_constraints; try discriminate.
    revert H0; intros [= <-]. rewrite map_app. apply SemanticsBlocking.eval_exprlist_app; eauto.
  + inversion_clear H. simpl in H0.
    do 2 destruct expr_constraints; try discriminate.
    revert H0; intros [= <-]. rewrite map_app. apply SemanticsBlocking.eval_exprlist_app; eauto.
  + inversion_clear H. simpl in H0.
    do 2 destruct expr_constraints; try discriminate.
    revert H0; intros [= <-]. rewrite map_app. apply SemanticsBlocking.eval_exprlist_app; eauto.
  + inversion_clear H. simpl in H0.
    do 2 destruct expr_constraints; try discriminate.
    revert H0; intros [= <-]. rewrite map_app. apply SemanticsBlocking.eval_exprlist_app; eauto.
  + inversion_clear H;
      simpl in H0; destruct list_assoc_pos eqn:Hi, expr_constraints eqn:Hc; try discriminate;
      revert H0; intros [= <-]; apply SemanticsBlocking.eval_Econs; try eauto;
      apply list_assoc_pos_Some in Hi;
      rewrite (list_assoc_nodup_injective _ _ _ _ Hnodup Hi H4);
      eapply SemanticsBlocking.eval_Binop_cmpu; eauto with nbtob semantics;
      simpl; unfold Int64.ltu; rewrite Coqlib.zlt_true; easy.
Qed.

Lemma eval_expr_None_constraints_not_verified:
  forall m e f exp constrs,
    list_assoc_nodup f.(fn_arrszvar) ->
    SemanticsNonBlocking.eval_expr m e f exp None ->
    Safety.expr_constraints f exp = Some constrs ->
    exists c, In c constrs /\ eval_expr m e f c (Some Vfalse).
Proof.
  induction exp; simpl; intros constrs Hnodup Heval Hconstrs; inversion Heval; eauto.
  all: only 1-4:
      (destruct (expr_constraints f exp1), (expr_constraints f exp2); try discriminate;
       revert Hconstrs; intros [= <-]; destruct H0 as [[H0 _] | [_ H0]];
       [ destruct (IHexp1 _ Hnodup H0 eq_refl) as [constr [Hc1 Hc2]];
         eexists; split; [ apply in_or_app |]; eauto
       | destruct (IHexp2 _ Hnodup H0 eq_refl) as [constr [Hc1 Hc2]];
         eexists; split; [ apply in_or_app |]; eauto ]).
  destruct (list_assoc_pos (fn_arrszvar f) i) eqn:Hi1,
      (expr_constraints f exp); try discriminate.
  revert Hconstrs; intros [= <-].
  eexists. split. simpl. left. reflexivity.
  apply list_assoc_pos_Some in Hi1.
  rewrite (list_assoc_nodup_injective _ _ _ _ Hnodup Hi1 H2).
  eapply eval_Binop_cmpu; eauto with semanticsnb.
  simpl. unfold Int64.ltu. rewrite Coqlib.zlt_false. reflexivity. assumption.
Qed.

Hint Resolve eval_expr_Some_constraints_verified : nbtob.
Hint Resolve eval_expr_None_constraints_not_verified : nbtob.

Lemma eval_exprlist_Some_constraints_verified:
  forall p m e f tf
    (Htf: transl_function (genv_of_program p) f = OK tf),
    forall le lv constrs,
    list_assoc_nodup f.(fn_arrszvar) ->
    SemanticsNonBlocking.eval_exprlist m e f le (Some lv) ->
    Safety.exprlist_constraints f le = Some constrs ->
    SemanticsBlocking.eval_exprlist m e tf constrs (map (fun _ => Vtrue) constrs).
Proof.
  induction le; intros.
  + revert H1; intros [= <-]. apply SemanticsBlocking.eval_Enil.
  + inversion H0. simpl in H1.
    destruct expr_constraints eqn:Hl, exprlist_constraints; try discriminate.
    revert H1; intros [= <-]. rewrite map_app.
    apply SemanticsBlocking.eval_exprlist_app; eauto with nbtob.
Qed.

Hint Resolve eval_exprlist_Some_constraints_verified : nbtob.

Lemma expr_constraints_eval_bool:
  forall m e f exp constrs r,
    list_assoc_nodup f.(fn_arrszvar) ->
    SemanticsNonBlocking.eval_expr m e f exp r ->
    Safety.expr_constraints f exp = Some constrs ->
    exists lb, eval_exprlist m e f constrs (Some (map Vbool lb)).
Proof.
  induction exp; simpl; intros constrs r Hnodup Heval H; rewrite_equalities;
    try (exists []; apply eval_Enil; eauto).
  inversion Heval; eauto.
  inversion Heval; eauto.
  all: only 1-4:
      (inversion_clear Heval;
       destruct (expr_constraints f exp1), (expr_constraints f exp2); try discriminate;
       revert H; intros [= <-]; [| destruct H0 as [[H0 H1] | [H0 H1]] ];
       specialize (IHexp1 _ _ Hnodup H0 eq_refl); destruct IHexp1 as [lb1 Hlb1];
       specialize (IHexp2 _ _ Hnodup H1 eq_refl); destruct IHexp2 as [lb2 Hlb2];
       exists (lb1 ++ lb2); rewrite map_app; apply eval_exprlist_app; eauto).
  destruct list_assoc_pos eqn:Hi; try discriminate.
  destruct expr_constraints eqn:Hconstrs; try discriminate.
  revert H; intros [= <-]. specialize IHexp with (1 := Hnodup).
  inversion_clear Heval; (edestruct IHexp as [lb Hlb]; [ eassumption | easy | ]);
  eexists; rewrite map_cons; (eapply eval_Econs_Some_e; [| eassumption]);
    eapply eval_Binop_cmpu; try eassumption; apply list_assoc_pos_Some in Hi;
    rewrite (list_assoc_nodup_injective (fn_arrszvar f) i _ szvar Hnodup Hi);
    try eassumption; simpl; unfold Int64.ltu.
  rewrite Coqlib.zlt_true; easy. rewrite Coqlib.zlt_false; easy.
Qed.

Lemma call_constraints_Internal_verified:
  forall p m e caller tcaller callee args constrs
    (Htcaller: transl_function (genv_of_program p) caller = OK tcaller),
    list_assoc_nodup caller.(fn_arrszvar) ->
    match_sig_args_typ caller.(fn_tenv) callee.(fn_sig).(sig_args) args ->
    valid_call m e caller (Internal callee) args ->
    call_constraints caller callee args = Some constrs ->
    constraints_verified m tcaller e constrs.
Proof.
  intros until constrs. intros Htcaller NODUP TYPE. intros.
  destruct_tf caller tcaller.
  unfold call_constraints in H0.
  unfold valid_call in H. unfold valid_function_call in H.
  pose proof callee.(fn_sig_arrszvar).
  revert args constrs TYPE H H0 H1.
  induction (fn_arrszvar callee); simpl; intros.
  + revert H0; intros [= <-]. easy.
  + destruct a as [id sz].
    destruct (index_of Pos.eq_dec _ id) as [i|] eqn:Hid,
        (index_of Pos.eq_dec _ sz) as [j|] eqn:Hsz; try discriminate. simpl in H0.
    destruct (nth_error args i) as [id0|] eqn:Hi,
          (nth_error args j) as [sz0|] eqn:Hj; try discriminate. simpl in H0.
    destruct (list_assoc_pos (fn_arrszvar caller) id0) as [sz1|] eqn:Hid0; try discriminate.
    destruct call_constraints_rec as [constrs0|] eqn:Hconstrs0; try discriminate.
    revert H0; intros [= <-]. split.
    - apply index_of_nth_error in Hid, Hsz.
      specialize H with (1 := or_introl (In (id, sz) l) (eq_refl (id, sz)))
                        (2 := Hid) (3 := Hsz).
      decompose [ex and] H. pose proof Hj as Hsz0.
      revert Hi Hj H0 H2; intros [= ->] [= ->] [= <-] [= <-].
      apply list_assoc_pos_Some in Hid0.
      specialize (list_assoc_nodup_injective _ _ _ _ NODUP Hid0 H3); intros [= <-].
      apply caller.(fn_tenv_arrszvar) in H3. destruct H3 as [_ [_ [_ H3]]].
      specialize (H1 _ _ _ _ (or_introl (In (id, sz) l) (eq_refl (id, sz))) Hid Hsz)
        as [_ [_ [_ H1]]]. rewrite <- (TYPE _ _ Hsz0) in H1.
      eapply SemanticsBlocking.eval_Binop_cmpu; eauto using well_typed_Vint64 with semantics.
      simpl. unfold Int64.ltu. rewrite Coqlib.zlt_false. reflexivity. lia.
    - unfold valid_sig_arrszvar in *. simpl in H1.
      specialize IHl with (1 := TYPE) (3 := Hconstrs0). apply IHl; eauto.
Qed.

Lemma eval_identlist_nth_error:
  forall m e f args vargs i id,
    eval_identlist e f args (Some vargs) ->
    nth_error args i = Some id ->
    exists v, nth_error vargs i = Some v /\ eval_expr m e f (Evar id) (Some v).
Proof.
  induction args; simpl; intros.
  + destruct i; simpl in H0; discriminate.
  + inversion H. destruct i.
    - rewrite_equalities. revert H0; intros [= <-]. eexists.
      split; simpl; eauto with semanticsnb.
    - rewrite_equalities. simpl. eauto.
Qed.

Lemma hd_error_in {A: Type}:
  forall (l: list A) x, hd_error l = Some x -> In x l.
Proof. induction l; simpl; intros; [| revert H; intros [= ->]; left]; easy. Qed.

Lemma nth_error_in_split {A: Type}:
  forall (l: list A) i x,
    nth_error l i = Some x ->
    exists l1 l2, l = l1 ++ x :: l2 /\ Datatypes.length l1 = i.
Proof.
  induction l; simpl; intros.
  + case i in H; discriminate.
  + destruct i.
    - revert H; intros [= <-]. exists [], l. eauto.
    - specialize (IHl _ _ H). destruct IHl as [l1 [l2 [[= ->] H0]]].
      exists (a :: l1), l2. rewrite <- H0. eauto.
Qed.

Lemma call_constraints_Internal_bool:
  forall m e caller callee args vargs vargs' constrs,
    valid_env_arrszvar e caller.(fn_arrszvar) ->
    eval_identlist e caller args (Some vargs) ->
    check_cast_args vargs callee.(fn_sig).(sig_args) = Some vargs' ->
    call_constraints caller callee args = Some constrs ->
    exists lb, eval_exprlist m e caller constrs (Some (map Vbool lb)).
Proof.
  intros until constrs. intros VENV EVAL TYPE. intros.
  unfold call_constraints in H. pose proof callee.(fn_sig_arrszvar).
  revert H H0. revert constrs.
  induction (fn_arrszvar callee); simpl; intros.
  + revert H; intros [= <-]. exists []. apply eval_Enil.
  + destruct a as [id sz].
    destruct (index_of Pos.eq_dec _ id) as [i|] eqn:Hid,
        (index_of Pos.eq_dec _ sz) as [j|] eqn:Hsz; try discriminate. simpl in H.
    destruct (nth_error args i) as [id0|] eqn:Hi,
          (nth_error args j) as [sz0|] eqn:Hj; try discriminate. simpl in H.
    destruct (list_assoc_pos (fn_arrszvar caller) id0) as [sz1|] eqn:Hid0; try discriminate.
    destruct call_constraints_rec as [constrs0|] eqn:Hconstrs; try discriminate.
    apply index_of_nth_error in Hid, Hsz. revert H; intros [= <-].
    specialize (IHl _ eq_refl).
    pose proof (eval_identlist_nth_error m _ caller _ _ _ _ EVAL Hj)
      as [v [Hv1 Hv2]].
    destruct (H0 _ _ _ _ (or_introl (In (id, sz) l) (eq_refl (id, sz))) Hid Hsz)
      as [w [_ [_ Htj]]].
    apply nth_error_in_split in Hv1, Htj.
    destruct Hv1 as [lv1 [lv2 [[= ->] Hlen]]].
    destruct Htj as [lt1 [lt2 [H' [= <-]]]]. rewrite H' in TYPE. clear w H'.
    revert Hsz Hj. generalize (Datatypes.length lt1). intros k. intros.
    clear EVAL. revert vargs' TYPE. revert lt1 Hlen Hsz Hj. induction lv1; simpl; intros.
    - apply eq_sym in Hlen. apply length_zero_iff_nil in Hlen. revert Hlen; intros [= ->].
      (* apply list_assoc_pos_Some in Hid0. *)
      (* unfold valid_sig_arrszvar in H0.
         specialize H0 with (1 := in_eq _ _) (2 := Hid) (3 := Hsz). *)
      simpl in TYPE. destruct (check_cast_args lv2 lt2); try discriminate.
      destruct (well_typed_value_bool v Tuint64) eqn:Hwt; try discriminate.
      clear TYPE. destruct v; try discriminate; destruct s; try discriminate.
      inversion_clear Hv2.
      apply list_assoc_pos_Some in Hid0. pose proof (VENV _ _ Hid0) as H'.
      destruct H' as [idarr [lv [len [Hval Hlen]]]].
      assert (forall (id szvar : ident) (i j : nat),
                 In (id, szvar) l ->
                 nth_error (fn_params callee) i = Some id ->
                 nth_error (fn_params callee) j = Some szvar ->
                 exists (b : bool) (t : typ),
                   nth_error (sig_args (fn_sig callee)) i = Some (Tarr b t) /\
                   nth_error (sig_args (fn_sig callee)) j = Some (Tint64 Unsigned)).
      intros. unfold valid_sig_arrszvar in H0. simpl in H0. eauto.
      specialize (IHl H3). destruct IHl as [c Hc].
      apply caller.(fn_tenv_arrszvar) in Hid0. destruct Hid0 as [_ [_ [_ H']]].
      eexists. rewrite map_cons. apply eval_Econs_Some_e.
      pose proof (well_typed_Vint64 len Unsigned).
      eapply eval_Binop_cmpu; eauto with semanticsnb. reflexivity. eassumption.
    - destruct lt1. discriminate. injection Hlen. clear Hlen. intro Hlen.
      specialize (IHlv1 _ Hlen Hsz Hj).
      destruct t; simpl in TYPE; destruct check_cast_args;
        try destruct a; try destruct i0, s; try destruct i1, s0;
        try discriminate; eauto.
Qed.

Lemma eval_exprlist_bool_all_true_or_not:
  forall m e f lexp lb,
    eval_exprlist m e f lexp (Some (map Vbool lb)) ->
    (forall exp, In exp lexp -> eval_expr m e f exp (Some (Vbool true)))
    \/ (exists exp, In exp lexp /\ eval_expr m e f exp (Some (Vbool false))).
Proof.
  induction lexp; simpl; intros; [tauto|].
  inversion H. clear e0 le H0 H1. apply eq_sym, map_eq_cons in H2.
  destruct H2 as [b [lb' [[= ->] [[= <-] [= <-]]]]].
  destruct b; [|eauto]. specialize (IHlexp _ H4). destruct IHlexp.
  + left. intros. destruct H1 as [[= ->] | H1]; eauto.
  + right. destruct H0 as [exp Hexp]. exists exp. tauto.
Qed.

Lemma index_of_rec_S:
  forall {A: Type} (eq_dec: forall x y: A, {x = y} + {x <> y})
         (l: list A) (n i: nat) (x: A),
    index_of_rec eq_dec l x n = Some i ->
    index_of_rec eq_dec l x (S n) = Some (S i).
Proof.
  induction l; simpl; intros. discriminate.
  destruct (eq_dec x a).
  + revert H; intros [= <-]. reflexivity.
  + eauto.
Qed.

Lemma NoDup_nth_error_index_of:
  forall {A: Type} (eq_dec: forall x y: A, {x = y} + {x <> y})
         (l: list A) (i: nat) (x: A),
    NoDup l ->
    nth_error l i = Some x ->
    index_of eq_dec l x = Some i.
Proof.
  induction l; simpl; intros.
  + rewrite Coqlib.nth_error_nil in H0. discriminate.
  + cbn. inversion_clear H.
    destruct (eq_dec x a).
    - revert e; intros [= <-].
      destruct i. reflexivity. cbn in H0.
      apply nth_error_In in H0. contradiction.
    - destruct i.
      * apply eq_sym in H0. injection H0. intro. contradiction.
      * specialize (IHl _ _ H2 H0).
        apply index_of_rec_S. assumption.
Qed.

Lemma call_constraints_Internal_correct:
  forall m e caller callee args constrs,
    valid_env_arrszvar e caller.(fn_arrszvar) ->
    call_constraints caller callee args = Some constrs ->
    (forall exp, In exp constrs -> eval_expr m e caller exp (Some (Vbool true))) ->
    valid_call m e caller (Internal callee) args.
Proof.
  unfold call_constraints, valid_call, valid_function_call. intros until callee.
  induction (fn_arrszvar callee); simpl; intros until constrs; intros VENV Hconstrs H.
  + contradiction.
  + intros id sz i j H0 Hid Hsz. destruct H0.
    - revert H0; intros [= ->].
      apply NoDup_nth_error_index_of
        with (eq_dec := Pos.eq_dec) (1 := fn_nodup_params callee) in Hid, Hsz.
      rewrite Hid, Hsz in Hconstrs. simpl in Hconstrs.
      destruct (nth_error args i) as [id0|] eqn:Hi,
            (nth_error args j) as [sz0|] eqn:Hj; try discriminate. simpl in Hconstrs.
      destruct list_assoc_pos as [sz1|] eqn:Hpos,
            call_constraints_rec eqn:Hconstrs' in Hconstrs; try discriminate.
      revert Hconstrs; intros [= <-]. apply list_assoc_pos_Some in Hpos.
      simpl in H. specialize (H _ (or_introl (In _ l0) eq_refl)).
      inversion_clear H. inversion_clear H0. inversion_clear H1.
      specialize (VENV id0 sz1 Hpos). destruct VENV as [idarr [lv [len [Harr Hlen]]]].
      rewrite H0 in Hlen. injection Hlen. clear Hlen. intros [= ->].
      destruct v1; try discriminate; destruct s; try discriminate. cbn in H2.
      injection H2. clear H2. intro H2. unfold negb in H2.
      destruct Int64.ltu eqn:H'. discriminate. clear H2.
      unfold Int64.ltu in H'. destruct Coqlib.zlt; try discriminate. clear H'.
      exists id0, sz0, sz1, i0, len.
      repeat split; assumption || lia.
    - destruct a as [id' sz'].
      destruct index_of, index_of in Hconstrs; try discriminate. simpl in Hconstrs.
      destruct nth_error, nth_error in Hconstrs; try discriminate. simpl in Hconstrs.
      destruct list_assoc_pos, call_constraints_rec eqn:Hconstrs' in Hconstrs; try discriminate.
      revert Hconstrs; intros [= <-]. simpl in H. eauto.
Qed.

Lemma call_constraints_Internal_not_verified:
  forall m e caller callee args vargs vargs' constrs,
    valid_env_arrszvar e caller.(fn_arrszvar) ->
    eval_identlist e caller args (Some vargs) ->
    check_cast_args vargs callee.(fn_sig).(sig_args) = Some vargs' ->
    ~valid_call m e caller (Internal callee) args ->
    call_constraints caller callee args = Some constrs ->
    exists c, In c constrs /\ eval_expr m e caller c (Some Vfalse).
Proof.
  intros until constrs. intros VENV EVAL TYPE. intros.
  specialize call_constraints_Internal_bool
    with (1 := VENV) (2 := EVAL) (3 := TYPE) (4 := H0) as [lb Hlb].
  apply eval_exprlist_bool_all_true_or_not in Hlb. destruct Hlb as [Hlb | Hlb].
  specialize call_constraints_Internal_correct
    with (1 := VENV) (2 := H0) (3 := Hlb) as Hvalid. contradiction.
  eauto.
Qed.

Theorem transl_cont_destruct_preservation:
  forall ge f k tk,
    transl_cont ge f k = OK tk ->
    transl_cont ge None (SemanticsNonBlocking.destructCont k) = OK (SemanticsBlocking.destructCont tk).
Proof.
  induction k; simpl; intros.
  + revert H; intros [= <-]. reflexivity.
  + destruct f, transl_stmt; try discriminate.
    destruct (transl_cont ge (Some f) k); try discriminate.
    revert H; intros [= <-]. simpl. eauto.
  + destruct (transl_function ge f0), (transl_cont ge (Some f0) k); try discriminate.
    revert H; intros [= <-]. reflexivity.
  + destruct f, transl_stmt; try discriminate.
    destruct (transl_cont ge (Some f) k); try discriminate.
    revert H; intros [= <-]. simpl. eauto.
Qed.

Lemma valid_call_preservation:
  forall ge m e args f fd tf tfd,
    transl_function ge f = OK tf ->
    transl_fundef ge fd = OK tfd ->
    valid_call m e f fd args ->
    valid_call m e tf tfd args.
Proof.
  intros. destruct fd; simpl in H0, H1.
  + destruct (transl_function ge f0) eqn:Hf0; try discriminate.
    revert H0; intros [= <-]. simpl.
    intros id sz i j Hszvar Hpi Hpj.
    unfold transl_function in Hf0. destruct transl_stmt; try discriminate.
    revert Hf0; intros [= <-]. simpl in Hpj, Hpi, Hszvar.
    specialize (H1 id sz i j Hszvar Hpi Hpj).
    unfold transl_function in H. destruct transl_stmt; try discriminate.
    revert H; intros [= <-]. simpl. eassumption.
  + revert H0; intros [= <-]. easy.
Qed.

Fixpoint list_assoc_nodup_cont (k: cont) :=
  match k with
  | Kstop => True
  | Kloop _ k | Kseq _ k => list_assoc_nodup_cont k
  | Kreturnto _ _ f _ k =>
      list_assoc_nodup f.(fn_arrszvar) /\ list_assoc_nodup_cont k
  end.

Definition list_assoc_nodup_fundef fd :=
  match fd with
  | Internal f => list_assoc_nodup f.(fn_arrszvar)
  | External ef => True
  end.

Definition list_assoc_nodup_genv (ge: genv) :=
  Forall (fun x => list_assoc_nodup_fundef (snd x)) (PTree.elements ge).

Inductive match_states (p: program) : SemanticsNonBlocking.state -> SemanticsBlocking.state -> Prop :=
| match_states_State: forall m e f llvl s k tf ts tk
    (TRFUNC: transl_function (genv_of_program p) f = OK tf)
    (TRSTMT: transl_stmt (genv_of_program p) f s = OK ts)
    (TRCONT: transl_cont (genv_of_program p) (Some f) k = OK tk)
    (NDCONT: list_assoc_nodup_cont k)
    (NDGENV: list_assoc_nodup_genv (genv_of_program p)),
    match_states p (State m e f llvl s k) (SemanticsBlocking.State m e tf ts tk)
| match_states_Callstate_Internal: forall m f args k tfd tk
    (TRFD  : transl_fundef (genv_of_program p) (Internal f) = OK tfd)
    (TRCONT: transl_cont (genv_of_program p) None k = OK tk)
    (NDCONT: list_assoc_nodup_cont k)
    (NDGENV: list_assoc_nodup_genv (genv_of_program p)),
    match_states p (Callstate m (Internal f) args k) (SemanticsBlocking.Callstate m tfd args tk)
| match_states_Callstate_External: forall m f args k tfd tk
    (TRFD  : transl_fundef (genv_of_program p) (External f) = OK tfd)
    (TRCONT: transl_cont (genv_of_program p) None k = OK tk)
    (NDCONT: list_assoc_nodup_cont k)
    (NDGENV: list_assoc_nodup_genv (genv_of_program p)),
    match_states p (Callstate m (External f) args k) (SemanticsBlocking.Callstate m tfd args tk)
| match_states_Returnstate: forall m v k tk
    (TRCONT: transl_cont (genv_of_program p) None k = OK tk)
    (NDCONT: list_assoc_nodup_cont k)
    (NDGENV: list_assoc_nodup_genv (genv_of_program p)),
    match_states p (Returnstate m v k) (SemanticsBlocking.Returnstate m v tk).

Hint Constructors match_states : nbtob.

Lemma is_Kreturnto_preservation:
  forall ge fopt k tk,
    transl_cont ge fopt k = OK tk ->
    is_Kreturnto k ->
    SemanticsBlocking.is_Kreturnto tk.
Proof.
  destruct k; simpl; intros; try contradiction.
  destruct transl_cont, transl_function; try discriminate.
  revert H; intros [= <-]. easy.
Qed.

Lemma list_assoc_nodup_genv_of_program:
  forall p,
    list_assoc_nodup_genv (genv_of_program p) <->
      Forall (fun x => list_assoc_nodup_fundef (snd x)) p.(prog_defs).
Proof.
  split; intro.
  + apply Forall_forall. intros.
    unfold list_assoc_nodup_genv in H. eapply Forall_forall in H.
    eassumption. unfold genv_of_program.
    apply (build_env_correct_empty p.(prog_defs) p.(prog_nodup)). assumption.
  + apply Forall_forall. intros.
    apply (build_env_correct_empty p.(prog_defs) p.(prog_nodup)) in H0.
    eapply Forall_forall in H; eassumption.
Qed.

Ltac destruct_transl_program p :=
  match goal with
  | H: (transl_program p = OK _) |- _ =>
      (* destruct p as [ prog_defs prog_main prog_nodup prog_main_exists ]; *)
      unfold transl_program in H; simpl in H; revert H;
      generalize (transl_fundefs_list_assoc_nodup (genv_of_program p) p.(prog_defs) p.(prog_nodup));
      generalize (transl_fundefs_eq_map_fst (genv_of_program p) p.(prog_defs));
      destruct (transl_fundefs (genv_of_program p) p.(prog_defs)) eqn:Hfd;
      intros Hmapfst Hnodup [= <-];
      destruct p as [ prog_defs prog_main prog_nodup prog_main_exists ]
  end.

Lemma list_assoc_nodup_genv_preservation:
  forall p tp,
    transl_program p = OK tp ->
    list_assoc_nodup_genv (genv_of_program p) ->
    list_assoc_nodup_genv (genv_of_program tp).
Proof.
  intros. destruct_transl_program p.
  apply list_assoc_nodup_genv_of_program in H0. simpl in H0.
  apply list_assoc_nodup_genv_of_program.
  apply Forall_forall. simpl. intros. destruct x as [id fd].
  destruct (proj1 (in_list_map_error_iff _ _ _ _ Hfd) H) as [(id', fd') H1].
  simpl in H1. destruct H1 as [H1 Hfd']. destruct transl_fundef eqn:Htfd'; try discriminate.
  revert H1; intros [= <-]. revert H2; intros [= <-]. simpl.
  pose proof (proj1 (Forall_forall _ _) H0 _ Hfd'). simpl in H1. destruct fd'.
  + simpl in Htfd'. destruct transl_function eqn:Htf; try discriminate.
    revert Htfd'; intros [= <-]. simpl. destruct f0. unfold transl_function in Htf.
    simpl in Htf. destruct transl_stmt; try discriminate.
    revert Htf; intros [= <-]. assumption.
  + simpl in Htfd'. revert Htfd'; intros [= <-]. assumption.
Qed.

Lemma list_assoc_nodup_destruct_preservation:
  forall k,
    list_assoc_nodup_cont k ->
    list_assoc_nodup_cont (SemanticsNonBlocking.destructCont k).
Proof. induction k; eauto. Qed.

Theorem transl_stmt_sem_preservation:
  forall p tp s s' ts t,
    transl_program p = OK tp ->
    match_states p s ts ->
    step_events (genv_of_program p) s t s' ->
    exists ts', plus SemanticsBlocking.step_events (genv_of_program tp) ts t ts' /\ match_states p s' ts'.
Proof.
  intros. destruct s. destruct s.
  (*  Sskip  *)
  + destruct H1. inversion H0. rewrite_equalities. revert H1; intros [= ->].
    inversion H2; rewrite_equalities; simpl in TRFUNC, TRSTMT, TRCONT.
    (*  Sskip, Kseq  *)
    - destruct (transl_stmt _ f s) eqn:Ts, (transl_cont _ (Some f) k) eqn:Tk; try discriminate.
      revert TRSTMT TRCONT; intros [= <-] [= <-].
      eexists. split; [ apply plus_one; split | ]; eauto with nbtob semantics.
    (*  Sskip, Kloop  *)
    - destruct (transl_stmt _ f s) eqn:Ts, (transl_cont _ (Some f) k) eqn:Tk; try discriminate.
      revert TRSTMT TRCONT; intros [= <-] [= <-].
      eexists. split. apply plus_one. split. reflexivity.
      apply SemanticsBlocking.step_skip_loop. eapply match_states_State; try eassumption.
      simpl. rewrite Ts. reflexivity.
    (*  Sskip, Kreturnto  *)
    - revert TRSTMT; intros [= <-]. eexists. split. apply plus_one. split. reflexivity.
      apply SemanticsBlocking.step_skip_returnto. eapply is_Kreturnto_preservation; eassumption.
      unfold transl_function in TRFUNC. destruct transl_stmt; try discriminate.
      revert TRFUNC; intros [= <-]. assumption.
      apply match_states_Returnstate; try assumption. destruct k; easy.
  (*  Sassign  *)
  + destruct H1. inversion H0. rewrite_equalities. revert H1; intros [= ->].
    inversion H2; rewrite_equalities; simpl in TRSTMT, TRCONT.
    (*  Sassign, cas normal  *)
    - destruct (guard_stmt_with_expr f exp (Sassign id exp)) eqn:Hg; try discriminate.
      revert TRSTMT; intros [= <-]. unfold guard_stmt_with_expr in Hg.
      destruct (expr_constraints f exp) eqn:Hconstrs; try discriminate.
      revert Hg; intros [= <-].
      pose proof (eval_expr_Some_constraints_verified _ _ _ _ _ _ _ _ TRFUNC f.(fn_nodup) H10 Hconstrs).
      pose proof TRFUNC. unfold transl_function in TRFUNC.
      destruct transl_stmt; try discriminate. revert TRFUNC; intros [= <-].
      clear Hconstrs H0. induction l; simpl.
      * eexists. split. apply plus_one. split. reflexivity. apply SemanticsBlocking.step_assign.
        eapply transl_expr_sem_preservation; eassumption.
        eapply match_states_State; eauto.
      * inversion_clear H1. destruct in_dec. eauto.
        specialize (IHl H4). destruct IHl as [ts [Hts1 Hts2]]. simpl. eexists.
        split; [ eapply plus_left; try split |]; eauto using plus_star with semantics.
    (*  Sassign id exp, exp s'évalue en None  *)
    - unfold guard_stmt_with_expr in TRSTMT.
      destruct expr_constraints eqn:Hconstrs; try discriminate.
      revert TRSTMT; intros [= <-].
      destruct (eval_expr_None_constraints_not_verified _ _ _ _ _ f.(fn_nodup) H10 Hconstrs)
        as [c [Hc1 Hc2]].
      destruct (in_split_last expr_eq_dec c l Hc1) as [c1 [c2 [[= ->] Hnotin]]].
      pose proof TRFUNC. unfold transl_function in TRFUNC.
      destruct transl_stmt; try discriminate. revert TRFUNC; intros [= <-].
      destruct (expr_constraints_eval_bool _ _ _ _ _ _ f.(fn_nodup) H10 Hconstrs) as [lb Hlb].
      clear Hconstrs H0. revert lb Hlb. induction c1; simpl; intros.
      * eexists. split. destruct in_dec; try contradiction.
        simpl. apply plus_one. split. reflexivity. apply SemanticsBlocking.step_ifthenelse.
        eapply transl_expr_sem_preservation; eassumption.
        apply match_states_State; easy.
      * inversion Hlb. apply eq_sym in H4. apply map_eq_cons in H4.
        destruct H4 as [b [tl [[= ->] [[= <-] [= <-]]]]]. destruct Hc1 as [[= ->] | Hc1].
        ** destruct in_dec. eauto. pose proof (in_elt c c1 c2). contradiction.
        ** destruct in_dec. eauto. destruct b.
           -- specialize (IHc1 Hc1 tl H6). destruct IHc1 as [ts' [Hts'1 Hts'2]].
              eexists. split; [ eapply plus_left; try split |];
                eauto using plus_star with nbtob semantics.
           -- eexists. split; [ eapply plus_one; split |];
                eauto using plus_star with nbtob semantics.
  (*  Sarr_assign  *)
  + destruct H1. inversion H0. rewrite_equalities. revert H1; intros [= ->].
    inversion H2; rewrite_equalities; simpl in TRSTMT.
    (*  Sarr_assign, cas normal  *)
    - destruct list_assoc_pos eqn:Hsize, (expr_constraints f idx) eqn:Hconstrs_idx,
            (expr_constraints f exp) eqn:Hconstrs_exp; try discriminate.
      revert TRSTMT; intros [= <-].
      pose proof (eval_expr_Some_constraints_verified _ _ _ _ _ _ _ _ TRFUNC f.(fn_nodup) H11 Hconstrs_idx).
      pose proof (eval_expr_Some_constraints_verified _ _ _ _ _ _ _ _ TRFUNC f.(fn_nodup) H15 Hconstrs_exp).
      pose proof TRFUNC. unfold transl_function in TRFUNC.
      apply list_assoc_pos_Some in Hsize.
      rewrite (list_assoc_nodup_injective (fn_arrszvar f) id _ szvar f.(fn_nodup) Hsize H12).
      destruct transl_stmt; try discriminate. revert TRFUNC; intros [= <-].
      clear Hconstrs_idx Hconstrs_exp H0. induction l; simpl; intros.
      * induction l0; simpl; intros.
        ** eexists. split. eapply plus_left. split. reflexivity.
           apply SemanticsBlocking.step_ifthenelse.
           eapply SemanticsBlocking.eval_Binop_cmpu; eauto with nbtob semantics.
           simpl. unfold Int64.ltu. rewrite Coqlib.zlt_true. reflexivity. assumption.
           inversion_clear H13.
           apply star_one. split. all: eauto with nbtob semantics.
        ** inversion H3. destruct in_dec. eauto.
           destruct (IHl0 H9) as [ts' [Hts'1 Hts'2]].
           eexists. split. eapply plus_left. split.
           all: eauto using plus_star with semantics.
      * inversion H1. destruct in_dec. eauto.
        destruct (IHl H9) as [ts' [Hts'1 Hts'2]].
        eexists. split. eapply plus_left. split.
        all: eauto using plus_star with semantics.
    (*  Sarr_assign id idx exp, idx dépasse la taille du tableau  *)
    - destruct list_assoc_pos eqn:Hsize, (expr_constraints f idx) eqn:Hconstrs_idx,
            (expr_constraints f exp) eqn:Hconstrs_exp; try discriminate.
      revert TRSTMT; intros [= <-].
      apply list_assoc_pos_Some in Hsize.
      rewrite (list_assoc_nodup_injective _ _ _ _ f.(fn_nodup) Hsize H12).
      pose proof (eval_expr_Some_constraints_verified _ _ _ _ _ _ _ _ TRFUNC f.(fn_nodup) H11 Hconstrs_idx).
      pose proof TRFUNC. unfold transl_function in TRFUNC.
      destruct transl_stmt; try discriminate. revert TRFUNC; intros [= <-].
      clear Hconstrs_idx H0. induction l; simpl; intros.
      2: { inversion_clear H1. destruct in_dec. eauto.
           destruct (IHl H4) as [ts' [Hts'1 Hts'2]].
           eexists. split. eapply plus_left. split. reflexivity.
           apply SemanticsBlocking.step_ifthenelse. eassumption. apply plus_star. eauto.
           reflexivity. assumption. }
      destruct (expr_constraints_eval_bool _ _ _ _ _ _ f.(fn_nodup) H14 Hconstrs_exp) as [lb Hlb].
      clear Hconstrs_exp. revert lb Hlb. induction l0; simpl; intros.
      * eexists. split. apply plus_one. split. reflexivity.
        apply SemanticsBlocking.step_ifthenelse.
        eapply SemanticsBlocking.eval_Binop_cmpu; eauto with nbtob semantics.
        simpl. unfold Int64.ltu. rewrite Coqlib.zlt_false. reflexivity. assumption.
        apply match_states_State; easy.
      * inversion Hlb. apply eq_sym in H5. apply map_eq_cons in H5.
        destruct H5 as [b [tl [[= ->] [[= <-] [= <-]]]]].
        destruct (IHl0 _ H7) as [ts' [Hts'1 Hts'2]].
        destruct in_dec. eauto. destruct b; eexists; split.
        eapply plus_left. split. reflexivity.
        eapply SemanticsBlocking.step_ifthenelse, transl_expr_sem_preservation; eassumption.
        apply plus_star. eassumption. reflexivity. assumption.
        apply plus_one. split. all: eauto with nbtob semantics.
    (*  Sarr_assign id idx exp, idx s'évalue à None  *)
    - destruct list_assoc_pos eqn:Hsize, (expr_constraints f idx) eqn:Hconstrs_idx,
            (expr_constraints f exp) eqn:Hconstrs_exp; try discriminate.
      revert TRSTMT; intros [= <-].
      apply list_assoc_pos_Some in Hsize.
      rewrite (list_assoc_nodup_injective _ _ _ _ f.(fn_nodup) Hsize H12).
      pose proof TRFUNC. unfold transl_function in TRFUNC.
      destruct transl_stmt; try discriminate. revert TRFUNC; intros [= <-].
      destruct (eval_expr_None_constraints_not_verified _ _ _ _ _ f.(fn_nodup) H11 Hconstrs_idx)
        as [c [H' Hc]].
      destruct (expr_constraints_eval_bool _ _ _ _ _ _ f.(fn_nodup) H11 Hconstrs_idx) as [lb1 Hlb1].
      destruct (expr_constraints_eval_bool _ _ _ _ _ _ f.(fn_nodup) H14 Hconstrs_exp) as [lb2 Hlb2].
      rewrite app_assoc. pose proof (eval_exprlist_app _ _ _ _ _ _ _ Hlb1 Hlb2) as Hlb.
      rewrite <- map_app in Hlb. generalize Hlb. generalize (lb1 ++ lb2).
      clear lb1 lb2 Hlb1 Hlb2 Hlb.
      (* apply or_introl with (B := In c (l0 ++ [Ebinop_cmpu Oltu OInt64 idx (Evar szvar)])) in H'. *)
      apply or_introl with (B := In c l0) in H'.
      apply in_or_app in H'.
      apply (in_split_last expr_eq_dec) in H'. destruct H' as [l1 [l2 [[= ->] Hnotin]]].
      clear Hconstrs_idx Hconstrs_exp H0. induction l1; simpl; intros.
      * destruct in_dec.
        apply in_app_or in i0. destruct i0. contradiction.
        simpl in H0. destruct H0 as [[= <-] | H0]; try contradiction.
        inversion Hc. pose proof (eval_expr_injective _ _ _ _ _ _ f.(fn_nodup) H11 H5). discriminate.
        eexists. split. apply plus_one. split. all: eauto with nbtob semantics.
      * inversion Hlb. apply eq_sym in H4. apply map_eq_cons in H4.
        destruct H4 as [b [tl [[= ->] [[= <-] [= <-]]]]].
        destruct (IHl1 _ H6) as [ts' [Hts'1 Hts'2]].
        destruct in_dec. eauto. destruct b; eexists; split.
        eapply plus_left. split. reflexivity.
        eapply SemanticsBlocking.step_ifthenelse, transl_expr_sem_preservation; eassumption.
        apply plus_star. eauto. reflexivity. assumption.
        apply plus_one. split. all: eauto with nbtob semantics.
    (*  Sarr_assign id idx exp, exp s'évalue à None  *)
    - destruct list_assoc_pos eqn:Hsize, (expr_constraints f idx) eqn:Hconstrs_idx,
            (expr_constraints f exp) eqn:Hconstrs_exp; try discriminate.
      revert TRSTMT; intros [= <-].
      apply list_assoc_pos_Some in Hsize.
      rewrite (list_assoc_nodup_injective _ _ _ _ f.(fn_nodup) Hsize H12).
      pose proof (eval_expr_Some_constraints_verified _ _ _ _ _ _ _ _ TRFUNC f.(fn_nodup) H11 Hconstrs_idx).
      pose proof TRFUNC. unfold transl_function in TRFUNC.
      destruct transl_stmt; try discriminate. revert TRFUNC; intros [= <-].
      clear Hconstrs_idx H0. induction l; simpl; intros.
      2: { inversion H1. destruct in_dec. eauto.
           destruct (IHl H8) as [ts' [Hts'1 Hts'2]].
           eexists. split. eapply plus_left. split. reflexivity.
           apply SemanticsBlocking.step_ifthenelse. eassumption.
           apply plus_star. eauto. reflexivity. assumption. }
      destruct (eval_expr_None_constraints_not_verified _ _ _ _ _ f.(fn_nodup) H15 Hconstrs_exp)
        as [c [H' Hc]].
      destruct (expr_constraints_eval_bool _ _ _ _ _ _ f.(fn_nodup) H15 Hconstrs_exp) as [lb Hlb].
      apply (in_split_last expr_eq_dec) in H'. destruct H' as [l1 [l2 [[= ->] Hnotin]]].
      clear Hconstrs_exp. revert lb Hlb. induction l1; simpl; intros.
      * destruct in_dec.
        apply in_app_or in i1. destruct i1. contradiction.
        simpl in H0. destruct H0 as [[= <-] | H0]; try contradiction.
        inversion Hc.
        specialize (eval_expr_injective _ _ _ _ _ _ f.(fn_nodup) H6 H11); intros [= ->].
        specialize (eval_expr_injective _ _ _ _ _ _ f.(fn_nodup) H9 H13); intros [= ->].
        simpl in H10. unfold Int64.ltu in H10. rewrite Coqlib.zlt_true in H10.
        discriminate. eassumption.
        eexists. split. apply plus_one. split. all: eauto with nbtob semantics.
      * inversion Hlb. apply eq_sym in H5. apply map_eq_cons in H5.
        destruct H5 as [b [tl [[= ->] [[= <-] [= <-]]]]].
        destruct (IHl1 _ H7) as [ts' [Hts'1 Hts'2]].
        destruct in_dec. eauto. destruct b; eexists; split.
        eapply plus_left. split. reflexivity.
        eapply SemanticsBlocking.step_ifthenelse, transl_expr_sem_preservation; eassumption.
        apply plus_star. eauto. reflexivity. assumption.
        apply plus_one. split. all: eauto with nbtob semantics.
  (*  Scall_internal  *)
  + destruct H1. inversion H0. rewrite_equalities. revert H1; intros [= ->].
    inversion H2; rewrite_equalities; simpl in TRSTMT.
    (*  Scall internal, cas normal  *)
    - rewrite H11 in TRSTMT.
      destruct call_constraints eqn:Hconstrs; try discriminate.
      revert TRSTMT; intros [= <-]. destruct_transl_program p; simpl in *.
      apply PTree.elements_correct in H11.
      pose proof (proj2 (build_env_correct_empty prog_defs prog_nodup _) H11).
      destruct (in_list_map_error _ _ _ _ Hfd H) as [y [Hy1 Hy2]].
      destruct transl_fundef eqn:Htfd; try discriminate. revert Hy1; intros [= <-].
      pose proof (call_constraints_Internal_verified _ _ _ _ _ _ _ _ TRFUNC f.(fn_nodup) H14 H12 Hconstrs).
      clear Hconstrs H0; induction l; simpl.
      2: { destruct H1. specialize (IHl H1). destruct IHl as [ts' [Hts'1 Hts'2]].
           destruct in_dec. eexists. split; eauto.
           eexists. split. eapply plus_left. split. reflexivity.
           apply SemanticsBlocking.step_ifthenelse. unfold transl_function in TRFUNC.
           destruct transl_stmt; try discriminate. revert TRFUNC; intros [= <-].
           eassumption. apply plus_star. eauto. reflexivity. assumption. }
      pose proof TRFUNC. unfold transl_function in TRFUNC.
      simpl in TRFUNC; destruct (transl_stmt _ _ (fn_body f)); try discriminate.
      revert TRFUNC; intros [= <-]. pose proof Htfd; simpl in Htfd.
      destruct (transl_function _ f') eqn:Htf; try discriminate.
      revert Htfd; intros [= <-]. unfold transl_function in Htf.
      destruct (transl_stmt _ _ (fn_body f')); try discriminate.
      revert Htf; intros [= <-].
      eexists; split; [apply plus_one; split; try reflexivity|].
      eapply SemanticsBlocking.step_call_internal.
      apply PTree.elements_complete.
      apply (proj1 (build_env_correct_empty _ Hnodup _) Hy2).
      eapply valid_call_preservation; eassumption. eassumption. eassumption.
      exact (identlist_sem_preservation _ _ _ _ _ _ H0 H15). eassumption.
      apply match_states_Callstate_Internal; try assumption.
      simpl. rewrite TRCONT, H0. reflexivity. split. exact f.(fn_nodup). assumption.
    (* Scall external, cas normal *)
    - rewrite H11 in TRSTMT. revert TRSTMT; intros [= <-].
      destruct_transl_program p; simpl in *.
      apply PTree.elements_correct in H11.
      pose proof (proj2 (build_env_correct_empty prog_defs prog_nodup _) H11).
      destruct (in_list_map_error _ _ _ _ Hfd H) as [y [Hy1 Hy2]].
      destruct transl_fundef eqn:Htfd; try discriminate. revert Hy1; intros [= <-].
      revert Htfd; intros [= <-].
      pose proof TRFUNC. unfold transl_function in TRFUNC.
      simpl in TRFUNC; destruct (transl_stmt _ _ (fn_body f)); try discriminate.
      revert TRFUNC; intros [= <-].
      eexists. split. apply plus_one. split. reflexivity.
      eapply SemanticsBlocking.step_call_external.
      apply PTree.elements_complete.
      apply (proj1 (build_env_correct_empty _ Hnodup _) Hy2). eassumption. eassumption.
      exact (identlist_sem_preservation _ _ _ _ _ _ H1 H14). eassumption.
      unfold genv_of_program in *. simpl in *. eassumption.
      apply match_states_State; try eassumption. reflexivity.
    (*  Scall, appel non valide  *)
    - rewrite H11 in TRSTMT. destruct fd; simpl in H13; try contradiction.
      destruct call_constraints eqn:Hconstrs; try discriminate.
      revert TRSTMT; intros [= <-]. destruct_transl_program p. simpl in *.
      specialize call_constraints_Internal_bool with
        (1 := H12) (2 := H16) (3 := H17) (4 := Hconstrs). intros [lb Hlb].
      specialize call_constraints_Internal_not_verified with
        (1 := H12) (2 := H16) (3 := H17) (4 := H13) (5 := Hconstrs).
      intros [c [Hc1 Hc2]]. apply (in_split_last expr_eq_dec) in Hc1.
      destruct Hc1 as [l1 [l2 [[= ->] Hc1]]].
      clear H0 Hconstrs. revert lb Hlb. induction l1; simpl; intros.
      * destruct in_dec. contradiction.
        inversion Hlb. apply eq_sym in H1. apply map_eq_cons in H1.
        destruct H1 as [b [tl [[= ->] [[= <-] [= <-]]]]]. clear H H0 Hlb.
        eexists. split. eapply plus_one. split. reflexivity.
        eapply SemanticsBlocking.step_ifthenelse, transl_expr_sem_preservation. eassumption.
        unfold transl_function in TRFUNC. destruct transl_stmt; try discriminate.
        revert TRFUNC; intros [= <-]. exact Hc2.
        apply match_states_State; easy.
      * inversion Hlb. apply eq_sym in H1. apply map_eq_cons in H1.
        destruct H1 as [b [tl [[= ->] [[= <-] [= <-]]]]]. clear H H0 Hlb.
        destruct in_dec. eauto. destruct (IHl1 _ H4) as [ts' [Hts'1 Hts'2]].
        destruct b.
        ** eexists. split. eapply plus_left. split. reflexivity.
           eapply SemanticsBlocking.step_ifthenelse, transl_expr_sem_preservation. eassumption.
           unfold transl_function in TRFUNC. destruct transl_stmt; try discriminate.
           revert TRFUNC; intros [= <-]. eassumption.
           apply plus_star. eassumption. reflexivity. assumption.
        ** eexists. split. apply plus_one. split. reflexivity.
           eapply SemanticsBlocking.step_ifthenelse, transl_expr_sem_preservation. eassumption.
           unfold transl_function in TRFUNC. destruct transl_stmt; try discriminate.
           revert TRFUNC; intros [= <-]. eassumption.
           apply match_states_State; easy.
  (*  Sreturn  *)
  + destruct H1. inversion H0. rewrite_equalities. revert H1; intros [= ->].
    inversion H2; rewrite_equalities; simpl in TRSTMT.
    (*  Sreturn, cas normal  *)
    - destruct guard_stmt_with_expr eqn:Hg; try discriminate. revert TRSTMT; intros [= <-].
      unfold guard_stmt_with_expr in Hg.
      destruct (expr_constraints f exp) eqn:Hconstrs; try discriminate.
      revert Hg; intros [= <-].
      pose proof (eval_expr_Some_constraints_verified _ _ _ _ _ _ _ _ TRFUNC f.(fn_nodup) H9 Hconstrs).
      pose proof TRFUNC. destruct_tf f tf.
      clear Hconstrs H0. induction l; simpl.
      * eexists. split. apply plus_one. split. reflexivity.
        eapply SemanticsBlocking.step_return; try eassumption.
        eauto using transl_expr_sem_preservation with semantics.
        apply match_states_Returnstate. exact (transl_cont_destruct_preservation _ _ _ _ TRCONT).
        exact (list_assoc_nodup_destruct_preservation _ NDCONT). assumption.
      * inversion H1. destruct in_dec. eauto.
        specialize (IHl H7). destruct IHl as [ts' [Hts'1 Hts'2]].
        eexists. split. eapply plus_left. split. reflexivity.
        apply SemanticsBlocking.step_ifthenelse. eassumption.
        apply plus_star. eassumption. reflexivity. assumption.
    (*  Sreturn exp, exp s'évalue à None  *)
    - destruct guard_stmt_with_expr eqn:Hg; try discriminate. revert TRSTMT; intros [= <-].
      unfold guard_stmt_with_expr in Hg.
      destruct (expr_constraints f exp) eqn:Hconstrs; try discriminate.
      revert Hg; intros [= <-].
      destruct (eval_expr_None_constraints_not_verified _ _ _ _ _ f.(fn_nodup) H9 Hconstrs)
        as [c [Hc1 Hc2]].
      destruct (in_split_last expr_eq_dec c l Hc1) as [c1 [c2 [[= ->] Hnotin]]].
      pose proof TRFUNC. destruct_tf f tf.
      destruct (expr_constraints_eval_bool _ _ _ _ _ _ f.(fn_nodup) H9 Hconstrs) as [lb Hlb].
      clear Hconstrs H0. revert lb Hlb. induction c1; simpl; intros.
      * eexists. split. destruct in_dec; try contradiction.
        simpl. apply plus_one. split. reflexivity. apply SemanticsBlocking.step_ifthenelse.
        eapply transl_expr_sem_preservation; eassumption.
        apply match_states_State; easy.
      * inversion Hlb. apply eq_sym in H3. apply map_eq_cons in H3.
        destruct H3 as [b [tl [[= ->] [[= <-] [= <-]]]]]. destruct Hc1 as [[= ->] | Hc1].
        ** destruct in_dec. eauto. pose proof (in_elt c c1 c2). contradiction.
        ** destruct in_dec. eauto. destruct b.
           -- specialize (IHc1 Hc1 tl H5). destruct IHc1 as [ts' [Hts'1 Hts'2]].
              eexists. split. eapply plus_left. split.
              all: eauto using plus_star with nbtob semantics.
           -- eexists. split. apply plus_one. split. all: eauto with nbtob semantics.
  (*  Sseq  *)
  + destruct H1. inversion H0. rewrite_equalities. revert H1; intros [= ->].
    inversion H2; rewrite_equalities; simpl in TRSTMT.
    destruct (transl_stmt _ f s0) eqn:Hs0, (transl_stmt _ f s3) eqn:Hs3; try discriminate.
    revert TRSTMT; intros [= <-].
    eexists. split. apply plus_one. split. reflexivity.
    apply SemanticsBlocking.step_seq. apply match_states_State; try assumption.
    simpl. rewrite Hs3, TRCONT. reflexivity.
  (*  Sifthenelse  *)
  + destruct H1. inversion H0. rewrite_equalities. revert H1; intros [= ->].
    inversion H2; rewrite_equalities; simpl in TRSTMT.
    (*  Sifthenelse, cas normal  *)
    - destruct (transl_stmt _ f s0) eqn:Hs0, (transl_stmt _ f s3) eqn:Hs3; try discriminate.
      simpl in TRSTMT. destruct guard_stmt_with_expr eqn:Hg; try discriminate.
      revert TRSTMT; intros [= <-].
      unfold guard_stmt_with_expr in Hg. destruct expr_constraints eqn:Hconstrs; try discriminate.
      revert Hg; intros [= <-].
      pose proof (eval_expr_Some_constraints_verified _ _ _ _ _ _ _ _ TRFUNC f.(fn_nodup) H11 Hconstrs).
      pose proof TRFUNC. unfold transl_function in TRFUNC.
      destruct transl_stmt; try discriminate. revert TRFUNC; intros [= <-].
      clear H0 Hconstrs. induction l; simpl; intros.
      * eexists. split. apply plus_one. split. reflexivity.
        eapply SemanticsBlocking.step_ifthenelse, transl_expr_sem_preservation; eassumption.
        destruct b; apply match_states_State; eassumption.
      * inversion H1. destruct in_dec. eauto.
        specialize (IHl H8). destruct IHl as [ts' [Hts'1 Hts'2]].
        eexists. split. eapply plus_left. split.
        all: eauto using plus_star with nbtob semantics.
    (*  Sifthenelse cond strue sfalse, cond s'évalue à None  *)
    - destruct (transl_stmt _ f s0) eqn:Hs0, (transl_stmt _ f s3) eqn:Hs3; try discriminate.
      simpl in TRSTMT.
      destruct guard_stmt_with_expr eqn:Hg; try discriminate. revert TRSTMT; intros [= <-].
      unfold guard_stmt_with_expr in Hg.
      destruct (expr_constraints f cond) eqn:Hconstrs; try discriminate.
      revert Hg; intros [= <-].
      destruct (eval_expr_None_constraints_not_verified _ _ _ _ _ f.(fn_nodup) H11 Hconstrs)
        as [c [Hc1 Hc2]].
      destruct (in_split_last expr_eq_dec c l Hc1) as [c1 [c2 [[= ->] Hnotin]]].
      pose proof TRFUNC. unfold transl_function in TRFUNC.
      destruct transl_stmt; try discriminate. revert TRFUNC; intros [= <-].
      destruct (expr_constraints_eval_bool _ _ _ _ _ _ f.(fn_nodup) H11 Hconstrs) as [lb Hlb].
      clear Hconstrs H0. revert lb Hlb. induction c1; simpl; intros.
      * eexists. split. destruct in_dec; try contradiction.
        simpl. apply plus_one. split. all: eauto with nbtob semantics.
      * inversion Hlb. apply eq_sym in H4. apply map_eq_cons in H4.
        destruct H4 as [b [tl [[= ->] [[= <-] [= <-]]]]]. destruct Hc1 as [[= ->] | Hc1].
        ** destruct in_dec. eauto. pose proof (in_elt c c1 c2). contradiction.
        ** destruct in_dec. eauto. destruct b.
           -- specialize (IHc1 Hc1 tl H6). destruct IHc1 as [ts' [Hts'1 Hts'2]].
              eexists. split. eapply plus_left. split.
              all: eauto using plus_star with nbtob semantics.
           -- eexists. split. apply plus_one. split. all: eauto with nbtob semantics.
  (*  Sloop  *)
  + destruct H1. inversion H0. rewrite_equalities. revert H1; intros [= ->].
    inversion H2; rewrite_equalities; simpl in TRSTMT.
    destruct (transl_stmt _ f s0) eqn:Hs0; try discriminate.
    revert TRSTMT; intros [= <-].
    eexists. split. apply plus_one. split. reflexivity.
    apply SemanticsBlocking.step_loop. apply match_states_State; try eassumption.
    simpl. rewrite Hs0, TRCONT. reflexivity.
  (*  Sbreak  *)
  + destruct H1. inversion H0. rewrite_equalities. revert H1; intros [= ->].
    inversion H2; rewrite_equalities; simpl in TRSTMT, TRCONT;
      destruct transl_stmt, transl_cont eqn:Hk; try discriminate;
      revert TRSTMT TRCONT; intros [= <-] [= <-];
      (eexists; split; [ apply plus_one; split |]; eauto with nbtob semantics).
  (*  Scontinue  *)
  + destruct H1. inversion H0. rewrite_equalities. revert H1; intros [= ->].
    inversion H2; rewrite_equalities; simpl in TRSTMT, TRCONT;
      destruct transl_stmt eqn:Hs, transl_cont eqn:Hk; try discriminate;
      revert TRSTMT TRCONT; intros [= <-] [= <-].
    (*  Scontinue, Kseq  *)
    - eexists. split. apply plus_one. split. reflexivity.
      apply SemanticsBlocking.step_continue_skip. apply match_states_State; easy.
    (*  Scontinue, Kloop  *)
    - eexists. split. apply plus_one. split. reflexivity.
      apply SemanticsBlocking.step_continue_loop. apply match_states_State; try eassumption.
      simpl. rewrite Hs. reflexivity.
  (*  Serror  *)
  + destruct H1. inversion H0. rewrite_equalities. revert H1; intros [= ->].
    inversion H2; rewrite_equalities. revert TRSTMT; intros [= <-].
    eexists. split. apply plus_one. split. all: eauto with semantics.
  (*  Callstate  *)
  + destruct H1. inversion H0; rewrite_equalities;
        inversion H2; rewrite_equalities; try discriminate.
    simpl in TRFD. destruct transl_function eqn:TRF; try discriminate.
    revert TRFD H8; intros [= <-] [= <-]. pose proof TRF.
    unfold transl_function in TRF. destruct transl_stmt eqn:TRBODY; try discriminate.
    revert TRF; intros [= <-].
    eexists. split. apply plus_one. split. all: eauto with nbtob semantics.
  (*  Returnstate  *)
  + destruct H1. inversion H0; rewrite_equalities;
        inversion H2; rewrite_equalities;
        simpl in TRCONT;
        destruct transl_cont eqn:TRK, transl_function eqn:TRF; try discriminate;
        revert TRCONT; intros [= <-]; simpl in NDCONT;
        (eexists; split; [ apply plus_one; split |]).
    all: eauto with nbtob semantics.
    all: (apply match_states_State; easy).
Qed.

Lemma transl_fundefs_genv_public_symbol_add_globals:
  forall p ge ge1 ge2 l id,
    transl_fundefs ge (prog_defs p) = OK l ->
    Genv.public_symbol ge1 id = Genv.public_symbol ge2 id ->
    Genv.genv_public ge1 = Genv.genv_public ge2 ->
    Genv.public_symbol
      (Genv.add_globals ge1
         (SemanticsBlocking.to_AST_globdef l)) id =
    Genv.public_symbol
      (Genv.add_globals ge2
         (to_AST_globdef (prog_defs p))) id.
Proof.
  intro p. induction (prog_defs p); simpl; intros.
  + revert H; intros [= <-]. assumption.
  + destruct a. unfold transl_fundefs in H. simpl in H.
    destruct transl_fundef, list_map_error eqn:Hfundefs in H; try discriminate.
    revert H; intros [= <-].
    apply IHl with (1 := Hfundefs). simpl.
    unfold Genv.add_global. simpl.
    unfold Genv.public_symbol. unfold Genv.find_symbol. simpl.
    unfold Genv.public_symbol in H0. unfold Genv.find_symbol in H0. simpl.
    repeat rewrite PTree.gsspec. destruct (Coqlib.peq id i).
    rewrite H1. all: easy.
Qed.

Theorem transl_program_correct (p: program):
  forall tp,
    transl_program p = OK tp ->
    forward_simulation (SemanticsNonBlocking.semantics p) (SemanticsBlocking.semantics tp).
Proof.
  intros. pose proof H. destruct_transl_program p. rename H into Hp.
  eapply forward_simulation_plus; simpl; intros.
  + pose proof (transl_fundefs_genv_public_symbol_add_globals _ _
              (Genv.empty_genv _ _ (map fst l))
              (Genv.empty_genv _ _ (map fst prog_defs)) l id Hfd).
    simpl in H. simpl in Hmapfst. apply H; rewrite (Hmapfst _ eq_refl); easy.
  + inversion H. rewrite_equalities.
    simpl in H0. pose proof H0. apply PTree.elements_correct in H0.
    apply (proj2 (build_env_correct_empty prog_defs prog_nodup _)) in H0.
    destruct (in_list_map_error _ _ _ _ Hfd H0) as [(prog_main', fd') [H' Hfd']].
    destruct transl_fundef eqn:Htfd; try discriminate. revert H'; intros [= <-].
    simpl in Htfd. destruct transl_function eqn:Htf; try discriminate.
    revert H3 Htfd; intros [= ->] [= <-].
    eexists. split. eapply SemanticsBlocking.initial_state_intro.
    - apply PTree.elements_complete. unfold genv_of_program.
      apply (build_env_correct_empty l); eassumption.
    - unfold transl_function in Htf. destruct transl_stmt; try discriminate.
      revert Htf; intros [= <-]. assumption.
    - apply match_states_Callstate_Internal; try easy. simpl. rewrite Htf. reflexivity.
      apply Forall_forall. intros. destruct x. destruct f0.
      exact f0.(fn_nodup). easy.
  + inversion H0. rewrite_equalities. inversion_clear H.
    revert TRCONT; intros [= <-]. apply SemanticsBlocking.final_state_intro.
  + eapply transl_stmt_sem_preservation; eassumption.
Qed.

End NonBlockingSemanticsToBlockingSemantics.
