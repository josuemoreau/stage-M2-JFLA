Require Import Coq.Lists.List.
Require Import BinNums BinInt.

Import ListNotations.

Require Import Types Ops BValues Syntax Typing BEnv BMemory Validity External.

From compcert Require Import Integers Floats Maps Smallstep.
From compcert Require Import Globalenvs.
From compcert Require AST Events.
Module CAST := AST.

Section SEMANTICS_NON_BLOCKING.

Variable ge: genv.

Section EXPR_NON_BLOCKING.

Variable m: mem.
Variable e: env.
Variable f: function.
(* Variable arrszvar: list (ident * ident).
   Variable te: tenv. *)

Inductive eval_expr: expr -> option value -> Prop :=
| eval_Const_int: forall sz sig n,
  eval_expr (Econst (Cint sz sig n)) (Some (Vint sz sig n))
| eval_Const_int64: forall sig n,
  eval_expr (Econst (Cint64 sig n)) (Some (Vint64 sig n))
| eval_Const_float32: forall f,
  eval_expr (Econst (Cfloat32 f)) (Some (Vfloat32 f))
| eval_Const_float64: forall f,
  eval_expr (Econst (Cfloat64 f)) (Some (Vfloat64 f))
| eval_Var: forall id v t,
  e!id = Some v ->
  f.(fn_tenv)!id = Some t ->
  well_typed_value v t ->
  eval_expr (Evar id) (Some v)
| eval_Cast: forall exp t t1 v1 v,
  eval_expr exp (Some v1) ->
  well_typed_value v1 t1 ->
  sem_cast v1 t1 t = Some v ->
  eval_expr (Ecast exp t1 t) (Some v)
| eval_Cast_ERR: forall exp t1 t,
  eval_expr exp None ->
  eval_expr (Ecast exp t1 t) None
| eval_Unop: forall op k e1 v1 v,
  eval_expr e1 (Some v1) ->
  sem_unop op k v1 = Some v ->
  eval_expr (Eunop op k e1) (Some v)
| eval_Unop_ERR: forall op k e1,
  eval_expr e1 None ->
  eval_expr (Eunop op k e1) None
| eval_Binop_arith: forall op k e1 e2 v1 v2 v,
  eval_expr e1 (Some v1) ->
  eval_expr e2 (Some v2) ->
  sem_binarith_operation op k v1 v2 = Some v ->
  eval_expr (Ebinop_arith op k e1 e2) (Some v)
| eval_Binop_arith_ERR: forall op k e1 e2 r,
  ((eval_expr e1 None /\ eval_expr e2 r)
   \/ (eval_expr e1 r /\ eval_expr e2 None)) ->
  eval_expr (Ebinop_arith op k e1 e2) None
| eval_Binop_logical: forall op e1 e2 v1 v2 v,
  eval_expr e1 (Some v1) ->
  eval_expr e2 (Some v2) ->
  sem_logical_operation op v1 v2 = Some v ->
  eval_expr (Ebinop_logical op e1 e2) (Some v)
| eval_Binop_logical_ERR: forall op e1 e2 r,
  ((eval_expr e1 None /\ eval_expr e2 r)
   \/ (eval_expr e1 r /\ eval_expr e2 None)) ->
  eval_expr (Ebinop_logical op e1 e2) None
| eval_Binop_cmp: forall op k e1 e2 v1 v2 v,
  eval_expr e1 (Some v1) ->
  eval_expr e2 (Some v2) ->
  sem_cmp_operation op k v1 v2 = Some v ->
  eval_expr (Ebinop_cmp op k e1 e2) (Some v)
| eval_Binop_cmp_ERR: forall op k e1 e2 r,
  ((eval_expr e1 None /\ eval_expr e2 r)
   \/ (eval_expr e1 r /\ eval_expr e2 None)) ->
  eval_expr (Ebinop_cmp op k e1 e2) None
| eval_Binop_cmpu: forall op k e1 e2 v1 v2 v,
  eval_expr e1 (Some v1) ->
  eval_expr e2 (Some v2) ->
  sem_cmpu_operation op k v1 v2 = Some v ->
  eval_expr (Ebinop_cmpu op k e1 e2) (Some v)
| eval_Binop_cmpu_ERR: forall op k e1 e2 r,
  ((eval_expr e1 None /\ eval_expr e2 r)
   \/ (eval_expr e1 r /\ eval_expr e2 None)) ->
  eval_expr (Ebinop_cmpu op k e1 e2) None
| eval_Arr_access: forall id idx idarr blk lv szvar n i v b t,
  e!id = Some (Varr idarr lv) ->
  f.(fn_tenv)!id = Some (Tarr b t) ->
  eval_expr idx (Some (Vint64 Unsigned i)) ->
  In (id, szvar) f.(fn_arrszvar) ->
  eval_expr (Evar szvar) (Some (Vint64 Unsigned n)) ->
  m!idarr = Some blk ->
  blk.(blk_values) = lv ->
  blk.(blk_type) = t ->
  Int64.unsigned i < Int64.unsigned n ->
  nth_error lv (Z.to_nat (Int64.unsigned i)) = Some v ->
  eval_expr (Earr_access id idx) (Some v)
(* | eval_Mutarr_access: forall id idx idarr blk szvar n i v t,
     e!id = Some (Vmutarr idarr) ->
     f.(fn_tenv)!id = Some (Tarr true t) ->
     eval_expr idx (Some (Vint64 Unsigned i)) ->
     In (id, szvar) f.(fn_arrszvar) ->
     eval_expr (Evar szvar) (Some (Vint64 Unsigned n)) ->
     m!idarr = Some blk ->
     blk.(blk_type) = t ->
     Int64.unsigned i < Int64.unsigned n ->
     nth_error blk.(blk_values) (Z.to_nat (Int64.unsigned i)) = Some v ->
     eval_expr (Earr_access id idx) (Some v) *)
| eval_Arr_access_ERR: forall id idx szvar n i,
  eval_expr idx (Some (Vint64 Unsigned i)) ->
  In (id, szvar) f.(fn_arrszvar) ->
  eval_expr (Evar szvar) (Some (Vint64 Unsigned n)) ->
  ~(Int64.unsigned i < Int64.unsigned n) ->
  eval_expr (Earr_access id idx) None.

Inductive eval_exprlist: list expr -> option (list value) -> Prop :=
| eval_Enil: eval_exprlist [] (Some [])
| eval_Econs_Some_e: forall e v le lv,
  eval_expr e (Some v) ->
  eval_exprlist le (Some lv) ->
  eval_exprlist (e :: le) (Some (v :: lv))
| eval_Econs_None_e: forall e le,
  eval_expr e None ->
  eval_exprlist (e :: le) None
| eval_Econs_None: forall e le,
  eval_exprlist le None ->
  eval_exprlist (e :: le) None.

Lemma eval_exprlist_length_preservation:
  forall le lv,
    eval_exprlist le (Some lv) -> length le = length lv.
Proof.
  induction le, lv.
  + easy.
  + intro. inversion H.
  + intro. inversion H.
  + intro. inversion_clear H. simpl; apply eq_S. apply (IHle _ H1).
Qed.

Lemma eval_exprlist_app:
  forall le1 le2 lv1 lv2,
    eval_exprlist le1 (Some lv1) ->
    eval_exprlist le2 (Some lv2) ->
    eval_exprlist (le1 ++ le2) (Some (lv1 ++ lv2)).
Proof.
  intros. revert lv1 H. induction le1.
  + intros. inversion_clear H. apply H0.
  + intros. inversion_clear H. simpl.
    specialize (IHle1 _ H2). apply eval_Econs_Some_e; assumption.
Qed.

End EXPR_NON_BLOCKING.

Section STATEMENT_NON_BLOCKING.

Inductive cont : Type :=
| Kstop: cont
| Kseq: stmt -> cont -> cont
| Kreturnto: option ident -> env -> function -> nat -> cont -> cont
| Kloop: stmt -> cont -> cont.

Inductive state : Type :=
| State
    (m:    mem)
    (e:    env)
    (f:    function)
    (llvl: nat)
    (s:    stmt)
    (k:    cont) : state
| Callstate
    (m:    mem)
    (fd:   fundef)
    (args: list value)
    (k:    cont) : state
| Returnstate
    (m:   mem)
    (res: value)
    (k:   cont) : state.

Fixpoint destructCont (k: cont) : cont :=
  match k with
  | Kseq _ k | Kloop _ k => destructCont k
  | _ => k
  end.

Definition is_Kreturnto (k: cont) :=
  match k with
  | Kreturnto _ _ _ _ _ => True
  | _ => False
  end.

Inductive eval_identlist (e: env) (f: function): list ident -> option (list value) -> Prop :=
| eval_ident_Enil: eval_identlist e f [] (Some [])
| eval_ident_Econs: forall id v lids lv t,
  e!id = Some v ->
  f.(fn_tenv)!id = Some t ->
  well_typed_value v t ->
  eval_identlist e f lids (Some lv) ->
  eval_identlist e f (id :: lids) (Some (v :: lv))
| eval_ident_Econs_None_e: forall id lids,
  e!id = None ->
  eval_identlist e f (id :: lids) None
| eval_ident_Econs_None: forall id lids,
  eval_identlist e f lids None ->
  eval_identlist e f (id :: lids) None.

Inductive step_stmt: state -> state -> Prop :=
(* Sskip *)
| step_skip: forall m e f llvl s k,
  step_stmt (State m e f llvl Sskip (Kseq s k)) (State m e f llvl s k)
| step_skip_loop: forall m e f llvl s k,
  step_stmt (State m e f llvl Sskip (Kloop s k)) (State m e f llvl (Sloop s) k)
| step_skip_returnto: forall m e f llvl k,
  is_Kreturnto k ->
  well_typed_value Vunit f.(fn_sig).(sig_res) ->
  step_stmt (State m e f llvl Sskip k)
            (Returnstate m Vunit k)
(* Sassign *)
| step_assign: forall m e f llvl k id exp v,
  eval_expr m e f exp (Some v) ->
  step_stmt (State m e f llvl (Sassign id exp) k)
            (State m (PTree.set id v e) f llvl Sskip k)
| step_assign_ERR: forall m e f llvl k id exp,
  eval_expr m e f exp None ->
  step_stmt (State m e f llvl (Sassign id exp) k)
            (State m e f llvl Serror k)
(* Sarr_assign *)
| step_arr_assign: forall m e f llvl k id idx exp idarr lv blk i v v' szvar n t m' e',
  e!id = Some (Varr idarr lv) ->
  eval_expr m e f idx (Some (Vint64 Unsigned i)) ->
  In (id, szvar) f.(fn_arrszvar) ->
  eval_expr m e f (Evar szvar) (Some (Vint64 Unsigned n)) ->
  Int64.unsigned i < Int64.unsigned n ->
  eval_expr m e f exp (Some v) ->
  f.(fn_tenv)!id = Some (Tarr true t) ->
  well_typed_value v t ->
  sem_cast v t t = Some v' ->
  m!idarr = Some blk ->
  blk.(blk_type) = t ->
  blk.(blk_values) = lv ->
  write_array m e id (Int64.unsigned i) v' = Some (m', e') ->
  step_stmt (State m e f llvl (Sarr_assign id idx exp) k)
            (State m' e f llvl Sskip k)
| step_arr_assign_ERR: forall m e f llvl k id idx exp i szvar n r
  (VAREXISTS: In id (f.(fn_vars) ++ f.(fn_params))),
  eval_expr m e f idx (Some (Vint64 Unsigned i)) ->
  In (id, szvar) f.(fn_arrszvar) ->
  eval_expr m e f (Evar szvar) (Some (Vint64 Unsigned n)) ->
  eval_expr m e f exp r ->
  ~(Int64.unsigned i < Int64.unsigned n) ->
  step_stmt (State m e f llvl (Sarr_assign id idx exp) k)
            (State m e f llvl Serror k)
| step_arr_assign_ERR_idx: forall m e f llvl k id idx exp szvar n r
  (VAREXISTS: In id (f.(fn_vars) ++ f.(fn_params))),
  eval_expr m e f idx None ->
  In (id, szvar) f.(fn_arrszvar) ->
  eval_expr m e f (Evar szvar) (Some (Vint64 Unsigned n)) ->
  eval_expr m e f exp r ->
  step_stmt (State m e f llvl (Sarr_assign id idx exp) k)
            (State m e f llvl Serror k)
| step_arr_assign_ERR_val: forall m e f llvl k id idx exp i szvar n
  (VAREXISTS: In id (f.(fn_vars) ++ f.(fn_params))),
  eval_expr m e f idx (Some (Vint64 Unsigned i)) ->
  In (id, szvar) f.(fn_arrszvar) ->
  eval_expr m e f (Evar szvar) (Some (Vint64 Unsigned n)) ->
  Int64.unsigned i < Int64.unsigned n ->
  eval_expr m e f exp None ->
  step_stmt (State m e f llvl (Sarr_assign id idx exp) k)
            (State m e f llvl Serror k)
(* Scall *)
| step_call_internal: forall m e f llvl k idvar idf args vargs vargs' f',
  ge!idf = Some (Internal f') ->
  valid_call m e f (Internal f') args ->
  length args = length f'.(fn_sig).(sig_args) ->
  match_sig_args_typ f.(fn_tenv) f'.(fn_sig).(sig_args) args ->
  eval_identlist e f args (Some vargs) ->
  check_cast_args vargs f'.(fn_sig).(sig_args) = Some vargs' ->
  step_stmt (State m e f llvl (Scall idvar idf args) k)
            (Callstate m (Internal f') vargs' (Kreturnto idvar e f llvl k))
| step_call_external: forall m e f llvl k idvar idf args vargs vargs' ef m' v,
  ge!idf = Some (External ef) ->
  length args = length (ef_sig ef).(sig_args) ->
  match_sig_args_typ f.(fn_tenv) (ef_sig ef).(sig_args) args ->
  eval_identlist e f args (Some vargs) ->
  check_cast_args vargs (ef_sig ef).(sig_args) = Some vargs' ->
  external_call ef m vargs' v m' ->
  step_stmt (State m e f llvl (Scall idvar idf args) k)
            (State m' (set_optenv e idvar v) f llvl Sskip k)
| step_call_ERR: forall m e f llvl k idvar idf args vargs vargs' fd,
  ge!idf = Some fd ->
  valid_env_arrszvar e f.(fn_arrszvar) ->
  ~valid_call m e f fd args ->
  length args = length (fd_sig fd).(sig_args) ->
  match_sig_args_typ f.(fn_tenv) (fd_sig fd).(sig_args) args ->
  eval_identlist e f args (Some vargs) ->
  check_cast_args vargs (fd_sig fd).(sig_args) = Some vargs' ->
  step_stmt (State m e f llvl (Scall idvar idf args) k)
            (State m e f llvl Serror k)
(* Callstate *)
| step_call_Internal: forall m fd f vargs k e,
  fd = Internal f ->
  build_func_env (PTree.empty value) f.(fn_params) vargs = Some e ->
  step_stmt (Callstate m fd vargs k) (State m e f 0%nat f.(fn_body) k)
(* Sreturn *)
| step_return: forall m e f llvl k exp v v',
  eval_expr m e f exp (Some v) ->
  well_typed_value v f.(fn_sig).(sig_res) ->
  sem_cast v f.(fn_sig).(sig_res) f.(fn_sig).(sig_res) = Some v' ->
  step_stmt (State m e f llvl (Sreturn exp) k)
            (Returnstate m v' (destructCont k))
| step_return_ERR: forall m e f llvl k exp,
  eval_expr m e f exp None ->
  step_stmt (State m e f llvl (Sreturn exp) k)
            (State m e f llvl Serror k)
(* Returnstate *)
| step_returnstate_noident: forall m v e f llvl k,
  step_stmt (Returnstate m v (Kreturnto None e f llvl k))
            (State m e f llvl Sskip k)
| step_returnstate: forall m v id e f llvl k,
  step_stmt (Returnstate m v (Kreturnto (Some id) e f llvl k))
            (State m (PTree.set id v e) f llvl Sskip k)
(* Sseq *)
| step_seq: forall m e f llvl k s1 s2,
  step_stmt (State m e f llvl (Sseq s1 s2) k)
            (State m e f llvl s1 (Kseq s2 k))
(* Sifthenelse *)
| step_ifthenelse: forall m e f llvl k cond b s1 s2,
  eval_expr m e f cond (Some (Vbool b)) ->
  step_stmt (State m e f llvl (Sifthenelse cond s1 s2) k)
            (State m e f llvl (if b then s1 else s2) k)
| step_ifthenelse_ERR: forall m e f llvl k cond s1 s2,
  eval_expr m e f cond None ->
  step_stmt (State m e f llvl (Sifthenelse cond s1 s2) k)
            (State m e f llvl Serror k)
(* Sloop *)
| step_loop: forall m e f llvl s k,
  step_stmt (State m e f llvl (Sloop s) k)
            (State m e f (S llvl) s (Kloop s k))
(* Sbreak *)
| step_break_skip: forall m e f llvl s k,
  step_stmt (State m e f (S llvl) Sbreak (Kseq s k))
            (State m e f (S llvl) Sbreak k)
| step_break_loop: forall m e f llvl s k,
  step_stmt (State m e f (S llvl) Sbreak (Kloop s k))
            (State m e f (S llvl) Sskip k)
(* | step_break_ERR: forall m e f k,
     step_stmt (State m e f 0%nat Sbreak k)
               (State m e f 0%nat Serror k) *)
(* Scontinue *)
| step_continue_skip: forall m e f llvl s k,
  step_stmt (State m e f (S llvl) Scontinue (Kseq s k))
            (State m e f (S llvl) Scontinue k)
| step_continue_loop: forall m e f llvl s k,
  step_stmt (State m e f (S llvl) Scontinue (Kloop s k))
            (State m e f (S llvl) (Sloop s) k)
(* | step_continue_ERR: forall m e f k,
     step_stmt (State m e f 0%nat Scontinue k)
               (State m e f 0%nat Serror k) *)
(* Serror *)
| step_error: forall m e f llvl k,
  step_stmt (State m e f llvl Serror k) (State m e f llvl Serror k).

Inductive reachable_state (s: state): state -> Prop :=
| RS_id: reachable_state s s
| RS_step: forall s1 s2,
    step_stmt s s1 ->
    reachable_state s1 s2 ->
    reachable_state s s2.

Lemma reachable_state_one_step (s1 s2: state):
  step_stmt s1 s2 ->
  reachable_state s1 s2.
Proof.
  intros. apply (RS_step _ s2). exact H. apply RS_id.
Qed.

End STATEMENT_NON_BLOCKING.

Inductive initial_state (p: program) : state -> Prop :=
| initial_state_intro: forall f,
  (genv_of_program p) ! (prog_main p) = Some (Internal f) ->
  f.(fn_sig) = {| sig_args := []; sig_res := Tint I32 Signed |} ->
  initial_state p (Callstate empty_mem (Internal f) [] Kstop).

Inductive final_state : state -> int -> Prop :=
| final_state_intro: forall m sz sig i,
  final_state (Returnstate m (Vint sz sig i) Kstop) i.

End SEMANTICS_NON_BLOCKING.

Section COMPCERT_SEMANTICS.

Definition step_events (ge: genv) (st1: state) (t: Events.trace) (st2: state): Prop :=
  t = Events.E0 /\ step_stmt ge st1 st2.

Definition to_AST_globdef (l: list (ident * fundef)) : list (ident * CAST.globdef fundef typ):=
  map (fun x => (fst x, CAST.Gfun (snd x))) l.

Definition to_genv (prog_defs: list (ident * fundef)) : Genv.t fundef typ :=
  Genv.add_globals (Genv.empty_genv fundef typ (map fst prog_defs)) (to_AST_globdef prog_defs).

Definition semantics p :=
  Semantics_gen step_events (initial_state p) final_state (genv_of_program p) (to_genv p.(prog_defs)).

End COMPCERT_SEMANTICS.

Create HintDb semanticsnb.
Global Hint Constructors eval_expr eval_exprlist eval_identlist : semanticsnb.
Global Hint Constructors step_stmt reachable_state : semanticsnb.
Global Hint Resolve eval_exprlist_app : semanticsnb.
Global Hint Resolve reachable_state_one_step : semanticsnb.

Inductive valid_cont (ge: genv) (f: function): cont -> Prop :=
| valid_Kstop:
  valid_cont ge f Kstop
| valid_Kseq: forall s k,
  valid_stmt ge f s ->
  valid_cont ge f k ->
  valid_cont ge f (Kseq s k)
| valid_Kloop: forall s k,
  valid_stmt ge f (Sloop s) ->
  valid_cont ge f k ->
  valid_cont ge f (Kloop s k)
| valid_Kreturnto: forall id e' f' llvl' k,
  valid_cont ge f' k ->
  valid_cont ge f (Kreturnto id e' f' llvl' k).
