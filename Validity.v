Require Import Coq.Lists.List.
Require Import BinNums BinInt.
Require Import Lia.

Import ListNotations.

Require Import Types Ops BValues Syntax BEnv Typing BUtils BMemory.

From compcert Require Import Integers Floats Maps Errors.
From compcert Require AST Events.

Section VALIDITY_IN_FUNCTION.

Section VALIDITY_EXPR.

Variable f: function.

Inductive valid_expr: expr -> Prop :=
(* | valid_expr_Eunit:
       valid_expr Eunit *)
| valid_expr_Evar: forall id t,
    In id (f.(fn_params) ++ f.(fn_vars)) ->
    type_expression f.(fn_tenv) (Evar id) = Some t ->
    valid_expr (Evar id)
| valid_expr_Econst: forall c,
    valid_expr (Econst c)
| valid_expr_Ecast: forall exp t1 t,
    valid_expr exp ->
    valid_expr (Ecast exp t1 t)
| valid_expr_Eunop: forall op k e1,
    valid_expr e1 ->
    valid_expr (Eunop op k e1)
| valid_expr_Ebinop_arith: forall op k e1 e2,
    valid_expr e1 ->
    valid_expr e2 ->
    valid_expr (Ebinop_arith op k e1 e2)
| valid_expr_Ebinop_logical: forall op e1 e2,
    valid_expr e1 ->
    valid_expr e2 ->
    valid_expr (Ebinop_logical op e1 e2)
| valid_expr_Ebinop_cmp: forall op k e1 e2,
    valid_expr e1 ->
    valid_expr e2 ->
    valid_expr (Ebinop_cmp op k e1 e2)
| valid_expr_Ebinop_cmpu: forall op k e1 e2,
    valid_expr e1 ->
    valid_expr e2 ->
    valid_expr (Ebinop_cmpu op k e1 e2)
| valid_expr_Earr_access: forall id idx b t,
    valid_expr idx ->
    f.(fn_tenv)!id = Some (Tarr b t) ->
    (exists szvar, In (id, szvar) f.(fn_arrszvar)) ->
    valid_expr (Earr_access id idx).

Fixpoint valid_list_expr (le: list expr): Prop :=
  match le with
  | [] => True
  | exp :: le => valid_expr exp /\ valid_list_expr le
  end.

End VALIDITY_EXPR.

Section VALIDITY_STMT.

Variable ge: genv.
Variable f: function.

Fixpoint valid_list_ids (lids: list ident): Prop :=
  match lids with
  | [] => True
  | id :: lids =>
      In id (f.(fn_params) ++ f.(fn_vars)) /\ valid_list_ids lids
  end.

Inductive valid_stmt: stmt -> Prop :=
| valid_stmt_Sskip:
    valid_stmt Sskip
| valid_stmt_Sassign: forall id exp,
    valid_expr f exp ->
    valid_stmt (Sassign id exp)
| valid_stmt_Sarr_assign: forall id idx exp b t,
    valid_expr f idx ->
    valid_expr f exp ->
    f.(fn_tenv)!id = Some (Tarr b t) ->
    (exists szvar, In (id, szvar) f.(fn_arrszvar)) ->
    valid_stmt (Sarr_assign id idx exp)
| valid_stmt_Scall_noident: forall idf args f,
    valid_list_ids args ->
    ge!idf = Some (Internal f) ->
    (* À enlever après, en fait on peut, par typage, voir que le nombre d'argument
       est égal au nombre de paramètres dans la signature.
       Et, lorsqu'on créera une fonction on vérifiera trivialement que le nombre de
       paramètres et le nombre de paramètres dans la signature sont égaux. *)
    fundef_nb_params (Internal f) = length args ->
    valid_stmt (Scall None idf args)
| valid_stmt_Scall: forall idvar idf args t f,
    In idvar (f.(fn_params) ++ f.(fn_vars)) ->
    f.(fn_tenv)!idvar = Some t ->
    valid_list_ids args ->
    ge!idf = Some (Internal f) ->
    fundef_nb_params (Internal f) = length args ->
    valid_stmt (Scall (Some idvar) idf args)
| valid_stmt_Sreturn: forall exp,
    valid_expr f exp ->
    valid_stmt (Sreturn exp)
| valid_stmt_Sseq: forall s1 s2,
    (* On exige pour l'instant que toutes les variables du corps d'une fonction
       soient dans l'environnement à n'importe quel moment, même avant leur initialisation
       par l'utilisateur. *)
    valid_stmt s1 ->
    valid_stmt s2 ->
    valid_stmt (Sseq s1 s2)
| valid_stmt_Sifthenelse: forall cond strue sfalse,
    valid_expr f cond ->
    valid_stmt strue ->
    valid_stmt sfalse ->
    valid_stmt (Sifthenelse cond strue sfalse)
| valid_stmt_Sloop: forall s,
    valid_stmt s ->
    valid_stmt (Sloop s)
| valid_stmt_Sbreak:
    valid_stmt Sbreak
| valid_stmt_Scontinue:
    valid_stmt Scontinue
| valid_stmt_Serror:
    valid_stmt Serror.

End VALIDITY_STMT.

(* Definition valid_function (ge: genv) (f: function) :=
     valid_stmt ge f f.(fn_body)
     /\ valid_sig_arrszvar
     /\ forall id szvar, (In (id, szvar) f.(fn_arrszvar) ->
                          exists b t, f.(fn_tenv)!id = Some (Tarr b t)
                                      /\ f.(fn_tenv)!szvar = Some (Tint64 Unsigned)). *)

(* Definition valid_genv (ge: genv) :=
     Forall (fun fd => match snd fd with
                       | Internal f  => valid_function ge f
                       | External ef => True
                       end) (PTree.elements ge). *)

End VALIDITY_IN_FUNCTION.


Section VALIDITY_OF_FUNCTION_IN_ENVIRONMENT.

Definition arr_szvar_exists (e: env) (arrszvar: list (ident * ident)) :=
  forall id idarr lv,
    e!id = Some (Varr idarr lv) ->
    exists szvar, In (id, szvar) arrszvar.

(* Definition mutarr_szvar_exists (e: env) (arrszvar: list (ident * ident)) :=
     forall id idarr,
       e!id = Some (Vmutarr idarr) ->
       exists szvar, In (id, szvar) arrszvar. *)

Definition valid_env_arrszvar (e: env) (arrszvar: list (ident * ident)) :=
  forall id szvar,
    In (id, szvar) arrszvar ->
    exists idarr lv len,
      e!id = Some (Varr idarr lv) /\ e!szvar = Some (Vint64 Unsigned len).

Definition valid_szvar (e: env) (arrszvar: list (ident * ident)) :=
  forall id szvar idarr lv len,
    In (id, szvar) arrszvar ->
    e!id = Some (Varr idarr lv) ->
    e!szvar = Some (Vint64 Unsigned len) ->
    Int64.unsigned len = Z.of_nat (length lv).

(* Definition valid_szvar_mut (m: mem) (e: env) (arrszvar: list (ident * ident)) :=
     forall id szvar idarr blk len,
       In (id, szvar) arrszvar ->
       e!id = Some (Vmutarr idarr) ->
       m!idarr = Some blk ->
       e!szvar = Some (Vint64 Unsigned len) ->
       Int64.unsigned len = Z.of_nat (length blk.(blk_values)). *)

Definition separated_env (te: tenv) (e: env) :=
  forall id id' idarr idarr' lv lv' t,
    (* à changer quand on s'intéressera au vues sur des tableaux *)
    e!id = Some (Varr idarr lv) ->
    e!id' = Some (Varr idarr' lv') ->
    te ! id = Some (Tarr true t) ->
    id <> id' ->
    idarr <> idarr'.

Definition well_typed_env (te: tenv) (m: mem) (e: env) :=
  (forall id idarr lv blk,
      e!id = Some (Varr idarr lv) ->
      m!idarr = Some blk ->
      exists b, te!id = Some (Tarr b blk.(blk_type)))
  /\ (forall id b t,
         te!id = Some (Tarr b t) ->
         exists idarr lv, e!id = Some (Varr idarr lv))
  /\ (forall id v t,
         te!id = Some t ->
         e!id = Some v ->
         well_typed_value v t).

(* Definition valid_env (e: env) (f: function) :=
     forall x,
       In x (f.(fn_params) ++ f.(fn_vars)) -> In x (map fst (PTree.elements e)). *)

Definition valid_env_function (m: mem) (e: env) (f: function) :=
  arr_szvar_exists e f.(fn_arrszvar)
  (* /\ mutarr_szvar_exists e f.(fn_arrszvar) *)
  /\ valid_env_arrszvar e f.(fn_arrszvar)
  /\ valid_szvar e f.(fn_arrszvar)
  (* /\ valid_szvar_mut m e f.(fn_arrszvar) *)
  /\ well_typed_env f.(fn_tenv) m e
  (* /\ valid_env e f *)
  /\ separated_env f.(fn_tenv) e.

End VALIDITY_OF_FUNCTION_IN_ENVIRONMENT.

Section VALIDITY_OF_FUNCTION_CALL.

Definition valid_function_call (m: mem) (e: env)
                               (caller callee: function) (args: list ident) :=
  forall id sz i j,
    In (id, sz) callee.(fn_arrszvar) ->
    nth_error callee.(fn_params) i = Some id ->
    nth_error callee.(fn_params) j = Some sz ->
    exists id0 sz0 sz1 n1 n2,
      nth_error args i = Some id0 /\
      nth_error args j = Some sz0 /\
      In (id0, sz1) caller.(fn_arrszvar) /\
      e!sz0 = Some (Vint64 Unsigned n1) /\
      e!sz1 = Some (Vint64 Unsigned n2) /\
      (* caller.(fn_tenv)!sz0 = Some Tuint64 /\ *)
      (* caller.(fn_tenv)!sz1 = Some Tuint64 /\ *)
      Int64.unsigned n1 <= Int64.unsigned n2.

(* Definition valid_call_sig_arrszvar (callee: fundef) :=
     match callee with
     | Internal f => valid_sig_arrszvar f
     | External _ => True
     end. *)

(* Inductive valid_call (m: mem) (e: env)
             (caller: function) (args: list ident) : fundef -> Prop :=
   | valid_call_Internal: forall f,
     valid_function_call m e caller f args ->
     valid_call m e caller args (Internal f)
   | valid_call_External: forall ef,
     valid_call m e caller args (External ef). *)

Definition valid_call (m: mem) (e: env) (caller: function)
          (callee: fundef) (args: list ident) :=
  match callee with
  | Internal f => valid_function_call m e caller f args
  | External _ => True
  end.

End VALIDITY_OF_FUNCTION_CALL.

Section VALIDITY_OF_ENVIRONMENT.

Definition valid_mem_env (m: mem) (e: env) :=
  forall id idarr lv,
    e!id = Some (Varr idarr lv) ->
    exists blk, m!idarr = Some blk /\ blk.(blk_values) = lv.

End VALIDITY_OF_ENVIRONMENT.


Section USEFUL_LEMMAS.

Lemma read_arr_not_None (m: mem) (e: env) (f: function):
  forall id idarr lv idx szvar len,
    valid_env_function m e f ->
    In (id, szvar) f.(fn_arrszvar) ->
    e!id = Some (Varr idarr lv) ->
    e!szvar = Some (Vint64 Unsigned len) ->
    is_true (Int64.ltu idx len) ->
    nth_error lv (Z.to_nat (Int64.unsigned idx)) <> None.
Proof.
  intros. unfold valid_env_function in H. destruct H as [ _ [ _ [ Hd _ ] ] ].
  specialize (Hd id szvar idarr lv len H0 H1 H2).
  apply nth_error_Some. pose proof (Int64.unsigned_range idx).
  unfold Int64.ltu in H3. destruct Coqlib.zlt in H3; try discriminate. lia.
Qed.

(* Lemma read_mutarr_not_None (m: mem) (e: env) (f: function):
       forall id idarr blk idx szvar len,
         valid_mem_env m e ->
         valid_env_function m e f ->
         In (id, szvar) f.(fn_arrszvar) ->
         e!id = Some (Vmutarr idarr) ->
         m!idarr = Some blk ->
         e!szvar = Some (Vint64 Unsigned len) ->
         is_true (Int64.ltu idx len) ->
         nth_error blk.(blk_values) (Z.to_nat (Int64.unsigned idx)) <> None.
   Proof.
     intros. destruct H0 as [ _ [ Hb [ Hc [ _ [ He _ ] ] ] ] ].
     specialize (He id szvar idarr blk len H1 H2 H3 H4).
     apply nth_error_Some. pose proof (Int64.unsigned_range idx).
     unfold Int64.ltu in H5. destruct Coqlib.zlt in H5; try discriminate. lia.
   Qed. *)

End USEFUL_LEMMAS.
