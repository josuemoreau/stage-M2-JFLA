Require Import Coq.Lists.List.
Require Import BinNums BinInt.
Require Import Coq.Bool.Bool.
Require Import MSets.

Require Import Types Syntax Ops BValues BEnv BUtils.

Module PSet := Make Pos.

From compcert Require Import Integers Maps.

Import ListNotations.

Local Open Scope bool_scope.

Create HintDb typing.

Definition typ_corresp_opkind_unop (t: typ) (k: operation_kind) :=
  match k, t with
  | OInt, Tint _ _   => true
  | OInt64, Tint64 _ => true
  | OFloat32, Tfloat F32 => true
  | OFloat64, Tfloat F64 => true
  | _, _ => false
  end.

Definition typ_corresp_opkind_binop (t1 t2: typ) (k: operation_kind) :=
  match k with
  | OInt =>
      match t1, t2 with
      | Tint _ _, Tint _ _ => true
      | _, _ => false
      end
  | OInt64 =>
      match t1, t2 with
      | Tint64 _, Tint64 _ => true
      | _, _ => false
      end
  | OFloat32 => eq_typ t1 (Tfloat F32) && eq_typ t2 (Tfloat F32)
  | OFloat64 => eq_typ t1 (Tfloat F64) && eq_typ t2 (Tfloat F64)
  end.

Definition op_corresp_signedness (op: binarith_operation)
                                 (sig1 sig2: signedness) :=
  match op, sig1, sig2 with
  | Omods, Signed, Signed => true
  | Omods, _, _ => false
  | Omodu, Signed, Signed => false
  | Omodu, _, _ => true
  | Odivs, Signed, Signed => true
  | Odivs, _, _ => false
  | Odivu, Signed, Signed => false
  | Odivu, _, _ => true
  | _, _, _ => true
  end.

Definition op_corresp_intsize (op: binarith_operation)
                              (sz1 sz2: intsize) :=
  match op, sz1, sz2 with
  | Omodu, I32, I32 => true
  | Omodu, _, _ => false
  | Odivu, I32, I32 => true
  | Odivu, _, _ => false
  | _, _, _ => true
  end.

Fixpoint type_expression (te: tenv) (e: expr) : option typ :=
  match e with
  | Evar x => te!x
  | Econst (Cint sz sig n) => Some (Tint sz sig)
  | Econst (Cint64 sig n) => Some (Tint64 sig)
  | Econst (Cfloat32 _) => Some (Tfloat F32)
  | Econst (Cfloat64 _) => Some (Tfloat F64)
  | Ecast exp t1 t =>
      match type_expression te exp, t with
      | Some ((Tint _ _ | Tint64 _ | Tfloat _) as t'),
        (Tint _ _ | Tint64 _ | Tfloat _) => if eq_typ t1 t' then Some t else None
      | _, _ => None
      end
  | Eunop Onotbool _ e =>
      match type_expression te e with
      | Some Tbool as t => t
      | _ => None
      end
  | Eunop Onotint k e =>
      match type_expression te e with
      | Some (Tint64 _ as t) | Some (Tint _ _ as t) =>
        if typ_corresp_opkind_unop t k then Some t else None
      | _ => None
      end
  | Eunop Oneg k e =>
      match type_expression te e with
      | Some t => if typ_corresp_opkind_unop t k then Some t else None
      | None => None
      end
  (* TODO utiliser des monades ! *)
  | Eunop Oabsfloat k e =>
      match type_expression te e with
      | Some (Tfloat _ as t) =>
          if typ_corresp_opkind_unop t k then Some (Tfloat F64) else None
      | _ => None
      end
  | Ebinop_arith (Omods as op) k e1 e2 | Ebinop_arith (Omodu as op) k e1 e2  =>
      match type_expression te e1, type_expression te e2 with
      | Some (Tint s1 sig1 as t1), Some (Tint s2 sig2 as t2) =>
          if op_corresp_signedness op sig1 sig2
             && typ_corresp_opkind_binop t1 t2 k
             && eq_intsize s1 s2
             && op_corresp_intsize op s1 s2 then
            Some (Tint I32 (max_signedness sig1 sig2))
          else None
      | Some (Tint64 sig1 as t1), Some (Tint64 sig2 as t2) =>
          if op_corresp_signedness op sig1 sig2
             && typ_corresp_opkind_binop t1 t2 k then
            Some (Tint64 (max_signedness sig1 sig2))
          else None
      | _, _ => None
      end
  | Ebinop_arith op k e1 e2 =>
      match type_expression te e1, type_expression te e2 with
      (* On ne considère pas de conversion implicite pour le moment *)
      | Some (Tint s1 sig1 as t1), Some (Tint s2 sig2 as t2) =>
          if op_corresp_signedness op sig1 sig2
             && typ_corresp_opkind_binop t1 t2 k
             && eq_intsize s1 s2
             && op_corresp_intsize op s1 s2 then
            Some (Tint s1 (max_signedness sig1 sig2))
          else None
      | Some (Tint64 sig1 as t1), Some (Tint64 sig2 as t2) =>
          if op_corresp_signedness op sig1 sig2
             && typ_corresp_opkind_binop t1 t2 k then
            Some (Tint64 (max_signedness sig1 sig2))
          else None
      | Some (Tfloat _ as t1), Some t2 =>
          if typ_corresp_opkind_binop t1 t2 k then Some t1 else None
      | _, _ => None
      end
  | Ebinop_logical _ e1 e2 =>
      match type_expression te e1, type_expression te e2 with
      | Some Tbool, Some Tbool => Some Tbool
      | _, _ => None
      end
  | Ebinop_cmp _ k e1 e2 =>
      match type_expression te e1, type_expression te e2 with
      | Some (Tint s1 Signed as t1), Some (Tint s2 Signed as t2) =>
          if typ_corresp_opkind_binop t1 t2 k && eq_intsize s1 s2 then Some Tbool
          else None
      | Some (Tint64 Signed as t1), Some (Tint64 Signed as t2) =>
          if typ_corresp_opkind_binop t1 t2 k then Some Tbool
          else None
      | Some (Tfloat _ as t1), Some t2 =>
          if typ_corresp_opkind_binop t1 t2 k then Some Tbool else None
      | _, _ => None
      end
  | Ebinop_cmpu _ k e1 e2 =>
      match type_expression te e1, type_expression te e2 with
      | Some (Tint I32 sig1 as t1), Some (Tint I32 sig2 as t2) =>
          if typ_corresp_opkind_binop t1 t2 k
             && (eq_signedness sig1 Unsigned || eq_signedness sig2 Unsigned) then Some Tbool
          else None
      | Some (Tint64 sig1 as t1), Some (Tint64 sig2 as t2) =>
          if typ_corresp_opkind_binop t1 t2 k
             && (eq_signedness sig1 Unsigned || eq_signedness sig2 Unsigned) then Some Tbool
          else None
      | _, _ => None
      end
  | Earr_access id idx =>
      match type_expression te idx with
      | Some (Tint64 Unsigned) =>
          match te!id with
          | Some (Tarr _ t) => Some t
          | _ => None
          end
      | _ => None
      end
  end.

Definition well_typed (te: tenv) (e: expr) : Prop :=
  type_expression te e <> None.

Inductive well_typed_value: value -> typ -> Prop :=
| well_typed_Vunit:
    well_typed_value Vunit Tvoid
| well_typed_Vbool: forall b,
    well_typed_value (Vbool b) Tbool
| well_typed_Vint: forall n sz sig,
    well_typed_value (Vint sz sig n) (Tint sz sig)
| well_typed_Vint64: forall n sig,
    well_typed_value (Vint64 sig n) (Tint64 sig)
| well_typed_Vfloat32: forall f,
    well_typed_value (Vfloat32 f) (Tfloat F32)
| well_typed_Vfloat64: forall f,
    well_typed_value (Vfloat64 f) (Tfloat F64)
| well_typed_Varr: forall id lv b t,
    Forall (fun v => well_typed_value v t) lv ->
    well_typed_value (Varr id lv) (Tarr b t).

Inductive well_typed_valuelist: list value -> list typ -> Prop :=
| well_typed_valuelist_Nil:
    well_typed_valuelist [] []
| well_typed_valuelist_Cons: forall v t lv lt,
    well_typed_value v t ->
    well_typed_valuelist lv lt ->
    well_typed_valuelist (v :: lv) (t :: lt).

Lemma well_typed_value_shrink:
    forall v t,
      well_typed_value v t ->
      well_typed_value (shrink v) t.
Proof.
  induction v; simpl; intros; try assumption.
  inversion_clear H. destruct i, s; apply well_typed_Vint.
Qed.


Global Hint Constructors well_typed_value well_typed_valuelist : typing.

Local Open Scope option_bool_monad_scope.

Fixpoint type_expression_list (te: tenv) (le: list expr) : option (list typ) :=
  match le with
  | [] => Some []
  | e :: le =>
      do t <- type_expression te e;
      do tl <- type_expression_list te le;
      Some (t :: tl)
  end.

Fixpoint type_ident_list (te: tenv) (lids: list ident) : option (list typ) :=
  match lids with
  | [] => Some []
  | id :: lids =>
      do t <- te!id;
      do tids <- type_ident_list te lids;
      Some (t :: tids)
  end.

Fixpoint eq_type_list (l1 l2: list typ): bool :=
  match l1, l2 with
  | [], [] => true
  | t1 :: l1, t2 :: l2 =>
      if eq_typ t1 t2 then eq_type_list l1 l2
      else false
  | _, _ => false
  end.

Definition compatible_tenvs (te1 te2: tenv) : bool :=
  PTree.fold (fun b k t1 =>
    match te2!k with
    | None => b
    | Some t2 => b && eq_typ t1 t2
    end) te1 true.

Definition combine_tenvs (te1 te2: tenv) : tenv :=
  PTree.combine (fun t1 t2 =>
    match t1, t2 with
    | None, None => None
    | Some t, None => Some t
    | None, Some t => Some t
    | Some t1, Some t2 => if eq_typ t1 t2 then Some t1 else None
    end) te1 te2.

Open Scope positive_scope.



Fixpoint build_function_tenv (te: tenv) (params: list ident) (sig: list typ) :=
  match params, sig with
  | [], [] => Some te
  | [], _ | _, [] => None
  | param :: params, typ :: sig =>
      build_function_tenv (PTree.set param typ te) params sig
  end.

Fixpoint args_aliasing' (f: function) (s: PSet.t) (args: list ident) :=
  match args with
  | [] => false
  | id :: args =>
      if PSet.mem id s then
        match f.(fn_tenv) ! id with
        | Some (Tarr false _) => args_aliasing' f s args
        | _ => false
        end
      else args_aliasing' f (PSet.add id s) args
  end.

Definition args_aliasing (f: function) (args: list ident) :=
  args_aliasing' f PSet.empty args.

Fixpoint type_arg (targ: typ) (tsig: typ) :=
  match targ, tsig with
  | Tarr  true t1, Tarr     _ t2 => type_arg t1 t2
  | Tarr false t1, Tarr false t2 => type_arg t1 t2
  | Tarr false  _, Tarr  true  _ => false
  |            t1,            t2 => eq_typ t1 t2
  end.

Fixpoint type_args (targs: list typ) (sig: list typ) :=
  match targs, sig with
  | [], [] => true
  | [], _  | _, [] => false
  | t1 :: targs, t2 :: sig => type_arg t1 t2 && type_args targs sig
  end.

Fixpoint type_statement (ge: genv) (f: function) (s: stmt) : bool :=
  match s with
  | Sskip => true
  | Sassign id exp =>
      if existsb (fun x => x =? id) (map snd f.(fn_arrszvar)) then false
      else do* t <- type_expression f.(fn_tenv) exp;
           do* t' <- f.(fn_tenv)!id;
           match t with
           | Tarr _ _ => false
           | _ => eq_typ t t'
           end
  | Sarr_assign id idx exp =>
      do* tarr <- f.(fn_tenv)!id;
      do* tidx <- type_expression f.(fn_tenv) idx;
      do* t <- type_expression f.(fn_tenv) exp;
      match tidx, tarr with
      | Tint64 Unsigned, Tarr true t' => eq_typ t t'
      | _, _ => false
      end
  | Scall None idf args =>
      do* fd <- ge!idf;
      do* tl <- type_ident_list f.(fn_tenv) args;
      if args_aliasing f args then false
      else match fd with
           | Internal f => eq_type_list f.(fn_sig).(sig_args) tl
           | External ef =>
               match ef with
               | EF_external _ sig => eq_type_list sig.(sig_args) tl
               end
           end
  | Scall (Some idvar) idf args =>
      if existsb (fun x => x =? idvar) (map snd f.(fn_arrszvar)) then false
      else do* fd <- ge!idf;
           do* tl <- type_ident_list f.(fn_tenv) args;
           do* tvar <- f.(fn_tenv)!idvar;
           match fd with
           | Internal f => eq_typ tvar f.(fn_sig).(sig_res)
                           && type_args tl f.(fn_sig).(sig_args)
           | External ef =>
               match ef with
               | EF_external _ sig => eq_typ tvar sig.(sig_res)
                                     && type_args tl sig.(sig_args)
               end
           end
  | Sreturn exp =>
      do* texp <- type_expression f.(fn_tenv)exp;
      eq_typ texp f.(fn_sig).(sig_res)
  | Sseq s1 s2 => type_statement ge f s1 && type_statement ge f s2
  | Sifthenelse c s1 s2 =>
      do* tc <- type_expression f.(fn_tenv) c;
      match tc with
      | Tbool => type_statement ge f s1 && type_statement ge f s2
      | _ => false
      end
  | Sloop s => type_statement ge f s
  | Sbreak | Scontinue | Serror => true
  end.

Definition type_function (ge: genv) (f: function) :=
  type_statement ge f f.(fn_body).

Definition type_genv (ge: genv) :=
  forallb (fun x => match snd x with
                    | Internal f => type_function ge f
                    | External f => true
                    end) (PTree.elements ge).

Fixpoint well_typed_value_bool (v: value) (t: typ) :=
  match v, t with
  |        Vunit ,         Tvoid => true
  |      Vbool b ,         Tbool => true
  | Vint sz sig _, Tint sz' sig' => eq_intsize sz sz' && eq_signedness sig sig'
  |  Vint64 sig _,   Tint64 sig' => eq_signedness sig sig'
  |    Vfloat32 _,    Tfloat F32 => true
  |    Vfloat64 _,    Tfloat F64 => true
  |     Varr _ lv,      Tarr _ t => forallb (fun v => well_typed_value_bool v t) lv
  |             _,             _ => false
  end.

Lemma well_typed_value_bool_correct:
  forall t v,
    well_typed_value_bool v t = true -> well_typed_value v t.
Proof.
  induction t; simpl; intros; destruct v; try discriminate.
  + apply well_typed_Vunit.
  + apply well_typed_Vbool.
  + destruct i, i0, s, s0; try discriminate; apply well_typed_Vint.
  + destruct s, s0; try discriminate; apply well_typed_Vint64.
  + destruct f; try discriminate; apply well_typed_Vfloat32.
  + destruct f; try discriminate; apply well_typed_Vfloat64.
  + apply well_typed_Varr, Forall_forall. intros. simpl in H.
    eapply forallb_forall with (x := x) in H. exact (IHt _ H). assumption.
Qed.

(* à voir si tjrs utile *)
Fixpoint check_cast_args (lv: list value) (lt: list typ) : option (list value) :=
  match lt, lv with
  | [], [] => Some []
  | _, [] | [], _ => None
  (* | (Vmutarr idarr) :: lv, (Tarr false _) :: lt =>
         do vargs <- check_cast_args m lv lt;
         do l <- m!idarr;
         Some ((Varr idarr l.(blk_values)) :: vargs)
     | (Varr _ _) :: _, (Tarr true _) :: _ => None *)
  | Tint i1 s1 :: lt, Vint i2 s2 n :: lv =>
      if eq_intsize i1 i2 && eq_signedness s1 s2 then
        do vargs <- check_cast_args lv lt;
        Some (Vint i1 s1 (cast_int_int i1 s1 n) :: vargs)
      else None
  (* | Tint I8 Signed :: lt, Vint I8 Signed n :: lv =>
         do vargs <- check_cast_args lv lt;
         Some (Vint I8 Signed (Int.sign_ext 8 n) :: vargs)
     | Tint I8 Unsigned :: lt, Vint I8 Unsigned n :: lv =>
         do vargs <- check_cast_args lv lt;
         Some (Vint I8 Unsigned (Int.zero_ext 8 n) :: vargs)
     | Tint I16 Signed :: lt, Vint I16 Signed n :: lv =>
         do vargs <- check_cast_args lv lt;
         Some (Vint I8 Signed (Int.sign_ext 16 n) :: vargs)
     | Tint I16 Unsigned :: lt, Vint I16 Unsigned n :: lv =>
         do vargs <- check_cast_args lv lt;
         Some (Vint I8 Unsigned (Int.zero_ext 16 n) :: vargs) *)
  | t :: lt, v :: lv =>
      do vargs <- check_cast_args lv lt;
      if well_typed_value_bool v t then Some (v :: vargs)
      else None
  end.

Definition match_sig_args_typ (te: tenv) (sig: list typ) (args: list ident) :=
    forall i var,
      nth_error args i = Some var ->
      te!var = nth_error sig i.

Close Scope positive_scope.
