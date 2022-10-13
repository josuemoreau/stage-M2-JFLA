Require Import Coq.Lists.List.
Require Import BinNums BinInt.
Require Import Coq.Bool.Bool.
Require Import Lia.

Import ListNotations.

From compcert Require Import Integers Floats Maps Errors Smallstep.
From compcert Require Import AST Ctypes Cop Memory Values Events Clight.
From compcert Require Import Globalenvs.

Module CValues := Values.

Require Import BValues Types Syntax Typing Ops BUtils.
Require Import BEnv BMemory Validity SemanticsBlocking Safety.

Local Open Scope option_bool_monad_scope.

Definition transl_signedness (s: signedness) : Ctypes.signedness :=
  match s with
  | Unsigned => Ctypes.Unsigned
  | Signed => Ctypes.Signed
  end.

Definition transl_intsize (sz: intsize) : Ctypes.intsize :=
  match sz with
  | I8  => Ctypes.I8
  | I16 => Ctypes.I16
  | I32 => Ctypes.I32
  end.

Definition transl_floatsize (sz: floatsize) :=
  match sz with
  | F32 => Ctypes.F32
  | F64 => Ctypes.F64
  end.

Fixpoint transl_typ (t: typ) : Ctypes.type :=
  match t with
  | Tvoid       =>  Ctypes.Tvoid
      (* Ctypes.Tint Ctypes.I32 Ctypes.Unsigned noattr *)
  | Tbool       => Ctypes.Tint Ctypes.IBool Ctypes.Unsigned noattr
  | Tint sz sig => Ctypes.Tint (transl_intsize sz) (transl_signedness sig) noattr
  | Tint64 sig  => Ctypes.Tlong (transl_signedness sig) noattr
  | Tfloat sz   => Ctypes.Tfloat (transl_floatsize sz) noattr
  | Tarr _ t    => Tpointer (transl_typ t) noattr
  end.

(* Definition transl_typlist (lt: list typ) : list Ctypes.type :=
     map transl_typ lt. *)

Fixpoint transl_typlist (lt: list typ) : Ctypes.typelist :=
  match lt with
  | []      => Ctypes.Tnil
  | t :: lt => Ctypes.Tcons (transl_typ t) (transl_typlist lt)
  end.

Definition transl_typ_to_AST_typ (t: typ) : AST.typ :=
  match t with
  | Tvoid      => AST.Tint
  | Tbool      => AST.Tint
  | Tint _ _   => AST.Tint
  | Tint64 _   => AST.Tlong
  | Tfloat F32 => AST.Tsingle
  | Tfloat F64 => AST.Tfloat
  | Tarr _ _   => AST.Tany64
  end.

Definition transl_typlist_to_AST_typlist (lt: list typ) : list AST.typ :=
  map transl_typ_to_AST_typ lt.

Definition transl_typ_to_AST_rettype (t: typ) : AST.rettype :=
  match t with
  | Tvoid => AST.Tvoid
  | Tint I8 Unsigned => AST.Tint8unsigned
  | Tint I8 Signed => AST.Tint8signed
  | Tint I16 Unsigned => AST.Tint16unsigned
  | Tint I16 Signed => AST.Tint16signed
  | _ => AST.Tret (transl_typ_to_AST_typ t)
  end.

Definition transl_signature (sig: signature) : AST.signature :=
  AST.mksignature
    (transl_typlist_to_AST_typlist sig.(sig_args))
    (transl_typ_to_AST_rettype sig.(sig_res))
    AST.cc_default.

Definition transl_external_function (ef: external_function) : AST.external_function :=
  match ef with
  | EF_external name sig =>
      AST.EF_external name (transl_signature sig)
  end.

Definition transl_unary_operation (op: unary_operation) : Cop.unary_operation :=
  match op with
  | Onotbool => Cop.Onotbool
  | Onotint => Cop.Onotint
  | Oneg => Cop.Oneg
  | Oabsfloat => Cop.Oabsfloat
  end.

Definition transl_binarith_operation (op: binarith_operation) : Cop.binary_operation :=
  match op with
  | Oadd => Cop.Oadd
  | Osub => Cop.Osub
  | Omul => Cop.Omul
  | Odivs => Cop.Odiv
  | Odivu => Cop.Odiv
  | Omods => Cop.Omod
  | Omodu => Cop.Omod
  end.

Definition transl_logical_operation (op: logical_operation) : Cop.binary_operation :=
  match op with
  | Oand => Cop.Oand
  | Oor => Cop.Oor
  | Oxor => Cop.Oxor
  end.

Definition transl_cmp_operation (op: cmp_operation) : Cop.binary_operation :=
  match op with
  | Oeq => Cop.Oeq
  | One => Cop.One
  | Olt => Cop.Olt
  | Ole => Cop.Ole
  | Ogt => Cop.Ogt
  | Oge => Cop.Oge
  end.

Definition transl_cmpu_operation (op: cmpu_operation) : Cop.binary_operation :=
  match op with
  | Oltu => Cop.Olt
  | Oleu => Cop.Ole
  | Ogtu => Cop.Ogt
  | Ogeu => Cop.Oge
  end.

Definition clight_array_idx_addr (te: tenv) (id: ident) (tidx: Clight.expr) : option Clight.expr :=
  do tarr <- te!id;
  match tarr with
  | Tarr _ t =>
      Some (Clight.Ebinop
              Cop.Oadd
              (Clight.Etempvar id (transl_typ tarr))
              (* (Clight.Ecast tidx (Ctypes.Tlong Ctypes.Unsigned noattr)) *)
              tidx
              (Ctypes.Tpointer (transl_typ t) noattr))
  | _ => None
  end.

Fixpoint transl_expr (te: tenv) (exp: Syntax.expr) {struct exp} : option Clight.expr :=
  match exp with
  | Econst (Cint sz sig n) => Some (Econst_int n (transl_typ (Tint sz sig)))
  | Econst (Cint64 sig n) => Some (Econst_long n (transl_typ (Tint64 sig)))
  | Econst (Cfloat32 f) => Some (Econst_single f (transl_typ (Tfloat F32)))
  | Econst (Cfloat64 f) => Some (Econst_float f (transl_typ (Tfloat F64)))
  | Evar id => option_map (fun t => Clight.Etempvar id (transl_typ t)) (te!id)
  | Ecast e _ t =>
      do t  <- type_expression te exp;
      do te <- transl_expr te e;
      Some (Clight.Ecast te (transl_typ t))
  | Eunop op _ e =>
      do t <- type_expression te exp;
      do te <- transl_expr te e;
      Some (Clight.Eunop (transl_unary_operation op) te (transl_typ t))
  | Ebinop_arith op _ e1 e2 =>
      do t <- type_expression te exp;
      do te1 <- transl_expr te e1;
      do te2 <- transl_expr te e2;
      (* match op, typeof te1, typeof te2 with
         | Odivu, Ctypes.Tint sz1 _ _, Ctypes.Tint sz2 _ _
         | Omodu, Ctypes.Tint sz1 _ _, Ctypes.Tint sz2 _ _ =>
           Some (Clight.Ebinop
                   (transl_binarith_operation op)
                   (Clight.Ecast te1 (Ctypes.Tint sz1 Ctypes.Unsigned noattr))
                   (Clight.Ecast te2 (Ctypes.Tint sz2 Ctypes.Unsigned noattr))
                   (transl_typ t))
         | _, _, _ => *)
        Some (Clight.Ebinop (transl_binarith_operation op) te1 te2 (transl_typ t))
      (* end *)
  | Ebinop_logical op e1 e2 =>
      do t <- type_expression te exp;
      do te1 <- transl_expr te e1;
      do te2 <- transl_expr te e2;
      Some (Clight.Ebinop (transl_logical_operation op) te1 te2 (transl_typ t))
  | Ebinop_cmp op _ e1 e2 =>
      do t <- type_expression te exp;
      do te1 <- transl_expr te e1;
      do te2 <- transl_expr te e2;
      Some (Clight.Ebinop (transl_cmp_operation op) te1 te2 (transl_typ t))
  | Ebinop_cmpu op _ e1 e2 =>
      do t <- type_expression te exp;
      do te1 <- transl_expr te e1;
      do te2 <- transl_expr te e2;
      Some (Clight.Ebinop (transl_cmpu_operation op) te1 te2 (transl_typ t))
  | Earr_access id idx =>
      do t <- type_expression te exp;
      do tidx <- transl_expr te idx;
      do addr <- clight_array_idx_addr te id tidx;
      Some (Clight.Ederef addr (transl_typ t))
  end.

Fixpoint transl_exprlist (te: tenv) (le: list expr) : option (list Clight.expr) :=
  match le with
  | [] => Some []
  | exp :: le =>
      do tle <- transl_exprlist te le;
      do texp <- transl_expr te exp;
      Some (texp :: tle)
  end.

Fixpoint transl_identlist (te: tenv) (lids: list ident) : option (list Clight.expr) :=
  match lids with
  | [] => Some []
  | id :: lids =>
      do t <- te!id;
      do tlids <- transl_identlist te lids;
      Some (Clight.Etempvar id (transl_typ t) :: tlids)
  end.

Fixpoint transl_stmt (ge: genv) (f: function) (s: Syntax.stmt) : option Clight.statement :=
  let te := f.(fn_tenv) in
  match s with
  | Sskip => Some Clight.Sskip
  | Sassign id exp =>
      do texp <- transl_expr te exp;
      Some (Clight.Sset id texp)
  | Sarr_assign id idx exp =>
      do tarr <- type_expression te (Evar id);
      do tidx <- transl_expr te idx;
      do texp <- transl_expr te exp;
      do addr <- clight_array_idx_addr te id tidx;
      match type_expression te idx with
      | Some (Tint64 Unsigned) =>
          match type_expression te exp, tarr with
          | Some Tvoid, _ => None
          | Some t0, Tarr _ t1 =>
              if eq_typ t0 t1 then
                Some (Clight.Sassign (Clight.Ederef addr (transl_typ t1)) texp)
              else None
          | _, _ => None
          end
      | _ => None
      end
  | Scall idvar idf args =>
      do targs <- transl_identlist te args;
      match ge!idf with
      | None => None
      | Some (Internal f) =>
          let tparams := transl_typlist (f.(fn_sig).(sig_args)) in
          let tres := transl_typ (f.(fn_sig).(sig_res)) in
          Some (Clight.Scall idvar (Clight.Evar idf (Ctypes.Tfunction tparams tres AST.cc_default)) targs)
      | Some (External ef) =>
          Some (Clight.Sbuiltin
                  idvar
                  (transl_external_function ef)
                  (transl_typlist (ef_sig ef).(sig_args))
                  targs)
      end
  | Sreturn exp =>
      do texp <- transl_expr te exp;
      do ty   <- type_expression te exp;
      if eq_typ ty f.(fn_sig).(sig_res) then
        Some (Clight.Sreturn (Some texp))
      else None
  | Sseq s1 s2 =>
      do ts1 <- transl_stmt ge f s1;
      do ts2 <- transl_stmt ge f s2;
      Some (Clight.Ssequence ts1 ts2)
  | Sifthenelse c s1 s2 =>
      do ts1 <- transl_stmt ge f s1;
      do ts2 <- transl_stmt ge f s2;
      do tc <- transl_expr te c;
      do ty <- type_expression te c;
      if eq_typ ty Tbool then
        Some (Clight.Sifthenelse tc ts1 ts2)
      else None
  | Sloop s =>
      do ts <- transl_stmt ge f s;
      Some (Clight.Sloop ts Clight.Sskip)
  | Sbreak => Some (Clight.Sbreak)
  | Scontinue => Some (Clight.Scontinue)
  | Serror => Some (Clight.Sloop Clight.Sskip Clight.Sskip)
  end.

Fixpoint build_clight_list_ident_type (te: tenv) (l: list ident) : option (list (ident * Ctypes.type)) :=
  match l with
  | [] => Some []
  | id :: l => do t <- te!id;
               do lt <- build_clight_list_ident_type te l;
               Some ((id, transl_typ t) :: lt)
  end.

Definition transl_function (ge: genv) (f: function) : option Clight.function :=
  do params <- build_clight_list_ident_type f.(fn_tenv) f.(fn_params);
  do temps <- build_clight_list_ident_type f.(fn_tenv) f.(fn_vars);
  do tbody <- transl_stmt ge f f.(fn_body);
  Some (Clight.mkfunction (transl_typ f.(fn_sig).(sig_res)) cc_default params [] temps tbody).

Definition transl_fundef (ge: genv) (fd: fundef) : option Clight.fundef :=
  match fd with
  | Internal f =>
      do tf <- transl_function (ge: genv) f;
      Some (Ctypes.Internal tf)
  | External ef =>
      Some (Ctypes.External
              (transl_external_function ef)
              (transl_typlist (ef_sig ef).(sig_args))
              (transl_typ (ef_sig ef).(sig_res))
              cc_default)
  end.

Fixpoint transl_fundefs (ge: genv) (lfd: list (ident * fundef))
  : option (list (ident * AST.globdef Clight.fundef Ctypes.type)) :=
  match lfd with
  | [] => Some []
  | (id, fd) :: l =>
      do tfd <- transl_fundef ge fd;
      do tl <- transl_fundefs ge l;
      Some ((id, Gfun tfd) :: tl)
  end.

Definition transl_program (p: program) : option Clight.program :=
  let ge := build_env (PTree.empty fundef) p.(prog_defs) in
  do tfd <- transl_fundefs ge p.(prog_defs);
  match Ctypes.make_program [] tfd (map fst p.(prog_defs)) p.(prog_main) with
  | Error _ => None
  | OK prog => Some prog
  end.

(*****************************************************************************)
(*                                                                           *)
(*                  TRADUCTION DES ÉTATS DE LA SÉMANTIQUE                    *)
(*                                                                           *)
(*****************************************************************************)

Definition typ_to_memory_chunk (t: typ) : memory_chunk :=
  match t with
  | Tvoid             => Mint8unsigned
  | Tbool             => Mint8unsigned
  | Tint I8 Unsigned  => Mint8unsigned
  | Tint I8 Signed    => Mint8signed
  | Tint I16 Unsigned => Mint16unsigned
  | Tint I16 Signed   => Mint16signed
  | Tint I32 _        => Mint32
  | Tint64 _          => Mint64
  | Tfloat F32        => Mfloat32
  | Tfloat F64        => Mfloat64
  | Tarr _ _          => Mptr
  end.

Definition transl_value (trarr: ident -> (block * ptrofs))
                        (v: value) : val :=
  match v with
  | Vunit       => Vundef
  | Vbool false => CValues.Vfalse
  | Vbool true  => CValues.Vtrue
  | Vint _ _ n    => CValues.Vint n
  | Vint64 _ n    => Vlong n
  | Vfloat32 f  => Vsingle f
  | Vfloat64 f  => Vfloat f
  | Varr id lv  => let (b, ofs) := trarr id in Vptr b ofs
  end.

(* Definition transl_value_shrink (trarr: ident -> (block * ptrofs))
                                  (v: value) : val :=
     match v with
     | Vint I8 Unsigned n => CValues.Vint (Int.zero_ext 8 n)
     | Vint I8 Signed n => CValues.Vint (Int.sign_ext 8 n)
     | Vint I16 Unsigned n => CValues.Vint (Int.zero_ext 16 n)
     | Vint I16 Signed n => CValues.Vint (Int.sign_ext 16 n)
     | _ => transl_value trarr v
     end. *)

Definition transl_valuelist (fm: ident -> (block * ptrofs))
                            (lv: list value) : list val :=
  map (transl_value fm) lv.

Fixpoint complete_env (vars: list ident) (e: env) : env :=
  match vars with
  | []         => e
  | id :: vars =>
      match e!id with
      | None   => complete_env vars (PTree.set id Vunit e)
      | Some _ => complete_env vars e
      end
  end.

Definition transl_env (trarr: ident -> (block * ptrofs)) (vars: list ident)
                    (e: env) : temp_env :=
  PTree.map (fun _ => transl_value trarr) (complete_env vars e).

Definition valid_trarr (trarr: ident -> (block * ptrofs)) :=
  forall idarr idarr', idarr <> idarr' -> fst (trarr idarr) <> fst (trarr idarr').

Definition match_mem' (tp: Clight.program)
                      (trarr: ident -> (block * ptrofs))
                      (l: list (ident * memory_block)) (mcl: Memory.mem) : Prop :=
  Forall (fun (x: (ident * memory_block)) =>
            let (idarr, blk) := x in
            let (b, ofs) := trarr idarr in
            let chunk := typ_to_memory_chunk (blk.(blk_type)) in
            forall (idx: nat), (idx < length blk.(blk_values))%nat ->
                               (Z.of_nat idx <= Int64.max_unsigned) ->
                               Ptrofs.unsigned ofs +
                                 sizeof (globalenv tp) (transl_typ blk.(blk_type)) * Z.of_nat idx
                               <= Ptrofs.max_unsigned /\
                               Mem.valid_access mcl chunk b
                                 (Ptrofs.unsigned
                                    (Ptrofs.add
                                       ofs
                                       (Ptrofs.mul
                                          (Ptrofs.repr
                                             (sizeof (globalenv tp) (transl_typ blk.(blk_type))))
                                          (Ptrofs.repr (Z.of_nat idx))))) Writable /\
                               Mem.loadv chunk mcl
                                 (Vptr b (Ptrofs.add
                                            ofs
                                            (Ptrofs.mul
                                               (Ptrofs.repr
                                                  (sizeof (globalenv tp) (transl_typ blk.(blk_type))))
                                               (Ptrofs.repr (Z.of_nat idx)))))
                               = option_map (transl_value trarr)
                                            (nth_error blk.(blk_values) idx)) l.

Definition match_mem tp trarr m mcl := match_mem' tp trarr (PTree.elements m) mcl.

Definition transl_valid_access (tp: Clight.program) (l: list (ident * memory_block))
                               (tm: Mem.mem) (trarr: ident -> (block * ptrofs)) :=
  forall idarr blk idx,
    In (idarr, blk) l ->
    (idx < length blk.(blk_values))%nat ->
    Mem.valid_access tm (typ_to_memory_chunk blk.(blk_type)) (fst (trarr idarr))
                     (Ptrofs.unsigned (snd (trarr idarr)) +
                      (sizeof (globalenv tp) (transl_typ blk.(blk_type))) * Z.of_nat idx) Writable.

Record transl_mem_u_res (tp: Clight.program)
                        (l: list (ident * memory_block))
                        (bound: nat) := mk_tr_mem_u_res {
                    tmemu: Mem.mem;
                   trarru: ident -> (block * ptrofs);
       tmemu_valid_access: transl_valid_access tp l tmemu trarru;
   tmemu_nextblock_length: Zpos (Mem.nextblock tmemu) <= Z.of_nat (length l) + 1;
          trarru_snd_zero: forall idarr, snd (trarru idarr) = Ptrofs.zero;
        trarru_fst_bounds: forall idarr, (fst (trarru idarr) < (Mem.nextblock tmemu))%positive
                                         \/ (fst (trarru idarr) > Pos.of_nat bound)%positive;
             trarru_valid: valid_trarr trarru
  }.

Lemma transl_typ_sizeof_prog_comp_env:
  forall (tp: Clight.program) t,
    sizeof (prog_comp_env tp) (transl_typ t) = typ_sizeof t.
Proof.
  destruct t; try destruct i; try destruct f; simpl;
    try destruct Archi.ptr64; reflexivity.
Qed.

Lemma transl_typ_sizeof:
  forall tp t,
    sizeof (globalenv tp) (transl_typ t) = typ_sizeof t.
Proof. simpl. exact transl_typ_sizeof_prog_comp_env. Qed.

Lemma typ_sizeof_typ_to_memory_chunk:
  forall t, size_chunk (typ_to_memory_chunk t) = typ_sizeof t.
Proof.
  destruct t; try destruct i; try destruct s; try destruct f; simpl; try lia.
  unfold Mptr; destruct Archi.ptr64; simpl; lia.
Qed.

Lemma typ_sizeof_bounds:
  forall t, 0 < typ_sizeof t <= 8.
Proof.
  destruct t; try destruct i; try destruct f; simpl; try destruct Archi.ptr64; simpl; lia.
Qed.

Definition transl_mem_uninitialized (tp: Clight.program) (m: mem)
  : transl_mem_u_res tp (PTree.elements m) (length (PTree.elements m)).
  pose proof (PTree.elements_keys_norepet m).
  specialize (Z.le_refl (Z.of_nat (length (PTree.elements m)))).
  generalize (length (PTree.elements m)) at 2 3. intros N HN.
  induction (PTree.elements m).
  + refine (mk_tr_mem_u_res tp [] N
              Mem.empty
              (fun idarr => (Pos.add (Pos.of_nat N) idarr, Ptrofs.zero))
              _ _ _ _ _).
    unfold transl_valid_access. contradiction. simpl. lia. reflexivity.
    intro. simpl. lia.
    unfold valid_trarr. intros. simpl. intro. apply H0.
    apply Pos.add_reg_l with (1 := H1).
  + destruct a as [idarr blk].
    rewrite map_cons in H. simpl in H. apply Coqlib_list_norepet_cons_inv in H.
    destruct H as [Hnotin Hnorepet]. specialize (IHl Hnorepet). destruct IHl.
    simpl in HN. rewrite Znat.Zpos_P_of_succ_nat in HN. unfold Z.succ in HN. lia.
    destruct (Mem.alloc tmemu0 0 (sizeof (prog_comp_env tp) (transl_typ (blk_type blk))
                                  * Z.of_nat (Datatypes.length blk.(blk_values))))
      as [tm' b] eqn:Halloc.
    apply mk_tr_mem_u_res with (tmemu  := tm')
                               (trarru := fun id =>
                                          if Pos.eqb id idarr then (b, Ptrofs.zero)
                                          else trarru0 id).
    unfold transl_valid_access. intros. destruct H.
    - injection H. intros [= <-] [= <-]. clear H. rewrite Pos.eqb_refl. simpl.
      apply Mem.valid_access_implies with (p1 := Freeable) (2 := perm_F_any Writable).
      change (Ptrofs.unsigned Ptrofs.zero) with 0. simpl.
      apply Mem.valid_access_alloc_same with (1 := Halloc).
      * apply Z.mul_nonneg_nonneg.
        destruct (blk_type blk); try destruct i; try destruct f; simpl;
          try destruct Archi.ptr64; simpl; lia. lia.
      * rewrite transl_typ_sizeof_prog_comp_env, typ_sizeof_typ_to_memory_chunk.
        apply Znat.inj_lt in H0. rewrite <- Z.mul_succ_r. apply Z.mul_le_mono_pos_l.
        apply typ_sizeof_bounds. lia.
      * destruct idx.
        ** rewrite Z.mul_0_r. exact (Z.divide_0_r _).
        ** assert (forall x: positive, Z.pos x~0 = Z.pos x * 2). lia.
           destruct (blk_type blk); simpl;
             try exact (Z.divide_1_l _);
             try destruct i; try destruct s; try destruct f; simpl;
             try (unfold Mptr; destruct Archi.ptr64; simpl);
             try exact (Z.divide_1_l _);
             repeat rewrite H with (x := (_~0)%positive);
             try rewrite H with (x := Pos.of_succ_nat idx);
             repeat rewrite Zmult_assoc_reverse;
             try exact (Z.divide_factor_r _ _).
           apply Z.divide_mul_r. exact (Z.divide_factor_r _ _).
           apply Z.divide_mul_r. exact (Z.divide_factor_r _ _).
    - specialize (tmemu_valid_access0 _ _ idx H H0). destruct (trarru0 idarr0) eqn:TRarr0.
      destruct (Pos.eq_dec idarr0 idarr) as [[= ->] | Hidarr_diff];
        [apply in_map_pair_fst in H; contradiction
        |rewrite (proj2 (Pos.eqb_neq _ _) Hidarr_diff)]. simpl in *.
      apply Mem.valid_access_alloc_other with (1 := Halloc) (2 := tmemu_valid_access0).
    - rewrite Mem.nextblock_alloc with (1 := Halloc). simpl.
      rewrite Pos2Z.inj_add, Znat.Zpos_P_of_succ_nat, Pos2Z.inj_succ.
      unfold Z.succ. apply Z.add_le_mono_r. assumption.
    - intro. destruct ((idarr0 =? idarr)%positive); eauto.
    - intro. destruct (Pos.eq_dec idarr0 idarr) as [[= ->] | H].
      * rewrite Pos.eqb_refl. left. simpl.
        rewrite Mem.nextblock_alloc with (1 := Halloc).
        rewrite Mem.alloc_result with (1 := Halloc). lia.
      * rewrite (proj2 (Pos.eqb_neq _ _) H).
        rewrite Mem.nextblock_alloc with (1 := Halloc).
        destruct (trarru_fst_bounds0 idarr0). lia. lia.
    - unfold valid_trarr. intros.
      destruct (Pos.eq_dec idarr0 idarr), (Pos.eq_dec idarr' idarr).
      * congruence.
      * revert e; intros [= ->]. rewrite Pos.eqb_refl.
        rewrite (proj2 (Pos.eqb_neq _ _) n). simpl.
        rewrite Mem.alloc_result with (1 := Halloc).
        destruct (trarru_fst_bounds0 idarr'). lia.
        simpl in HN. rewrite Znat.Zpos_P_of_succ_nat in HN. unfold Z.succ in HN.
        pose proof (Z.le_trans _ _ _ tmemu_nextblock_length0 HN). lia.
      * revert e; intros [= ->]. rewrite Pos.eqb_refl.
        rewrite (proj2 (Pos.eqb_neq _ _) n). simpl.
        rewrite Mem.alloc_result with (1 := Halloc).
        destruct (trarru_fst_bounds0 idarr0). lia.
        simpl in HN. rewrite Znat.Zpos_P_of_succ_nat in HN. unfold Z.succ in HN.
        pose proof (Z.le_trans _ _ _ tmemu_nextblock_length0 HN). lia.
      * rewrite (proj2 (Pos.eqb_neq _ _) n), (proj2 (Pos.eqb_neq _ _) n0). eauto.
Defined.

Theorem transl_mem_uninitialized_valid_access:
  forall tp m tm trarr H Hlength Hzero Hbounds Hvalid,
    transl_mem_uninitialized tp m = {| tmemu  := tm;
                                       trarru := trarr;
                                       tmemu_valid_access := H;
                                       tmemu_nextblock_length := Hlength;
                                       trarru_snd_zero := Hzero;
                                       trarru_fst_bounds := Hbounds;
                                       trarru_valid := Hvalid |} ->
    forall idarr blk idx,
      In (idarr, blk) (PTree.elements m) ->
      (idx < length blk.(blk_values))%nat ->
      Mem.valid_access tm (typ_to_memory_chunk blk.(blk_type)) (fst (trarr idarr))
        (Ptrofs.unsigned
           (Ptrofs.add
              (snd (trarr idarr))
              (Ptrofs.mul
                 (Ptrofs.repr
                    (sizeof (globalenv tp) (transl_typ blk.(blk_type))))
                 (Ptrofs.repr (Z.of_nat idx))))) Writable.
Proof.
  intros. pose proof (H _ _ _ H1 H2).
  pose proof (blk_valid_size blk) as valid_size.
  rewrite (Hzero idarr) in *.
  pose proof (typ_sizeof_bounds (blk_type blk)).
  rewrite transl_typ_sizeof in *.
  pose proof (Ptrofs_max_unsigned_gt_8).
  unshelve epose proof (Zmult_le_nonneg_nonneg_r _ _ _ (proj1 H4) _ valid_size). lia.
  rewrite Ptrofs.add_zero_l.
  unfold Ptrofs.mul. rewrite (Ptrofs.unsigned_repr (typ_sizeof _)),
                             (Ptrofs.unsigned_repr (Z.of_nat _)) by lia.
  rewrite Ptrofs.unsigned_repr. exact H3.
  split. destruct idx; [lia|];
    destruct (blk_type blk); try destruct i; try destruct f;
    simpl; try destruct Archi.ptr64; simpl; try lia.
  apply Z.le_trans with (2 := valid_size), Z.mul_le_mono_pos_l; lia.
Qed.

Definition valid_access (tp: Clight.program) (trarr: ident -> (block * ptrofs))
                        (m: mem) (tmem: Mem.mem) :=
  forall idarr blk idx,
    In (idarr, blk) (PTree.elements m) ->
    (idx < length (blk_values blk))%nat ->
    Mem.valid_access tmem (typ_to_memory_chunk (blk_type blk)) (fst (trarr idarr))
      (Ptrofs.unsigned
         (Ptrofs.add (snd (trarr idarr))
            (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv tp) (transl_typ (blk_type blk))))
               (Ptrofs.repr (Z.of_nat idx))))) Writable.

Record transl_mem_res (tp: Clight.program) (m: mem)
                      (l: list (ident * memory_block)) := mk_tr_mem_res {
    tr_mem: Mem.mem;
    tr_arr: ident -> (block * ptrofs);
    vaccess: valid_access tp tr_arr m tr_mem;
    mmem: match_mem' tp tr_arr l tr_mem;
    tr_arr_snd_zero: forall idarr : ident, snd (tr_arr idarr) = Ptrofs.zero;
    tr_arr_valid: valid_trarr tr_arr
  }.

Definition transl_mem_values (tp: Clight.program) (trarr: ident -> (block * ptrofs))
  (m: mem) (tm0: Mem.mem) (b: block) (lv: list value) (t: typ)
  (l: list (ident * memory_block))
  (Hshrunk: Forall (fun v => v = shrink v) lv)
  (Hsep: forall idarr blk, In (idarr, blk) l -> fst (trarr idarr) <> b)
  (VACCESS: valid_access tp trarr m tm0)
  (MMEM: match_mem' tp trarr l tm0)
  (Hwt: Forall (fun v => well_typed_value v t) lv)
  (Hsize: typ_sizeof t * Z.of_nat (length lv) <= Ptrofs.max_unsigned)
  (H: forall idx,
      (idx < length lv)%nat ->
      Mem.valid_access tm0 (typ_to_memory_chunk t) b
        (Ptrofs.unsigned
           (Ptrofs.mul
              (Ptrofs.repr
                 (sizeof (globalenv tp) (transl_typ t)))
              (Ptrofs.repr (Z.of_nat idx)))) Writable)
  : {tm: Mem.mem |
      match_mem' tp trarr l tm /\
      valid_access tp trarr m tm /\
      (forall idx,
          (idx < length lv)%nat ->
          sizeof (globalenv tp) (transl_typ t) * Z.of_nat idx <= Ptrofs.max_unsigned /\
          Mem.valid_access tm (typ_to_memory_chunk t) b
            (Ptrofs.unsigned
               (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv tp) (transl_typ t)))
                  (Ptrofs.repr (Z.of_nat idx)))) Writable) /\
       forall idx: nat,
         (0 <= idx < length lv)%nat ->
         Z.of_nat idx <= Int64.max_unsigned ->
         Mem.loadv (typ_to_memory_chunk t) tm
           (Vptr b
              (Ptrofs.mul (Ptrofs.repr (sizeof (globalenv tp) (transl_typ t)))
                 (Ptrofs.repr (Z.of_nat idx)))) =
         option_map (transl_value trarr) (nth_error lv (idx - 0)) }.
  pose proof (eq_refl (length lv)).
  rewrite <- plus_O_n in H0 at 1.
  rewrite transl_typ_sizeof in *.
  revert H0 H. generalize 0%nat at 1 2 3 as D. revert Hsize.
  generalize (length lv) at 1 3 4 5 6 as N. intros N HN.
  induction lv; simpl; intros.
  + exists tm0. split; [exact MMEM | split; [exact VACCESS |split; [|simpl; lia]]].
    intros. split.
    - apply Z.le_trans with (2 := HN). apply Z.mul_le_mono_nonneg_l.
      pose proof (typ_sizeof_bounds t). lia. lia.
    - eauto.
  + rewrite <- plus_n_Sm, <- plus_Sn_m in H0.
    specialize (IHlv (Forall_inv_tail Hshrunk) (Forall_inv_tail Hwt) _ H0 H).
    clear tm0 H MMEM VACCESS.
    destruct IHlv as [tm [MMEM [VACCESS [IH1 IH2]]]]. apply Forall_inv in Hwt.
    assert ((D < N)%nat). lia.
    pose proof (Mem.valid_access_store _ _ _ _ (transl_value trarr a) (proj2 (IH1 _ H))).
    destruct X as [tm' Hstore]. exists tm'.
    split; [| split; [| split; [intros; specialize (IH1 _ H1); split|]]].
    - apply Forall_forall. pose proof (proj1 (Forall_forall _ _) MMEM). intros.
      simpl in *. specialize (H1 _ H2).
      destruct x as [idarr blk]. destruct (trarr idarr) as [b0 ofs0] eqn:TRarr.
      intros. specialize (H1 idx H3 H4). decompose [and] H1. split; [|split].
      * tauto.
      * apply Mem.store_valid_access_1 with (1 := Hstore) (2 := H7).
      * rewrite Mem.load_store_other with (1 := Hstore). assumption.
        specialize (Hsep _ _ H2). rewrite TRarr in Hsep. eauto.
    - unfold valid_access. intros.
      apply Mem.store_valid_access_1 with (1 := Hstore). eauto.
    - tauto.
    - apply Mem.store_valid_access_1 with (1 := Hstore) (2 := proj2 IH1).
    - intros idx Hbounds Hintsize.
      destruct Hbounds as [Hlow Hhigh]. apply Lt.le_lt_or_eq in Hlow.
      destruct Hlow as [Hlow | [= <-]].
      * apply Lt.lt_le_S in Hlow.
        pose proof (conj Hlow Hhigh) as Hbounds. clear Hlow Hhigh.
        specialize (IH2 _ Hbounds Hintsize).
        rewrite Mem.load_store_other with (1 := Hstore).
        ** simpl in IH2. rewrite IH2. apply f_equal.
           rewrite PeanoNat.Nat.sub_succ_r.
           rewrite (Lt.S_pred_pos (idx - D)) by lia. reflexivity.
        ** right. right.
           pose proof (typ_sizeof_bounds t).
           pose proof (Ptrofs_max_unsigned_gt_8).
           unfold Ptrofs.mul. rewrite (Ptrofs.unsigned_repr (typ_sizeof _)) by lia.
           rewrite typ_sizeof_typ_to_memory_chunk.
           unshelve epose proof (Zmult_le_nonneg_nonneg_r _ _ _ _ _ HN). lia. lia.
           pose proof (Z.le_trans _ _ _ (Z.lt_le_incl _ _ (Znat.inj_lt _ _ H)) H3).
           repeat rewrite (Ptrofs.unsigned_repr (Z.of_nat _)) by lia.
           repeat rewrite Ptrofs.unsigned_repr.
           rewrite <- (Z.mul_1_r (typ_sizeof _)) at 2. rewrite <- Z.mul_add_distr_l.
           apply Z.mul_le_mono_nonneg_l. lia. lia.
           all: (split; [lia|apply Z.le_trans with (2 := HN), Z.mul_le_mono_nonneg_l; lia]).
      * rewrite Mem.load_store_same with (1 := Hstore), PeanoNat.Nat.sub_diag.
        simpl. apply Forall_inv in Hshrunk.
        destruct a; try destruct i; try destruct s; inversion Hwt; simpl in *;
          try (injection Hshrunk; intros [= <-]); try reflexivity.
        destruct b0; reflexivity. destruct (trarr p); reflexivity.
Defined.

Definition transl_mem' (tp: Clight.program) (m: mem)
  : transl_mem_res tp m (PTree.elements m).
  destruct (transl_mem_uninitialized tp m) eqn:Htru.
  specialize transl_mem_uninitialized_valid_access with (1 := Htru) as H. clear Htru.
  clear trarru_fst_bounds0 tmemu_valid_access0 tmemu_nextblock_length0.
  refine (list_rect_In (PTree.elements m) (fun l => NoDup (map fst l) -> transl_mem_res tp m l)
          (fun l0 IH x Hin Hnodup => _)
          (fun Hnodup =>
             mk_tr_mem_res tp m [] tmemu0 trarru0 H _ trarru_snd_zero0 trarru_valid0) _).
  + rewrite map_cons in Hnodup. apply NoDup_cons_iff in Hnodup. destruct Hnodup as [Hnotin Hnodup].
    destruct (IH Hnodup). destruct x as [idarr blk].
    destruct (tr_arr0 idarr) as [b ofs] eqn:TRarr.
    pose (chunk := typ_to_memory_chunk (blk_type blk)).
    pose proof (transl_mem_values tp tr_arr0 m tr_mem0 b (blk_values blk) (blk_type blk)).
    assert (forall (idarr : ident) (blk : memory_block),
               In (idarr, blk) l0 -> fst (tr_arr0 idarr) <> b).
    intros. simpl in Hnotin. apply in_map_pair_fst in H0.
    pose proof (list_in_diff _ _ _ H0 Hnotin). specialize (tr_arr_valid0 _ _ H1).
    rewrite TRarr in tr_arr_valid0. assumption.
    specialize X with (1 := blk_values_shrunk blk) (2 := H0) (3 := vaccess0) (4 := mmem0)
                      (5 := blk_well_typed blk) (6 := blk_valid_size blk).
    destruct X as [tm [MMEM [VACCESS [Htm1 Htm2]]]].
    intro idx. pose proof (vaccess0 _ _ idx Hin).
    rewrite (tr_arr_snd_zero0 idarr), Ptrofs.add_zero_l, TRarr in H1. assumption.
    refine (mk_tr_mem_res tp m _ tm tr_arr0 VACCESS _ tr_arr_snd_zero0 tr_arr_valid0).
    unfold match_mem'. apply Forall_forall.
    pose proof (proj1 (Forall_forall _ _) MMEM). simpl in H1.
    intros. destruct H2 as [[= <-] | H2].
    - pose proof (tr_arr_snd_zero0 idarr). rewrite TRarr in *. revert H2; intros [= ->].
      intros. rewrite Ptrofs.add_zero_l. split; [| split].
      * pose proof (blk_valid_size blk). change (Ptrofs.unsigned Ptrofs.zero) with 0. simpl.
        rewrite transl_typ_sizeof_prog_comp_env. apply Z.le_trans with (2 := H4).
        apply Z.mul_le_mono_pos_l. apply typ_sizeof_bounds. lia.
      * exact (proj2 (Htm1 _ H2)).
      * specialize (Htm2 idx). rewrite PeanoNat.Nat.sub_0_r in Htm2. apply Htm2; lia.
    - specialize (H1 _ H2). assumption.
  + exact (Forall_nil _).
  + pose proof (PTree.elements_keys_norepet m). clear H. induction (PTree.elements m).
    exact (NoDup_nil _).
    inversion_clear H0. rewrite map_cons. apply NoDup_cons; eauto.
Defined.

(* Definition transl_mem (tp: Clight.program) (m: mem)
                         : {x | match_mem tp (fst x) m (snd x)}.
     destruct (transl_mem' tp m). exists (trarr0, tmem0). assumption.
   Defined. *)

Definition transl_mem (tp: Clight.program) (m: mem) :=
  let tr := transl_mem' tp m in
  (tr_arr tp m (PTree.elements m) tr, tr_mem tp m (PTree.elements m) tr).

Theorem transl_mem_match:
  forall tp m trarr tm,
    transl_mem tp m = (trarr, tm) ->
    match_mem tp trarr m tm.
Proof.
  intros. unfold transl_mem in H. destruct (transl_mem' tp m).
  injection H. intros [= <-] [= <-]. assumption.
Qed.

Fixpoint transl_cont (fm: ident -> (block * ptrofs))
                     (ge: genv) (f: option function)
                     (k: cont) : option Clight.cont :=
  match k with
  | Kstop => Some Clight.Kstop
  | Kseq s k =>
      do f' <- f;
      do ts <- transl_stmt ge f' s;
      do tk <- transl_cont fm ge f k;
      Some (Clight.Kseq ts tk)
  | Kloop s k =>
      do f' <- f;
      do ts <- transl_stmt ge f' s;
      do tk <- transl_cont fm ge f k;
      Some (Clight.Kloop1 ts Clight.Sskip tk)
  | Kreturnto id e f k =>
      let te := transl_env fm (f.(fn_vars) ++ f.(fn_params)) e in
      do tf <- transl_function ge f;
      do tk <- transl_cont fm ge (Some f) k;
      Some (Clight.Kcall id tf PTree.Empty te tk)
  end.

Inductive match_states (p: program) : state -> Clight.state -> Prop :=
| match_states_State: forall tp trarr m e f s k tm te tf ts tk
    (VTRARR  : valid_trarr trarr)
    (TPROG   : transl_program p = Some tp)
    (TF      : transl_function (genv_of_program p) f = Some tf)
    (TS      : transl_stmt (genv_of_program p) f s = Some ts)
    (TK      : transl_cont trarr (genv_of_program p) (Some f) k = Some tk)
    (TE      : transl_env trarr (f.(fn_vars) ++ f.(fn_params)) e = te)
    (MMEM    : match_mem tp trarr m tm),
    match_states p (State m e f s k) (Clight.State tf ts tk PTree.Empty te tm)
| match_states_Callstate: forall tp trarr m fd vargs k tm tfd tvargs tk
    (VTRARR  : valid_trarr trarr)
    (TPROG   : transl_program p = Some tp)
    (TFD     : transl_fundef (genv_of_program p) fd = Some tfd)
    (TVARGS  : transl_valuelist trarr vargs = tvargs)
    (TK      : transl_cont trarr (genv_of_program p) None k = Some tk)
    (MMEM    : match_mem tp trarr m tm),
    match_states p (Callstate m fd vargs k) (Clight.Callstate tfd tvargs tk tm)
| match_states_Returnstate: forall tp trarr m r k tm tk
    (VTRARR  : valid_trarr trarr)
    (TPROG   : transl_program p = Some tp)
    (TK      : transl_cont trarr (genv_of_program p) None k = Some tk)
    (MMEM    : match_mem tp trarr m tm),
    match_states p (Returnstate m r k) (Clight.Returnstate (transl_value trarr r) tk tm).

Lemma complete_env_correct:
  forall vars e id v,
    e ! id = Some v ->
    (complete_env vars e) ! id = Some v.
Proof.
  induction vars. eauto.
  simpl. intros. destruct e!a eqn:Ha. eauto.
  apply IHvars. rewrite PTree.gsspec.
  destruct (Coqlib.peq id a). rewrite e0, Ha in H. discriminate. eauto.
Qed.

Lemma transl_env_correct:
  forall trarr vars e id v,
    e ! id = Some v ->
    (transl_env trarr vars e) ! id = Some (transl_value trarr v).
Proof.
  intros. unfold transl_env. rewrite PTree.gmap.
  apply complete_env_correct with (vars := vars) in H.
  unfold Coqlib.option_map. rewrite H. reflexivity.
Qed.

Lemma PTree_set_order_independent {A: Type}:
  forall e i1 i2 (x1 x2: A),
    i1 <> i2 ->
    PTree.set i1 x1 (PTree.set i2 x2 e) = PTree.set i2 x2 (PTree.set i1 x1 e).
Proof.
  intros. apply PTree.extensionality; intro.
  repeat rewrite PTree.gsspec.
  destruct (Coqlib.peq i i1), (Coqlib.peq i i2); congruence || reflexivity.
Qed.

Lemma complete_env_set:
  forall vars e id v,
    complete_env vars (PTree.set id v e) = PTree.set id v (complete_env vars e).
Proof.
  induction vars. eauto.
  simpl. intros. rewrite PTree.gsspec. destruct Coqlib.peq.
  + rewrite e0. destruct e!id eqn:H. eauto.
    rewrite (IHvars e id Vunit). rewrite PTree.set2. eauto.
  + destruct e!a. eauto. rewrite <- (IHvars _ id v).
    rewrite PTree_set_order_independent with (1 := n). reflexivity.
Qed.

Lemma transl_env_set:
  forall trarr vars e id v,
    transl_env trarr vars (PTree.set id v e)
    = PTree.set id (transl_value trarr v) (transl_env trarr vars e).
Proof.
  intros. unfold transl_env. rewrite complete_env_set.
  rewrite PTree_map_set. reflexivity.
Qed.

Lemma transl_expr_correct_type:
  forall te exp cexp,
    transl_expr te exp = Some cexp ->
    (do t <- type_expression te exp; Some (transl_typ t)) = Some (typeof cexp).
Proof.
  destruct exp; simpl; intros.
  + destruct te!i; try discriminate. revert H; intros [= <-]. reflexivity.
  + destruct c; revert H; intros [= <-]; reflexivity.
  + destruct type_expression; try discriminate.
    destruct t1, t0, transl_expr; try discriminate;
      destruct eq_typ; try discriminate;
      revert H; intros [= <-]; reflexivity.
  + destruct u; destruct type_expression; try discriminate;
      destruct transl_expr; try discriminate;
      destruct t, o; try destruct f; try discriminate;
      revert H; intros [= <-]; reflexivity.
  + destruct b; try discriminate;
      destruct type_expression, type_expression; try discriminate;
      destruct transl_expr, transl_expr;
      destruct t; try discriminate; try destruct t0; try discriminate;
      try destruct s; try destruct s0; try discriminate;
      try destruct i, i0; try discriminate;
      try destruct f; try destruct f0; try discriminate;
      try destruct o; try discriminate;
      revert H; intros [= <-]; reflexivity.
  + destruct type_expression, type_expression; try discriminate;
      destruct transl_expr, transl_expr;
      destruct t; try destruct t0; try discriminate;
      revert H; intros [= <-]; reflexivity.
  + destruct type_expression, type_expression; try discriminate;
      destruct transl_expr, transl_expr;
      destruct t; try destruct t0; try discriminate;
      try destruct s; try destruct s0; try discriminate;
      try destruct i, i0; try discriminate;
      try destruct f; try destruct f0; try discriminate;
      try destruct o; try discriminate;
      revert H; intros [= <-]; reflexivity.
  + destruct type_expression, type_expression; try discriminate;
      destruct transl_expr, transl_expr;
      destruct t; try destruct t0; try discriminate;
      try destruct s; try destruct s0; try discriminate;
      try destruct i; try destruct i0; try discriminate;
      try destruct f; try destruct f0; try discriminate;
      try destruct o; try discriminate;
      revert H; intros [= <-]; reflexivity.
  + destruct type_expression; try discriminate.
    destruct t; try discriminate. destruct s; try discriminate.
    destruct te!i; try discriminate. destruct t; try discriminate.
    destruct transl_expr; try discriminate.
    simpl in H. destruct clight_array_idx_addr; try discriminate.
    revert H; intros [= <-]; reflexivity.
Qed.

Lemma transl_expr_sem_preservation:
  forall trarr p tp m tm e f tf exp cexp v, forall
    (TRPROG: transl_program p = Some tp)
    (MMEM: match_mem tp trarr m tm)
    (TRFUNC: transl_function (genv_of_program p) f = Some tf)
    (TREXP: transl_expr f.(fn_tenv) exp = Some cexp)
    (EVEXP: eval_expr m e f exp v),
    Clight.eval_expr (globalenv tp) PTree.Empty (transl_env trarr (f.(fn_vars) ++ f.(fn_params)) e) tm cexp (transl_value trarr v).
Proof.
  intros. revert cexp v TREXP EVEXP. induction exp; simpl; intros.
  + inversion EVEXP. rewrite H1 in TREXP. revert TREXP; intros [= <-].
    apply Clight.eval_Etempvar. apply transl_env_correct. assumption.
  + destruct c; inversion EVEXP; revert TREXP; intros [= <-].
    - apply Clight.eval_Econst_int.
    - apply Clight.eval_Econst_long.
    - apply Clight.eval_Econst_single.
    - apply Clight.eval_Econst_float.
  + inversion EVEXP. rewrite_equalities.
    destruct type_expression eqn:Htexp; try discriminate;
      destruct t, t1; try discriminate; destruct eq_typ eqn:Heq; try discriminate;
      destruct transl_expr eqn:Hexp; try discriminate; revert TREXP; intros [= <-];
      (eapply Clight.eval_Ecast; [ eauto |]);
      apply eq_typ_correct in Heq; revert Heq; intros [= ->];
      eapply transl_expr_correct_type in Hexp; rewrite Htexp in Hexp; revert Hexp; intros [= <-];
      revert H5; inversion_clear H4;
      try destruct i; try destruct s; try destruct i0; try destruct s0; try discriminate;
      try destruct (f0: floatsize); try destruct (f1: floatsize);
      simpl; unfold Cop.sem_cast; simpl;
      try destruct (Float.to_int f1); try destruct (Float32.to_int f1);
      try destruct (Float.to_intu f1); try destruct (Float32.to_intu f1);
      try destruct (Float.to_long f1); try destruct (Float32.to_long f1);
      try destruct (Float.to_longu f1); try destruct (Float32.to_longu f1);
      intros [= <-]; reflexivity.
  + inversion EVEXP. rewrite_equalities.
    destruct op; destruct type_expression eqn:Htexp; try discriminate;
      destruct t; try discriminate; destruct transl_expr eqn:Hexp; try discriminate; revert TREXP;
      try destruct i; try destruct s; try destruct (f0: floatsize); destruct k; try discriminate;
      intros [= <-]; (eapply Clight.eval_Eunop; [ eauto |]);
      eapply transl_expr_correct_type in Hexp; rewrite Htexp in Hexp; revert Hexp; intros [= <-];
      destruct v1; try discriminate; revert H4; intros [= <-]; try reflexivity;
      try destruct b; try destruct i, s; reflexivity.
  + inversion EVEXP. rewrite_equalities.
    destruct op; destruct (type_expression (fn_tenv f) e1) eqn:Htexp1,
                          (type_expression (fn_tenv f) e2) eqn:Htexp2;
      try discriminate; destruct t; try destruct t0; try discriminate;
      try destruct i; try destruct s; try destruct i0; try destruct s0; try discriminate;
      try destruct (f0: floatsize); try destruct (f1: floatsize);
      try destruct k; try discriminate;
      destruct (transl_expr (fn_tenv f) e1) eqn:Hexp1,
               (transl_expr (fn_tenv f) e2) eqn:Hexp2; try discriminate;
      revert TREXP; intros [= <-]; eapply Clight.eval_Ebinop; try eauto;
      destruct v1, v2; try discriminate;
      apply transl_expr_correct_type in Hexp1, Hexp2;
      rewrite Htexp1 in Hexp1; rewrite Htexp2 in Hexp2; revert Hexp1 Hexp2; intros [= <-] [= <-].
    all: (try destruct (i: intsize); try destruct (i1: intsize); try discriminate).
    all: (revert H6; try intros [= <-]; try reflexivity; simpl; intros H6).
    all: (cbn; unfold sem_div, sem_mod; unfold Cop.sem_binarith; unfold Cop.sem_cast; simpl;
          destruct Archi.ptr64; [| try (destruct intsize_eq; [| contradiction])];
          simpl; unfold divs, divs64, divu, divu64, mods, mods64, modu, modu64 in H6;
          try destruct (Int.eq i2 Int.zero);
          try destruct (Int.eq i0 (Int.repr Int.min_signed) && Int.eq i2 Int.mone);
          try destruct (Int64.eq i0 Int64.zero);
          try destruct (Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone);
          try destruct eq_signedness;
          try discriminate; revert H6; intros [= <-]; reflexivity).
  + inversion EVEXP. rewrite_equalities. destruct op;
      destruct (type_expression (fn_tenv f) e1) eqn:Htexp1,
               (type_expression (fn_tenv f) e2) eqn:Htexp2;
      try discriminate; destruct t; try destruct t0; try discriminate;
      destruct (transl_expr (fn_tenv f) e1) eqn:Hexp1,
               (transl_expr (fn_tenv f) e2) eqn:Hexp2; try discriminate;
      specialize (IHexp1 _ _ eq_refl H2);
      specialize (IHexp2 _ _ eq_refl H4); revert TREXP; intros [= <-];
      apply Clight.eval_Ebinop with (v1 := transl_value trarr v1)
                                    (v2 := transl_value trarr v2)
                                    (1 := IHexp1) (2 := IHexp2);
      apply transl_expr_correct_type in Hexp1, Hexp2;
      rewrite Htexp1 in Hexp1; rewrite Htexp2 in Hexp2;
      revert Hexp1 Hexp2; intros [= <-] [= <-];
      destruct v1, v2; try discriminate;
      revert H5; intros [= <-]; destruct b, b0; reflexivity.
  + inversion EVEXP. rewrite_equalities.
    destruct (type_expression (fn_tenv f) e1) eqn:Htexp1,
             (type_expression (fn_tenv f) e2) eqn:Htexp2; try discriminate.
    all: (destruct t; try destruct t0; try discriminate).
    all: (destruct (transl_expr (fn_tenv f) e1) eqn:Hexp1,
                   (transl_expr (fn_tenv f) e2) eqn:Hexp2; try discriminate).
    all: (try destruct i; try destruct i0; try destruct s; try destruct s0; 
          try destruct f0; try destruct f1; try discriminate).
          (* ici, ajouter un rewrite pour typ_corresp_opkind_binop 
             quand les deux types sont différents, pour éviter
             d'avoir à détruire k inutilement *)
          try discriminate; destruct op, k; try discriminate;
          revert TREXP; intros [= <-]).
    all: (apply Clight.eval_Ebinop with (v1 := transl_value trarr v1)
                                        (v2 := transl_value trarr v2)
                                        (1 := IHexp1 _ _ eq_refl H4)
                                        (2 := IHexp2 _ _ eq_refl H5);
          apply transl_expr_correct_type in Hexp1, Hexp2;
          rewrite Htexp1 in Hexp1; rewrite Htexp2 in Hexp2;
          revert Hexp1 Hexp2; intros [= <-] [= <-]).
    all: (destruct v1, v2; try discriminate; simpl in *).
    all: (try destruct (eq_signedness s s0); try destruct (eq_intsize i i1)).
    all: (revert H6; intros [= <-]; reflexivity).
  + inversion EVEXP. rewrite_equalities.
    destruct (type_expression (fn_tenv f) e1) eqn:Htexp1,
             (type_expression (fn_tenv f) e2) eqn:Htexp2; try discriminate.
    all: (destruct t; try destruct t0; try discriminate).
    all: (destruct (transl_expr (fn_tenv f) e1) eqn:Hexp1,
                   (transl_expr (fn_tenv f) e2) eqn:Hexp2; try discriminate).
    all: (try destruct i; try destruct i0; try destruct s; try destruct s0; 
          try discriminate; destruct op, k; try discriminate;
          revert TREXP; intros [= <-]).
    all: (apply Clight.eval_Ebinop with (v1 := transl_value trarr v1)
                                        (v2 := transl_value trarr v2)
                                        (1 := IHexp1 _ _ eq_refl H4)
                                        (2 := IHexp2 _ _ eq_refl H5);
          apply transl_expr_correct_type in Hexp1, Hexp2;
          rewrite Htexp1 in Hexp1; rewrite Htexp2 in Hexp2;
          revert Hexp1 Hexp2; intros [= <-] [= <-]).
    all: (destruct v1, v2; try discriminate; simpl in *).
    all: (try destruct (eq_signedness s s0); try destruct (eq_intsize i i1)).
    all: (revert H6; intros [= <-]; reflexivity).
  + inversion EVEXP; rewrite_equalities.
    destruct (type_expression (fn_tenv f) idx) eqn:Htidx; try discriminate.
    destruct t0; try discriminate; destruct s; try discriminate.
    unfold clight_array_idx_addr in TREXP. rewrite H2 in TREXP.
    destruct (transl_expr (fn_tenv f) idx) eqn:Hidx; try discriminate.
    revert TREXP; intros [= <-].
    assert (exists b ofs, trarr idarr = (b, ofs) /\
                          (transl_env trarr (fn_vars f ++ fn_params f) e) ! id = Some (Vptr b ofs))
      as [bl [ofs [TRarr TRenv]]].
    apply transl_env_correct with (trarr := trarr)
                                  (vars := fn_vars f ++ fn_params f) in H1.
    rewrite H1. simpl. destruct (trarr idarr). eauto.
    eapply Clight.eval_Elvalue.
    - eapply Clight.eval_Ederef, Clight.eval_Ebinop.
      eapply Clight.eval_Etempvar. eassumption. eauto.
      apply transl_expr_correct_type in Hidx. rewrite Htidx in Hidx.
      revert Hidx; intros [= <-]. reflexivity.
    - pose proof (blk_not_void blk) as Hnotvoid.
      revert H7 H8; intros [= <-] [= <-].
      assert ((Z.to_nat (Int64.unsigned i0) < length (blk_values blk))%nat);
       [ apply nth_error_Some; (rewrite H10 || rewrite H11); discriminate |].
      eapply PTree.elements_correct in H6.
      pose proof (proj1 (Forall_forall _ _) MMEM (idarr, blk) H6) as H'; simpl in H'.
      rewrite TRarr in H'. specialize (H' _ H). rewrite H11 in H'.
      rewrite Znat.Z2Nat.id in H' by apply Int64.unsigned_range.
      specialize (H' (proj2 (Int64.unsigned_range_2 i0))) as [_ [_ H']].
      eapply Clight.deref_loc_value; [| eassumption]. simpl.
      destruct (blk_type blk); try easy; try destruct i, s; try destruct f0; try easy.
Qed.

Lemma transl_fundefs_exists:
  forall ge fds tfds idf f,
    transl_fundefs ge fds = Some tfds ->
    In (idf, f) fds ->
    exists f', In (idf, Gfun f') tfds /\ transl_fundef ge f = Some f'.
Proof.
  induction fds; simpl; intros. contradiction. destruct a as [id fd].
  destruct transl_fundef eqn:Htfd, transl_fundefs eqn:Htfds; try discriminate.
  revert H; intros [= <-]. destruct H0.
  injection H; intros [= ->] [= ->]. simpl. eauto.
  specialize (IHfds _ _ _ eq_refl H) as [f' [H1 H2]]. simpl. eauto.
Qed.

Lemma transl_fundefs_eq_map_fst:
  forall ge fds tfds,
    transl_fundefs ge fds = Some tfds ->
    map fst fds = map fst tfds.
Proof.
  induction fds; simpl; intros. revert H; intros [= <-]. reflexivity.
  destruct a as [id fd]. destruct transl_fundef, transl_fundefs eqn:Htfds; try discriminate.
  revert H; intros [= <-]. simpl. erewrite IHfds; reflexivity.
Qed.

Lemma transl_fundefs_list_assoc_nodup:
  forall fds tfds ge,
    transl_fundefs ge fds = Some tfds ->
    list_assoc_nodup fds ->
    Coqlib.list_norepet (map fst tfds).
Proof.
  induction fds; simpl; intros.
  revert H; intros [= <-]. apply Coqlib.list_norepet_nil.
  destruct a as [id fd]. destruct transl_fundef, transl_fundefs eqn:Htfds; try discriminate.
  revert H; intros [= <-]. rewrite map_cons. eapply Coqlib.list_norepet_cons.
  inversion H0. erewrite <- transl_fundefs_eq_map_fst; eassumption.
  inversion H0. eauto.
Qed.

Lemma transl_program_genv_preservation:
  forall p tp idf f,
    transl_program p = Some tp ->
    (genv_of_program p) ! idf = Some f ->
    exists loc fd, Globalenvs.Genv.find_symbol (globalenv tp) idf = Some loc
                   /\ Globalenvs.Genv.find_funct_ptr (globalenv tp) loc = Some fd
                   /\ transl_fundef (genv_of_program p) f = Some fd.
Proof.
  intros. destruct p. unfold transl_program in H.
  destruct transl_fundefs eqn:Htfds; try discriminate. revert H; intros [= <-].
  unfold genv_of_program in H0. simpl in H0.
  apply PTree.elements_correct in H0.
  apply build_env_correct_empty in H0; try assumption.
  pose proof (transl_fundefs_list_assoc_nodup _ _ _ Htfds prog_nodup) as Hnodup.
  apply transl_fundefs_exists with (1 := Htfds) in H0. destruct H0 as [f' [H1 H2]].
  unfold Globalenvs.Genv.find_funct_ptr.
  eapply PTree_Properties.of_list_norepet with (1 := Hnodup) in H1.
  simpl in *. cbn in *.
  specialize (Globalenvs.Genv.find_def_symbol) with (p := {|
                Ctypes.prog_defs := l;
                prog_public := map fst prog_defs;
                Ctypes.prog_main := prog_main;
                prog_types := [];
                prog_comp_env := PTree.empty composite;
                prog_comp_env_eq := eq_refl
              |}) (id := idf) (g := Gfun f') as [H0 _]. specialize (H0 H1).
  destruct H0 as [b [H H0]]. repeat eexists. eassumption.
  destruct (Globalenvs.Genv.find_def _ _); try discriminate.
  injection H0; intros [= ->]. reflexivity. assumption.
Qed.

Lemma transl_function_params_sig:
  forall ge f tf,
    transl_function ge f = Some tf ->
    type_of_params (Clight.fn_params tf) = transl_typlist (sig_args (fn_sig f)).
Proof.
  destruct f; simpl. intros. unfold transl_function in H. simpl in H.
  destruct build_clight_list_ident_type eqn:Hparams; try discriminate.
  destruct build_clight_list_ident_type in H; try discriminate.
  destruct transl_stmt; try discriminate. revert H; intros [= <-]. simpl.
  clear fn_nodup fn_nodup_params fn_disjoint fn_tenv_arrszvar fn_sig_arrszvar l0 s.
  revert l fn_tenv_sig Hparams. generalize (sig_args fn_sig) as sig.
  induction fn_params; simpl in *; intros.
  + revert Hparams; intros [= <-]. destruct fn_tenv_sig.
    apply eq_sym, length_zero_iff_nil in H. rewrite H. reflexivity.
  + destruct (fn_tenv ! a) eqn:Ha; try discriminate.
    destruct build_clight_list_ident_type; try discriminate.
    revert Hparams; intros [= <-]. simpl.
    destruct fn_tenv_sig. destruct sig. discriminate. simpl in H. apply eq_add_S in H.
    pose proof (H0 0%nat a eq_refl). simpl in H1. rewrite <- H1 in Ha. revert Ha; intros [= ->].
    simpl. rewrite IHfn_params with (sig := sig) (2 := eq_refl). reflexivity.
    split. assumption. intros. apply (H0 (S i)). assumption.
Qed.

Lemma transl_identlist_sem_preservation:
  forall p tp m tm trarr e f tf (arrszvar: list (ident * ident)) args vargs vargs' targs sig
    (TRPROG:  transl_program p = Some tp)
    (MMEM:    match_mem tp trarr m tm)
    (TRFUNC:  transl_function (genv_of_program p) f = Some tf)
    (TRIDLST: transl_identlist (fn_tenv f) args = Some targs)
    (EVAL:    eval_identlist e f args vargs)
    (TYPE:    check_cast_args vargs sig = Some vargs'),
    exists lv,
      Clight.eval_exprlist (globalenv tp) PTree.Empty
        (transl_env trarr (fn_vars f ++ fn_params f) e) tm targs
        (transl_typlist sig) lv
      /\ transl_valuelist trarr vargs' = lv.
Proof.
  induction args; simpl; intros.
  + revert TRIDLST; intros [= <-]. inversion EVAL. revert H0; intros [= <-].
    destruct sig. exists []. split. apply Clight.eval_Enil.
    revert TYPE; intros [= <-]. reflexivity.
    simpl in TYPE. destruct t; try destruct i, s; discriminate.
  + inversion EVAL. rewrite_equalities. rewrite H2 in TRIDLST.
    destruct transl_identlist; revert TRIDLST; intros [= <-].
    destruct sig. destruct v; try destruct i, s; try discriminate.
    simpl in TYPE. destruct (check_cast_args lv sig) eqn:Hchk; try discriminate.
    2: { destruct t0; try destruct i, s; try destruct v; try destruct i, s; discriminate. }
    destruct t0; destruct v; try destruct (i: intsize); try destruct (s: signedness);
       try destruct i0; try destruct s0; try destruct f0; try discriminate.
    all: only 13: (destruct well_typed_value_bool; try discriminate).
    all: (revert TYPE; intros [= <-]).
    all: (specialize (IHargs _ _ _ _ TRPROG MMEM TRFUNC eq_refl H5 Hchk) as [v [Hv1 Hv2]]).
    all: (specialize eval_Var with (m := m) (1 := H1) (2 := H2) (3 := H3) as Heval; clear H1).
    all: (eexists; split;
          [eapply Clight.eval_Econs with (3 := Hv1);
           [eapply transl_expr_sem_preservation with (1 := TRPROG) (2 := MMEM)
                                                     (3 := TRFUNC) (5 := Heval);
            simpl; rewrite H2; reflexivity|]
          | rewrite <- Hv2; reflexivity]).
    all: (destruct t; try inversion H3).
    reflexivity. destruct b. all: try reflexivity.
    cbn. destruct (trarr p0). reflexivity.
Qed.

Lemma bind_parameter_temps_set:
  forall formals args le id v,
    (forall t, ~In (id, t) formals) ->
    bind_parameter_temps formals args (PTree.set id v le)
    = option_map (fun le => PTree.set id v le) (bind_parameter_temps formals args le).
Proof.
  induction formals; simpl; intros.
  + destruct args; reflexivity.
  + destruct a as [id0 t]. destruct args. reflexivity.
    rewrite <- IHformals.
    destruct (Pos.eq_dec id id0).
    rewrite e in H. specialize (H t). tauto.
    rewrite PTree_set_order_independent with (1 := n). reflexivity.
    intro. specialize (H t0). tauto.
Qed.

Lemma build_clight_list_ident_type_not_in:
  forall te id l l',
    ~In id l ->
    build_clight_list_ident_type te l = Some l' ->
    forall t, ~In (id, t) l'.
Proof.
  induction l; simpl; intros. injection H0. intros [= <-]. easy.
  destruct te ! a, build_clight_list_ident_type; try discriminate.
  revert H0; intros [= <-]. simpl. intro. apply H. clear H. destruct H0.
  + injection H. intros [= <-] [= <-]. tauto.
  + specialize (In_dec Pos.eq_dec id l) as [Hin | Hnotin]. eauto.
    specialize (IHl _ Hnotin eq_refl t). contradiction.
Qed.

Lemma complete_env_set_get_neq:
  forall l e i a,
    i <> a ->
    (complete_env l e) ! i = (complete_env l (PTree.set a Vunit e)) ! i.
Proof. intros. now rewrite complete_env_set, PTree.gsspec, Coqlib.peq_false with (1 := H). Qed.

Lemma transl_env_build_preservation:
  forall f e trarr vargs l l0,
    NoDup (fn_params f) ->
    build_func_env (PTree.empty value) (fn_params f) vargs = Some e ->
    build_clight_list_ident_type (fn_tenv f) (fn_params f) = Some l ->
    build_clight_list_ident_type (fn_tenv f) (fn_vars f) = Some l0 ->
    bind_parameter_temps l (transl_valuelist trarr vargs) (create_undef_temps l0) =
    Some (transl_env trarr (fn_vars f ++ fn_params f) e).
Proof.
  intros f. induction (fn_params f).
  + intros. destruct vargs; try discriminate.
    revert H0 H1; intros [= <-] [= <-]. apply f_equal.
    revert l0 H2. induction (fn_vars f); simpl; intros.
    - revert H2; intros [= <-]. reflexivity.
    - destruct (fn_tenv f) ! a eqn:Htenv; try discriminate.
      destruct build_clight_list_ident_type eqn:Htype_ident; try discriminate.
      revert H2; intros [= <-]. simpl. rewrite (IHl _ eq_refl).
      unfold transl_env. simpl. now rewrite complete_env_set, PTree_map_set.
  + simpl; intros. destruct vargs; try discriminate.
    destruct (fn_tenv f) ! a eqn:Htenv; try discriminate.
    destruct build_clight_list_ident_type eqn:Htype_ident; try discriminate.
    destruct build_func_env eqn:He0; try discriminate.
    revert H0 H1; intros [= <-] [= <-]. inversion_clear H.
    specialize IHl with (1 := H1) (2 := He0) (3 := eq_refl) (4 := H2).
    pose proof (build_clight_list_ident_type_not_in _ _ _ _ H0 Htype_ident).
    simpl. rewrite bind_parameter_temps_set with (1 := H). rewrite IHl. simpl.
    apply f_equal. rewrite transl_env_set.
    apply PTree.extensionality. intro. destruct (Pos.eq_dec i a) as [[= <-] | H'].
    - now do 2 rewrite PTree.gsspec, Coqlib.peq_true.
    - do 2 rewrite PTree.gsspec, Coqlib.peq_false with (1 := H').
      clear H2 IHl He0. revert e0. induction (fn_vars f); simpl; intros.
      * unfold transl_env. simpl. destruct e0!a. reflexivity.
        do 2 rewrite PTree.gmap. now rewrite complete_env_set_get_neq with (1 := H').
      * simpl. unfold transl_env. simpl. destruct e0!a0; eauto.
Qed.

Lemma build_clight_list_ident_type_var_names_ident:
  forall te l l',
    build_clight_list_ident_type te l = Some l' ->
    var_names l' = l.
Proof.
  induction l; simpl; intros.
  + now revert H; intros [= <-].
  + destruct te!a; try discriminate.
    destruct build_clight_list_ident_type; try discriminate.
    revert H; intros [= <-]. simpl. now rewrite IHl.
Qed.

Lemma transl_cont_destructCont:
  forall trarr p f k tk,
    transl_cont trarr (genv_of_program p) (Some f) k = Some tk ->
    transl_cont trarr (genv_of_program p) None (destructCont k) = Some (call_cont tk).
Proof.
  induction k; simpl; intros.
  + revert H; intros [= <-]; reflexivity.
  + destruct transl_stmt, transl_cont eqn:Hk; try discriminate.
    revert H; intros [= <-]. apply IHk with (1 := eq_refl).
  + destruct transl_function; try discriminate. simpl in *.
    destruct (transl_cont _ _ (Some f0) k); try discriminate.
    revert H; intros [= <-]. reflexivity.
  + destruct transl_stmt, transl_cont eqn:Hk; try discriminate.
    revert H; intros [= <-]. apply IHk with (1 := eq_refl).
Qed.

Axiom transl_external_functions_sem_preservation:
  forall trarr p tp name sig m tm args v m' trarr' tm',
    transl_program p = Some tp ->
    match_mem tp trarr m tm ->
    match_mem tp trarr' m' tm' ->
    External.external_call (EF_external name sig) m args v m' ->
    external_functions_sem name (transl_signature sig)
      (Globalenvs.Genv.to_senv (globalenv tp))
      (transl_valuelist trarr args) tm E0 (transl_value trarr v) tm'.

Theorem transl_stmt_sem_preservation:
  forall p tp s s' ts t,
    transl_program p = Some tp ->
    match_states p s ts ->
    step_events (genv_of_program p) s t s' ->
    exists ts', plus Clight.step2 (globalenv tp) ts t ts' /\ match_states p s' ts'.
Proof.
  intros p tp s s' ts t TPROG MSTATE HSTEP. destruct HSTEP as [Hevent HSTEP].
  inversion HSTEP; clear HSTEP; rewrite_equalities.
  + inversion_clear MSTATE. simpl in TK.
    destruct (transl_stmt (genv_of_program p) f s0) eqn:TS'; try discriminate.
    destruct (transl_cont trarr (genv_of_program p) (Some f) k) eqn:TK'; try discriminate.
    revert TS TK; intros [= <-] [= <-].
    eexists. split. eapply plus_one. apply Clight.step_skip_seq.
    eapply match_states_State; eassumption.
  + inversion_clear MSTATE. simpl in TK.
    destruct (transl_stmt (genv_of_program p) f s0) eqn:TS'; try discriminate.
    destruct (transl_cont trarr (genv_of_program p) (Some f) k) eqn:TK'; try discriminate.
    revert TS TK; intros [= <-] [= <-].
    eexists. split. eapply plus_left. apply Clight.step_skip_or_continue_loop1. eauto.
    eapply star_one. apply Clight.step_skip_loop2. reflexivity.
    eapply match_states_State; try eassumption. simpl. rewrite TS'. reflexivity.
  + inversion_clear MSTATE. destruct k; try contradiction. pose proof TK as TK1. simpl in TK.
    destruct (transl_function (genv_of_program p) f0) eqn:TF'; try discriminate.
    destruct (transl_cont trarr (genv_of_program p) (Some f0) k) eqn:TK'; try discriminate.
    revert TS TK; intros [= <-] [= <-].
    eexists. split. apply plus_one. apply Clight.step_skip_call; easy.
    eapply match_states_Returnstate with (r := Vunit); try eassumption.
  + inversion_clear MSTATE. simpl in TS.
    destruct (transl_expr (fn_tenv f) exp) eqn:Hexp; try discriminate.
    revert TS TE; intros [= <-] [= <-].
    eexists. split. apply plus_one. apply Clight.step_set.
    eapply transl_expr_sem_preservation; try eassumption. congruence.
    eapply match_states_State; try eauto. apply transl_env_set.
  + inversion_clear MSTATE. simpl in TS. unfold clight_array_idx_addr in TS.
    rewrite H5 in TS.
    destruct (transl_expr _ idx) eqn:Hidx; try discriminate.
    destruct (transl_expr _ exp) eqn:Hexp; try discriminate.
    destruct (type_expression _ idx) eqn:Htidx; try discriminate.
    destruct t1; try discriminate. destruct s; try discriminate.
    destruct (type_expression _ exp) eqn:Htexp; try discriminate. simpl in TS.
    destruct (typ_eq_dec t1 Tvoid) as [Hvoid | Hnotvoid]. rewrite_equalities. discriminate.
    assert (forall {A: Type} (e: option A) (e': A), match t1 with
                           Tvoid => None | _ => e end = Some e' -> e = Some e').
    intros; destruct t1; easy. apply H12 in TS. clear H12.
    destruct (eq_typ t1 t0) eqn:Heq; try discriminate.
    apply eq_typ_correct in Heq. revert Heq TS TE; intros [= ->] [= <-] [= <-].
    assert (exists b ofs, trarr idarr = (b, ofs) /\
                          (transl_env trarr (fn_vars f ++ fn_params f) e) ! id = Some (Vptr b ofs))
      as [bl [ofs [TRarr TRenv]]].
    apply transl_env_correct with (trarr := trarr)
                                  (vars := fn_vars f ++ fn_params f) in H.
    rewrite H. simpl. destruct (trarr idarr). eauto.
    destruct (write_array_modifs) with (1 := H11) (2 := H) (3 := H8).
    apply PTree.elements_correct in H8.
    destruct H12 as [blk' [Hrep [Htyp [He'_id Hm'_idarr]]]].
    destruct H13 as [He'_other Hm'_other].
    pose proof (proj1 (Forall_forall _ _) MMEM (idarr, blk) H8) as H'; simpl in H'.
    revert H10; intros [= <-].
    assert ((Z.to_nat (Int64.unsigned i) < length (blk_values blk))%nat);
      [ eapply replace_nth_Some; rewrite Hrep; discriminate |].
    rewrite TRarr in H'. specialize (H' _ H10).
    rewrite Znat.Z2Nat.id in H'; try apply Int64.unsigned_range.
    specialize (H' (proj2 (Int64.unsigned_range_2 i))) as [H' [Hvalid Hload]].
    apply Mem.valid_access_store with (v := transl_value trarr v') in Hvalid.
    destruct Hvalid as [tm' Hstore].
    rewrite TPROG in TPROG0.
    revert TPROG0; intros [= <-].
    eexists. split. apply plus_one. rewrite Hevent.
    eapply Clight.step_assign with (v := transl_value trarr v').
    apply eval_Ederef. eapply eval_Ebinop.
    eapply eval_Etempvar. apply transl_env_correct with (1 := H).
    eapply transl_expr_sem_preservation; try eassumption.
    apply transl_expr_correct_type in Hidx. rewrite Htidx in Hidx.
    revert Hidx; intros [= <-]. simpl. rewrite TRarr. reflexivity.
    eapply transl_expr_sem_preservation; try eassumption.
    apply transl_expr_correct_type in Hexp. rewrite Htexp in Hexp.
    revert Hexp; intros [= <-]. simpl.
    destruct t0; inversion H6; revert H12; intros [= <-].
    revert H7; intros [= <-]; reflexivity.
    revert H7; intros [= <-]. destruct b; reflexivity.
    destruct i0, s; revert H7; intros [= <-]; reflexivity.
    destruct s; revert H7; intros [= <-]; reflexivity.
    rewrite <- H14 in H7; revert H7; intros [= <-]; reflexivity.
    rewrite <- H14 in H7; revert H7; intros [= <-]; reflexivity.
    rewrite <- H13 in H7. simpl in H7.
    rewrite (eq_typ_complete _ _ eq_refl), eqb_reflx in H7. revert H7; intros [= <-].
    simpl. destruct (trarr id0). reflexivity.
    simpl. eapply assign_loc_value.
    assert (access_mode (transl_typ t0) = By_value (typ_to_memory_chunk t0)) as Ham;
      [ destruct t0; try easy;
        try destruct i0; try destruct s; try destruct f0; try reflexivity;
        try destruct v; discriminate |].
    rewrite Ham. reflexivity. rewrite <- H9. eassumption.
    eapply match_states_State; try eassumption; try easy.
    unfold match_mem, match_mem'. apply Forall_forall. intros. destruct x as [idarr0 blk0].
    destruct (trarr idarr0) as [b0 ofs0] eqn:TRarr0. intros.
    apply PTree.elements_complete in H12.
    destruct (Pos.eq_dec idarr0 idarr).
    - revert e2; intros [= ->]. rewrite Hm'_idarr in H12. revert H12; intros [= <-]. simpl.
      rewrite <- (replace_nth_length _ _ _ _ Hrep) in H13.
      rewrite TRarr in TRarr0. injection TRarr0; intros [= <-] [= <-]. clear TRarr0.
      pose proof (proj1 (Forall_forall _ _) MMEM (idarr, blk) H8). simpl in H12.
      rewrite TRarr in H12. specialize (H12 _ H13 H14) as [H'0 [Hv Hl]]. rewrite Htyp.
      split. assumption. split. apply (Mem.store_valid_access_1 _ _ _ _ _ _ Hstore _ _ _ _ Hv).
      destruct (Int64.eq_dec i (Int64.repr (Z.of_nat idx0))).
      * revert e2; intros [= ->].
        rewrite Int64.unsigned_repr in Hrep, Hstore by lia.
        rewrite (Mem.load_store_same _ _ _ _ _ _ Hstore).
        rewrite Znat.Nat2Z.id in Hrep.
        rewrite (replace_nth_nth_error_same _ _ _ _ Hrep). simpl.
        revert H9; intros [= <-]. revert H7.
        destruct (blk_type blk); (contradiction || inversion H6).
        destruct b; intros [= <-]; reflexivity.
        destruct s, i; intros [= <-]; simpl; try reflexivity;
          try rewrite Int.sign_ext_idem; try rewrite Int.zero_ext_idem; easy.
        destruct s; now intros [= <-]. now intros [= <-]. now intros [= <-].
        simpl; rewrite (eq_typ_complete _ _ eq_refl), eqb_reflx; intros [= <-]; simpl.
        destruct (trarr id0). unfold Val.load_result. unfold Mptr. now destruct Archi.ptr64.
      * rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore). rewrite Hl.
        rewrite (replace_nth_nth_error_other _ _ _ _ Hrep idx0). reflexivity.
        intros [= <-]. rewrite Znat.Z2Nat.id in n0; try apply Int64.unsigned_range.
        rewrite Int64.repr_unsigned in n0. contradiction.
        right. destruct (Int64_neq_lt_or_gt _ _ n0); apply Int64.ltu_inv in H12; [right | left].
        all: (unfold Ptrofs.mul; rewrite Ptrofs.unsigned_repr).
        all: only 2, 4:
            (unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize;
             destruct (blk_type blk); simpl;
               destruct Archi.ptr64; try destruct i0; try destruct f0; simpl; lia).
        all: (unfold Ptrofs.add; repeat rewrite Ptrofs.unsigned_repr_eq;
                 do 2 rewrite Zdiv.Zmult_mod_idemp_r;
                 rewrite <- (Z.mod_small (Ptrofs.unsigned ofs) Ptrofs.modulus)
                 by apply Ptrofs.unsigned_range;
                 do 2 rewrite <- Zdiv.Zplus_mod; unfold Ptrofs.max_unsigned in H', H'0).
        all: (pose proof (sizeof_pos (prog_comp_env tp) (transl_typ (blk_type blk)))).
        all: (repeat rewrite (Z.mod_small (_ + _) Ptrofs.modulus)
               by (split; lia || (apply Z.add_nonneg_nonneg;
                                  [ apply Ptrofs.unsigned_range | apply Z.mul_nonneg_nonneg ]; lia));
              rewrite Int64.unsigned_repr in H12 by lia).
        all: (assert (size_chunk (typ_to_memory_chunk (blk_type blk)) =
                      sizeof (prog_comp_env tp) (transl_typ (blk_type blk)));
              [ destruct (blk_type blk); simpl; try reflexivity;
                try destruct i0, s; try destruct f0; simpl; reflexivity |]).
        all: (rewrite H16, <- Z.add_assoc; rewrite <- (Z.mul_1_r (sizeof _ _)) at 2;
              rewrite <- Z.mul_add_distr_l;
              apply Zorder.Zplus_le_compat_l, Z.mul_le_mono_nonneg_l; lia).
    - rewrite (Hm'_other _ n0) in H12. apply PTree.elements_correct in H12.
      pose proof (proj1 (Forall_forall _ _) MMEM _ H12). simpl in H15. rewrite TRarr0 in H15.
      specialize (H15 idx0 H13 H14) as [H'0 [Hv Hl]].
      split. assumption. split. apply (Mem.store_valid_access_1 _ _ _ _ _ _ Hstore _ _ _ _ Hv).
      simpl. rewrite (Mem.load_store_other _ _ _ _ _ _ Hstore). assumption.
      specialize (VTRARR idarr0 idarr n0). rewrite TRarr, TRarr0 in VTRARR. simpl in VTRARR.
      left. assumption.
  + inversion_clear MSTATE. simpl in TS. rewrite Hevent.
    destruct (transl_identlist (fn_tenv f) args) eqn:Hargs; try discriminate.
    rewrite H in TS. apply transl_program_genv_preservation with (1 := TPROG) in H.
    destruct H as [loc [g [Hloc [Hfd Htfd]]]]. revert TS TE; intros [= <-] [= <-].
    pose proof (fn_tenv_sig f'). simpl in *.
    destruct transl_function eqn:Htf; try discriminate. revert Htfd; intros [= <-].
    pose proof (transl_function_params_sig _ _ _ Htf) as Hparams_sig.
    pose proof Htf as Htf'. unfold transl_function in Htf.
    destruct build_clight_list_ident_type eqn:Hparams; try discriminate.
    destruct build_clight_list_ident_type in Htf; try discriminate.
    destruct transl_stmt; try discriminate. revert Htf; intros [= <-]. simpl in Hparams_sig.
    rewrite TPROG in TPROG0. revert TPROG0; intros [= <-].
    destruct (transl_identlist_sem_preservation p tp m tm trarr e f tf
                (fn_arrszvar f) args vargs vargs' l (sig_args (fn_sig f')) TPROG MMEM TF Hargs H3 H4)
      as [lv [Hlv1 Hlv2]].
    eexists. split. apply plus_one. eapply Clight.step_call. reflexivity.
    eapply Clight.eval_Elvalue. eapply Clight.eval_Evar_global. reflexivity. eassumption.
    simpl. apply Clight.deref_loc_reference. reflexivity. eassumption.
    simpl. destruct Ptrofs.eq_dec; try contradiction. eassumption.
    destruct transl_function eqn:Htf; try discriminate.
    simpl. unfold type_of_function. simpl. rewrite Hparams_sig. reflexivity.
    eapply match_states_Callstate. eassumption. eassumption.
    simpl. rewrite Htf'. reflexivity. eassumption.
    simpl. rewrite TF, TK. reflexivity. eassumption.
  + inversion_clear MSTATE. simpl in TS. rewrite Hevent.
    destruct (transl_identlist (fn_tenv f) args) eqn:Hargs; try discriminate.
    rewrite H in TS. apply transl_program_genv_preservation with (1 := TPROG) in H.
    destruct H as [loc [g [Hloc [Hfd Htfd]]]]. revert TS TE; intros [= <-] [= <-].
    simpl in *. revert Htfd; intros [= <-].
    rewrite TPROG in TPROG0. revert TPROG0; intros [= <-].
    destruct (transl_identlist_sem_preservation p tp m tm trarr e f tf
                (fn_arrszvar f) args vargs vargs' l (sig_args (ef_sig ef))
                TPROG MMEM TF Hargs H2 H3)
      as [lv [Hlv1 Hlv2]].
    destruct (transl_mem tp m') as [trarr' tm'] eqn:Htm.
    eexists. split. apply plus_one. eapply Clight.step_builtin. eassumption.
    destruct ef. simpl. rewrite <- Hlv2.
    eapply transl_external_functions_sem_preservation
      with (m' := m') (tm' := tm'); try eassumption.
    apply transl_mem_match with (1 := Htm).
    apply (match_states_State p tp) with (trarr := trarr') (m := m') (tm := tm'); try eassumption.
    admit. reflexivity. admit. admit. apply transl_mem_match with (1 := Htm).
    (* eapply match_states_State; try eassumption. reflexivity.
       destruct idvar. simpl. rewrite transl_env_set. reflexivity. reflexivity. *)
  + inversion_clear MSTATE. rewrite Hevent. rewrite H in *.
    simpl in TFD. destruct transl_function eqn:Htf; try discriminate.
    revert TFD; intros [= <-].
    eexists. split. apply plus_one.
    eapply Clight.step_internal_function
      with (e := PTree.Empty)
           (le := transl_env trarr (fn_vars f ++ fn_params f) e) (m1 := tm).
    unfold transl_function in Htf.
    destruct build_clight_list_ident_type eqn:Htparams; try discriminate.
    destruct build_clight_list_ident_type eqn:Htvars in Htf; try discriminate.
    destruct transl_stmt eqn:Htbody; try discriminate. revert Htf; intros [= <-].
    eapply function_entry2_intro; simpl.
    apply Coqlib.list_norepet_nil.
    rewrite build_clight_list_ident_type_var_names_ident with (1 := Htparams).
    apply Coqlib_list_norepet_NoDup. apply fn_nodup_params.
    rewrite build_clight_list_ident_type_var_names_ident with (1 := Htparams).
    rewrite build_clight_list_ident_type_var_names_ident with (1 := Htvars).
    apply fn_disjoint. apply alloc_variables_nil. rewrite <- TVARGS.
    apply transl_env_build_preservation with (1 := fn_nodup_params f) (2 := H0)
                                             (3 := Htparams) (4 := Htvars).
    apply match_states_State with (2 := TPROG) (trarr := trarr); try easy.
    unfold transl_function in Htf.
    do 2 destruct build_clight_list_ident_type; destruct transl_stmt; try discriminate.
    now revert Htf; intros [= <-]. now destruct k.
    now revert TPROG TPROG0; intros [= ->] [= <-].
  + inversion_clear MSTATE. rewrite Hevent.
    simpl in TS. destruct (transl_expr (fn_tenv f) exp) eqn:Hexp; try discriminate.
    destruct (type_expression (fn_tenv f) exp) eqn:Htexp; try discriminate. simpl in TS.
    destruct (eq_typ t0 (sig_res (fn_sig f))) eqn:Heqt; try discriminate.
    apply eq_typ_correct in Heqt. revert Heqt TS; intros [= ->] [= <-].
    specialize transl_expr_correct_type with (1 := Hexp) as H'. rewrite Htexp in H'.
    pose proof (eq_refl (transl_value trarr v')).
    destruct v; destruct (sig_res (fn_sig f)) eqn:Ht;
      inversion H0; clear H0; rewrite_equalities; simpl.
    all: only 2: destruct b0; cbn.
    all: only 4: destruct sz, sig; cbn.
    all: only 13: destruct (trarr id) eqn:TRarr.
    all: (eexists; split; [ apply plus_one; eapply Clight.step_return_1;
                           [ rewrite <- TE; eapply transl_expr_sem_preservation;
                             try eassumption; now revert TPROG TPROG0; intros [= ->] [= <-]
                           | unfold transl_function in TF;
                             do 2 destruct build_clight_list_ident_type;
                             destruct transl_stmt; try discriminate;
                             revert H' TF Ht; intros [= <-] [= <-] [= ->]; simpl;
                             try rewrite TRarr; reflexivity
                           | easy ]
                          | simpl]).
    all: only 10: destruct sig.
    all: only 14: (simpl in H1; rewrite eqb_reflx, eq_typ_complete in H1 by easy).
    all: revert H1; intros [= <-].
    all: simpl (transl_value trarr _) in H2 at 2.
    all: only 14: rewrite TRarr in H2.
    all: only 2, 3: rewrite Int.eq_true || rewrite Int.eq_false by discriminate;
      fold Values.Vtrue; fold Values.Vfalse.
    all: rewrite <- H2.
    all: eapply match_states_Returnstate; try eassumption.
    all: eapply transl_cont_destructCont; eassumption.
  + inversion_clear MSTATE. simpl in TK.
    destruct transl_function eqn:Htf, transl_cont eqn:Htk; try discriminate.
    revert TK; intros [= <-].
    eexists. split. apply plus_one, Clight.step_returnstate.
    eapply match_states_State; try eassumption. reflexivity. reflexivity.
  + inversion_clear MSTATE. simpl in TK.
    destruct transl_function eqn:Htf, transl_cont eqn:Htk; try discriminate.
    revert TK; intros [= <-].
    eexists. split. apply plus_one, Clight.step_returnstate.
    eapply match_states_State; try eassumption. reflexivity.
    rewrite transl_env_set. reflexivity.
  + inversion_clear MSTATE. simpl in TS.
    destruct (transl_stmt _ _ s1) eqn:Hs1, (transl_stmt _ _ s2) eqn:Hs2; try discriminate.
    revert TS; intros [= <-].
    eexists. split. apply plus_one, Clight.step_seq.
    eapply match_states_State; try eassumption.
    simpl. rewrite Hs2, TK. reflexivity.
  + inversion_clear MSTATE. simpl in TS.
    destruct (transl_stmt _ _ s1) eqn:Hs1,
             (transl_stmt _ _ s2) eqn:Hs2,
             transl_expr eqn:Hcond,
             (type_expression _ cond) eqn:Htcond; try discriminate. simpl in TS.
    destruct (eq_typ t Tbool) eqn:Hteq; try discriminate.
    apply eq_typ_correct in Hteq. revert Hteq; intros [= ->].
    revert TS; intros [= <-].
    eexists. split. eapply plus_one, Clight.step_ifthenelse with (b := b).
    rewrite <- TE. eapply transl_expr_sem_preservation; try eassumption.
    revert TPROG TPROG0; intros [= ->] [= <-]. assumption.
    apply transl_expr_correct_type in Hcond. rewrite Htcond in Hcond.
    revert Hcond; intros [= <-]. destruct b; reflexivity.
    eapply match_states_State; try eassumption.
    destruct b; simpl; [rewrite Hs1|rewrite Hs2]; reflexivity.
  + inversion_clear MSTATE. simpl in TS.
    destruct (transl_stmt _ _ s0) eqn:Hs0; try discriminate.
    revert TS; intros [= <-].
    eexists. split. apply plus_one, Clight.step_loop.
    eapply match_states_State; try eassumption.
    simpl. rewrite Hs0, TK. reflexivity.
  + inversion_clear MSTATE. revert TS; intros [= <-].
    simpl in TK. destruct transl_stmt, transl_cont eqn:Hk; try discriminate.
    revert TK; intros [= <-].
    eexists. split. apply plus_one, Clight.step_break_seq.
    eapply match_states_State; try eassumption. reflexivity.
  + inversion_clear MSTATE. revert TS; intros [= <-].
    simpl in TK. destruct transl_stmt, transl_cont eqn:Htk; try discriminate.
    revert TK; intros [= <-].
    eexists. split. apply plus_one, Clight.step_break_loop1.
    eapply match_states_State; try eassumption. reflexivity.
  + inversion_clear MSTATE. revert TS; intros [= <-].
    simpl in TK. destruct transl_stmt, transl_cont eqn:Hk; try discriminate.
    revert TK; intros [= <-].
    eexists. split. apply plus_one, Clight.step_continue_seq.
    eapply match_states_State; try eassumption. reflexivity.
  + inversion_clear MSTATE. revert TS; intros [= <-].
    simpl in TK. destruct transl_stmt eqn:Hs0, transl_cont eqn:Hk; try discriminate.
    revert TK; intros [= <-].
    eexists. split. eapply plus_two.
    apply Clight.step_skip_or_continue_loop1. tauto.
    apply Clight.step_skip_loop2. reflexivity.
    eapply match_states_State; try eassumption.
    simpl. rewrite Hs0. reflexivity.
  + inversion_clear MSTATE. revert TS; intros [= <-].
    eexists. split. eapply plus_three.
    apply Clight.step_loop. apply Clight.step_skip_or_continue_loop1. tauto.
    apply Clight.step_skip_loop2. reflexivity.
    eapply match_states_State; try eassumption. reflexivity.
Admitted.

Lemma transl_fundefs_genv_public_symbol_add_globals:
  forall p ge ge1 ge2 l id,
    transl_fundefs ge (prog_defs p) = Some l ->
    Genv.public_symbol ge1 id = Genv.public_symbol ge2 id  ->
    Genv.genv_public ge1 = Genv.genv_public ge2 ->
    Genv.public_symbol
      (Genv.add_globals ge1 l) id =
    Genv.public_symbol
      (Genv.add_globals ge2 (to_AST_globdef (prog_defs p))) id.
Proof.
  intro p. induction (prog_defs p); intros.
  + revert H; intros [= <-]. assumption.
  + destruct a as [idf fd]. simpl in H.
    destruct transl_fundef, transl_fundefs eqn:Htfds; try discriminate.
    revert H; intros [= <-]. simpl. apply IHl with (1 := Htfds).
    - unfold Genv.public_symbol, Genv.find_symbol. simpl.
      do 2 rewrite PTree.gsspec. destruct (Coqlib.peq id idf).
      * rewrite H1. reflexivity.
      * assumption.
    - assumption.
Qed.

Lemma transl_fundefs_alloc_globals:
  forall p ge ge' l m,
    transl_fundefs ge (prog_defs p) = Some l ->
    exists m',
      Genv.alloc_globals (Genv.add_globals ge' l) m l = Some m'.
Proof.
  intros p ge. induction (prog_defs p); intros; simpl.
  + revert H; intros [= <-]. exists m. reflexivity.
  + destruct a as [id fd]. simpl in H.
    destruct transl_fundef, transl_fundefs eqn:Htfds; try discriminate.
    revert H; intros [= <-]. simpl. destruct Mem.alloc eqn:Halloc.
    pose proof (Mem.perm_alloc_2 _ _ _ _ _ Halloc).
    specialize H with (k := Cur). unfold Mem.drop_perm.
    apply decide_left with (decide := Mem.range_perm_dec m0 b 0 1 Cur Freeable). eauto.
    intro. apply IHl. reflexivity.
Qed.

Theorem transl_program_correct (p: program):
  forall tp,
    transl_program p = Some tp ->
    forward_simulation (SemanticsBlocking.semantics p) (Clight.semantics2 tp).
Proof.
  intros.
  apply forward_simulation_plus with (match_states := match_states p); intros; simpl.
  + unfold transl_program in H.
    destruct transl_fundefs eqn:Htfds; try discriminate. revert H; intros [= <-]. cbn.
    apply transl_fundefs_genv_public_symbol_add_globals with (1 := Htfds); reflexivity.
  + pose proof H as TPROG. unfold transl_program in H.
    destruct transl_fundefs eqn:Htfds; try discriminate. revert H; intros [= <-].
    simpl in H0. inversion H0.
    destruct (transl_fundefs_alloc_globals _ _
                (Genv.empty_genv (Ctypes.fundef Clight.function) type (map fst (prog_defs p)))
                _ Mem.empty Htfds) as [tm Htm].
    destruct (transl_program_genv_preservation _ _ _ _ TPROG H) as [b [tf [Htf1 [Htf2 Htf3]]]].
    eexists. split. eapply Clight.initial_state_intro; simpl.
    eassumption. eassumption. eassumption.
    simpl in Htf3. destruct transl_function eqn:Htf; try discriminate.
    revert Htf3; intros [= <-]. unfold transl_function in Htf.
    simpl. unfold type_of_function. rewrite transl_function_params_sig with (1 := Htf).
    do 2 destruct build_clight_list_ident_type; destruct transl_stmt; try discriminate.
    revert Htf; intros [= <-]. simpl. rewrite H1. reflexivity.
    eapply match_states_Callstate with (trarr := fun x => (x, Ptrofs.zero)).
    unfold valid_trarr. eauto. eassumption. eassumption. reflexivity. reflexivity.
    unfold match_mem. simpl. apply Forall_nil.
  + simpl in H1. inversion H1. rewrite_equalities.
    inversion H0. clear m0 r H3 H4. revert H5 TK; intros [= ->] [= <-]. simpl.
    apply Clight.final_state_intro.
  + eapply transl_stmt_sem_preservation; eassumption.
Qed.
