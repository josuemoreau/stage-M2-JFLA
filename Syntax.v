Require Import BinNums BinInt String List.

From compcert Require Import Integers Floats Maps Coqlib.

Require Import Types Ops BValues BUtils.

Definition ident := positive.

Inductive constant : Type :=
| Cint: intsize -> signedness -> int -> constant
| Cint64: signedness -> int64 -> constant
| Cfloat32: float32 -> constant
| Cfloat64: float -> constant.

Definition int_beq := Int.eq.
Definition int_eq_dec := Int.eq_dec.
Definition int64_beq := Int64.eq.
Definition int64_eq_dec := Int64.eq_dec.
Definition float32_beq x y :=
  match Float32.eq_dec x y with
  | left _ => true
  | right _ => false
  end.
Definition float32_eq_dec := Float32.eq_dec.
Definition float_beq x y :=
  match Float.eq_dec x y with
  | left _ => true
  | right _ => false
  end.
Definition float_eq_dec := Float.eq_dec.

Definition constant_eq_dec (x y: constant) : {x = y} + {x <> y}.
  decide equality.
  apply int_eq_dec.
  apply signedness_eq_dec.
  apply intsize_eq_dec.
  apply int64_eq_dec.
  apply signedness_eq_dec.
  apply float32_eq_dec.
  apply float_eq_dec.
Defined.

Inductive expr : Type :=
(* | Eunit: expr *)
| Evar: ident -> expr
| Econst: constant -> expr
| Ecast: expr -> typ -> typ -> expr
| Eunop: unary_operation -> operation_kind -> expr -> expr
| Ebinop_arith: binarith_operation -> operation_kind -> expr -> expr -> expr
| Ebinop_logical: logical_operation -> expr -> expr -> expr
| Ebinop_cmp: cmp_operation -> operation_kind -> expr -> expr -> expr
| Ebinop_cmpu: cmpu_operation -> operation_kind -> expr -> expr -> expr
(* ajouter plus tard un opérateur binaire pour échanger deux tableaux *)
| Earr_access: ident -> expr -> expr.
(* | Etensor_access: expr -> list index -> expr *)
(* | Etensor_extract_dim: expr -> list index -> expr *)
(* | Earr_sub: ident -> index -> index -> expr. *)
(* | Esub_tensor: expr -> list index -> expr. *)

Scheme Equality for unary_operation.
Scheme Equality for binarith_operation.
Scheme Equality for logical_operation.
Scheme Equality for cmp_operation.
Scheme Equality for cmpu_operation.
Scheme Equality for operation_kind.


Definition expr_eq_dec (x y: expr) : {x = y} + {x <> y}.
  decide equality.
  apply Pos.eq_dec.
  apply constant_eq_dec.
  apply typ_eq_dec.
  apply typ_eq_dec.
  apply operation_kind_eq_dec.
  apply unary_operation_eq_dec.
  apply operation_kind_eq_dec.
  apply binarith_operation_eq_dec.
  apply logical_operation_eq_dec.
  apply operation_kind_eq_dec.
  apply cmp_operation_eq_dec.
  apply operation_kind_eq_dec.
  apply cmpu_operation_eq_dec.
  apply Pos.eq_dec.
Defined.

Record signature : Type := mk_signature {
  sig_args: list typ;
  sig_res: typ
  (* sig_cc: calling_convention *)
}.

Inductive external_function : Type :=
| EF_external (name: string) (sig: signature).

Inductive stmt : Type :=
| Sskip: stmt
| Sassign: ident -> expr -> stmt
| Sarr_assign: ident -> expr -> expr -> stmt
(* | Sarr_sub: ident -> ident -> expr -> expr -> stmt *)
(* | Stensor_assign: ident -> list index -> expr -> stmt *)
| Scall: option ident -> ident -> list ident -> stmt
(* | Stailcall: signature -> expr -> list expr -> stmt *)
| Sreturn: expr -> stmt
(* | Sbuiltin: option ident -> external_function -> list expr -> stmt *)
| Sseq: stmt -> stmt -> stmt
| Sifthenelse: expr -> stmt -> stmt -> stmt
(* | Sfor: ident -> expr -> expr -> expr -> stmt -> stmt *)
(* | Swhile: expr -> stmt -> stmt *)
| Sloop: stmt -> stmt
(* | Sswap: ... *)
| Sbreak
| Scontinue
| Serror.

Definition Swhile (cond: expr) (s: stmt) :=
  Sloop (Sifthenelse cond s Sbreak).

(* Definition Sfor (i ihigh istep: ident) (low high step: expr) (s: stmt) :=
     Sseq (Sassign i low)
       (Sseq (Sassign ihigh high)
             (Sseq (Sassign istep step)
                (Swhile
                   (Ebinop_cmp Olt OInt64 (Evar i) (Evar ihigh))
                   (Sseq s (Sassign i (Ebinop_arith Oadd OInt64 (Evar i) (Evar istep))))))). *)

Definition valid_sig_arrszvar (arrszvar: list (ident * ident))
                              (sig_args: list typ) (params: list ident) :=
  forall id szvar i j,
    In (id, szvar) arrszvar ->
    nth_error params i = Some id ->
    nth_error params j = Some szvar ->
    exists b t, nth_error sig_args i = Some (Tarr b t)
                /\ nth_error sig_args j = Some Tuint64.

Definition valid_tenv_arrszvar (te: tenv) (arrszvar: list (ident * ident)) :=
  forall id sz,
    In (id, sz) arrszvar ->
    exists b t, te!id = Some (Tarr b t) /\ te!sz = Some Tuint64.

Definition valid_tenv_sig (te: tenv) (params: list ident) (sig_args: list typ) :=
  length params = length sig_args /\
  forall i var,
    nth_error params i = Some var ->
    nth_error sig_args i = te!var.

Record function : Type :=
  mk_function {
      fn_sig: signature;
      fn_params: list ident;
      fn_arrszvar: list (ident * ident);
      fn_vars: list ident;
      fn_body: stmt;
      fn_tenv: tenv;
      fn_nodup: list_assoc_nodup fn_arrszvar;
      fn_nodup_params: NoDup fn_params;
      fn_disjoint: Coqlib.list_disjoint fn_params fn_vars;
      fn_tenv_arrszvar: valid_tenv_arrszvar fn_tenv fn_arrszvar;
      fn_tenv_sig: valid_tenv_sig fn_tenv fn_params fn_sig.(sig_args);
      fn_sig_arrszvar: valid_sig_arrszvar fn_arrszvar fn_sig.(sig_args) fn_params
    }.

Inductive fundef : Type :=
| Internal: function -> fundef
| External: external_function -> fundef.

Record program : Type :=
  mk_program {
      prog_defs: list (ident * fundef);
      prog_main: ident;
      prog_nodup: list_assoc_nodup prog_defs;
      prog_main_exists: In prog_main (map fst prog_defs)
    }.

Definition fundef_nb_params (fd: fundef): nat :=
  match fd with
  | Internal f => length f.(fn_params)
  | External ef =>
      match ef with
      | EF_external _ sig => length sig.(sig_args)
      end
  end.

Definition ef_sig (ef: external_function) : signature :=
  match ef with
  | EF_external _ sig => sig
  end.

Definition fd_sig (fd: fundef) : signature :=
  match fd with
  | Internal f  => f.(fn_sig)
  | External ef => ef_sig ef
  end.
