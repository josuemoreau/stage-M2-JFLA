Require Import BinNums BinInt.
Require Import Coq.Bool.Bool.

From compcert Require Import Integers Floats.

Require Import Types BValues.

Inductive unary_operation : Type :=
  | Onotbool : unary_operation
  | Onotint : unary_operation
  | Oneg : unary_operation
  | Oabsfloat : unary_operation.

Inductive operation_kind : Type :=
  | OInt
  | OInt64
  | OFloat32
  | OFloat64.

Inductive binarith_operation : Type :=
  | Oadd
  | Osub
  | Omul
  | Odivs
  | Odivu
  | Omods
  | Omodu.
  (* | Oshr
     | Oshl. *)

Inductive logical_operation : Type :=
  | Oand
  | Oor
  | Oxor.

Inductive cmp_operation : Type :=
  | Oeq
  | One
  | Olt
  | Ogt
  | Ole
  | Oge.

Inductive cmpu_operation : Type :=
  | Oltu
  | Ogtu
  | Oleu
  | Ogeu.

(* Sémantique des opérateurs unaires *)

Definition sem_notbool (v: value) : option value :=
  match v with
  | Vbool b => Some (Vbool (negb b))
  | _ => None
  end.


Definition sem_notint (k: operation_kind) (v: value) : option value :=
  match k, v with
  | OInt, Vint sz sig n => Some (Vint sz sig (Int.not n))
  | OInt64, Vint64 sig n => Some (Vint64 sig (Int64.not n))
  | _, _ => None
  end.

Definition sem_neg (k: operation_kind) (v: value) : option value :=
  match k, v with
  | OInt, Vint sz sig n => Some (Vint sz sig (Int.neg n))
  | OInt64, Vint64 sig n => Some (Vint64 sig (Int64.neg n))
  | OFloat32, Vfloat32 f => Some (Vfloat32 (Float32.neg f))
  | OFloat64, Vfloat64 f => Some (Vfloat64 (Float.neg f))
  | _, _ => None
  end.

Definition sem_absfloat (k: operation_kind) (v: value) : option value :=
  match k, v with
  | OFloat32, Vfloat32 f => Some (Vfloat64 (Float.abs (Float.of_single f)))
  | OFloat64, Vfloat64 f => Some (Vfloat64 (Float.abs f))
  | _, _ => None
  end.

Definition sem_unop (op: unary_operation) (k: operation_kind) (v: value) :=
  match op with
  | Onotbool => sem_notbool v
  | Onotint => sem_notint k v
  | Oneg => sem_neg k v
  | Oabsfloat => sem_absfloat k v
  end.

Definition sem_binarith
           (sem_int32: intsize -> signedness -> int -> int -> option value)
           (sem_int64: signedness -> int64 -> int64 -> option value)
           (sem_float32: Floats.float32 -> Floats.float32 -> option value)
           (sem_float64: Floats.float -> Floats.float -> option value)
           (k: operation_kind)
           (v1: value) (v2: value) : option value :=
  match k, v1, v2 with
  | OInt, Vint sz1 sig1 n1, Vint sz2 sig2 n2 =>
    if eq_intsize sz1 sz2 && eq_signedness sig1 sig2 then sem_int32 sz1 sig1 n1 n2 else None
  | OInt64, Vint64 sig1 n1, Vint64 sig2 n2 => if eq_signedness sig1 sig2 then sem_int64 sig1 n1 n2 else None
  | OFloat32, Vfloat32 f1, Vfloat32 f2 => sem_float32 f1 f2
  | OFloat64, Vfloat64 f1, Vfloat64 f2 => sem_float64 f1 f2
  | _, _, _ => None
  end.

Definition opf {A B C: Type} (f: A -> B -> C) : A -> B -> option C :=
  fun x y => Some (f x y).

Definition sem_logical (sem_bool: bool -> bool -> option value)
           (v1 v2: value) : option value :=
  match v1, v2 with
  | Vbool b1, Vbool b2 => sem_bool b1 b2
  | _, _ => None
  end.

Definition sem_cmp (c: Integers.comparison) (k: operation_kind)
           (v1: value) (v2: value) : option value :=
  match k, v1, v2 with
  | OInt, Vint sz1 sig1 n1, Vint sz2 sig2 n2 =>
    if eq_intsize sz1 sz2 && eq_signedness sig1 sig2 then Some (Vbool (Int.cmp c n1 n2)) else None
  | OInt64, Vint64 sig1 n1, Vint64 sig2 n2 => if eq_signedness sig1 sig2 then Some (Vbool (Int64.cmp c n1 n2)) else None
  | OFloat32, Vfloat32 f1, Vfloat32 f2 => Some (Vbool (Float32.cmp c f1 f2))
  | OFloat64, Vfloat64 f1, Vfloat64 f2 => Some (Vbool (Float.cmp c f1 f2))
  | _, _, _ => None
  end.

Definition sem_cmpu (c: Integers.comparison) (k: operation_kind)
           (v1: value) (v2: value) : option value :=
  match k, v1, v2 with
  | OInt, Vint sz1 sig1 n1, Vint sz2 sig2 n2 =>
    if eq_intsize sz1 sz2 && eq_signedness sig1 sig2 then Some (Vbool (Int.cmpu c n1 n2)) else None
  | OInt64, Vint64 sig1 n1, Vint64 sig2 n2 => if eq_signedness sig1 sig2 then Some (Vbool (Int64.cmpu c n1 n2)) else None
  | _, _, _ => None
  end.


Definition opb (f: bool -> bool -> bool) : bool -> bool -> option value :=
  fun x y => Some (Vbool (f x y)).

Definition opi (f: int -> int -> int) : intsize -> signedness -> int -> int -> option value :=
  fun sz sig x y => Some (Vint sz sig (f x y)).

Definition opi64 (f: int64 -> int64 -> int64) : signedness -> int64 -> int64 -> option value :=
  fun sig x y => Some (Vint64 sig (f x y)).

Definition opf32 (f: float32 -> float32 -> float32) : float32 -> float32 -> option value :=
  fun x y => Some (Vfloat32 (f x y)).

Definition opf64 (f: float -> float -> float) : float -> float -> option value :=
  fun x y => Some (Vfloat64 (f x y)).

Definition divu (sz: intsize) (sig: signedness) (n1 n2: int) : option value :=
  if Int.eq n2 Int.zero then None
  else Some (Vint sz sig (Int.divu n1 n2)).

Definition divs (sz: intsize) (sig: signedness) (n1 n2: int) : option value :=
  if Int.eq n2 Int.zero
     || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone then None
  else Some (Vint sz sig (Int.divs n1 n2)).

Definition divu64 (sig: signedness) (n1 n2: int64) : option value :=
  if Int64.eq n2 Int64.zero then None
  else Some (Vint64 sig (Int64.divu n1 n2)).

Definition divs64 (sig: signedness) (n1 n2: int64) : option value :=
  if Int64.eq n2 Int64.zero
     || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone then None
  else Some (Vint64 sig (Int64.divs n1 n2)).

Definition modu (sz: intsize) (sig: signedness) (n1 n2: int) : option value :=
  if Int.eq n2 Int.zero then None
  else Some (Vint sz sig (Int.modu n1 n2)).

Definition mods (sz: intsize) (sig: signedness) (n1 n2: int) : option value :=
  if Int.eq n2 Int.zero
     || Int.eq n1 (Int.repr Int.min_signed) && Int.eq n2 Int.mone then None
  else Some (Vint sz sig (Int.mods n1 n2)).

Definition modu64 (sig: signedness) (n1 n2: int64) : option value :=
  if Int64.eq n2 Int64.zero then None
  else Some (Vint64 sig (Int64.modu n1 n2)).

Definition mods64 (sig: signedness) (n1 n2: int64) : option value :=
  if Int64.eq n2 Int64.zero
     || Int64.eq n1 (Int64.repr Int64.min_signed) && Int64.eq n2 Int64.mone then None
  else Some (Vint64 sig (Int64.mods n1 n2)).


Definition sem_binarith_operation (op: binarith_operation)
           (k: operation_kind) (v1 v2: value) : option value :=
  match op with
  | Oadd =>
    sem_binarith
      (opi Int.add) (opi64 Int64.add) (opf32 Float32.add) (opf64 Float.add) k v1 v2
  | Osub =>
    sem_binarith
      (opi Int.sub) (opi64 Int64.sub) (opf32 Float32.sub) (opf64 Float.sub) k v1 v2
  | Omul =>
    sem_binarith
      (opi Int.mul) (opi64 Int64.mul) (opf32 Float32.mul) (opf64 Float.mul) k v1 v2
  | Odivu =>
    sem_binarith
      divu divu64 (opf32 Float32.div) (opf64 Float.div) k v1 v2
  | Odivs =>
    sem_binarith
      divs divs64 (opf32 Float32.div) (opf64 Float.div) k v1 v2
  | Omodu =>
    sem_binarith
      modu modu64 (fun _ _ => None) (fun _ _ => None) k v1 v2
  | Omods =>
    sem_binarith
      mods mods64 (fun _ _ => None) (fun _ _ => None) k v1 v2
  end.

Definition sem_logical_operation (op: logical_operation)
           (v1 v2: value) : option value :=
  match op with
  | Oand =>
    sem_logical (opb andb) v1 v2
  | Oor =>
    sem_logical (opb orb) v1 v2
  | Oxor =>
    sem_logical (opb xorb) v1 v2
  end.

Definition sem_cmp_operation (op: cmp_operation) (k: operation_kind)
           (v1 v2: value) : option value :=
  match op with
  | Oeq => sem_cmp Integers.Ceq k v1 v2
  | One => sem_cmp Integers.Cne k v1 v2
  | Olt => sem_cmp Integers.Clt k v1 v2
  | Ogt => sem_cmp Integers.Cgt k v1 v2
  | Ole => sem_cmp Integers.Cle k v1 v2
  | Oge => sem_cmp Integers.Cge k v1 v2
  end.

Definition sem_cmpu_operation (op: cmpu_operation) (k: operation_kind)
           (v1 v2: value) : option value :=
  match op with
  | Oltu => sem_cmpu Integers.Clt k v1 v2
  | Ogtu => sem_cmpu Integers.Cgt k v1 v2
  | Oleu => sem_cmpu Integers.Cle k v1 v2
  | Ogeu => sem_cmpu Integers.Cge k v1 v2
  end.

Definition cast_int_int (sz: intsize) (sig: signedness) (i: int) : int :=
  match sz, sig with
  | I8,  Signed   => Int.sign_ext 8 i
  | I8,  Unsigned => Int.zero_ext 8 i
  | I16, Signed   => Int.sign_ext 16 i
  | I16, Unsigned => Int.zero_ext 16 i
  | I32, _        => i
  end.

Definition sem_cast (v: value) (tv: typ) (t: typ) : option value :=
  match v, tv, t with
  | Vint _ _ n, Tint _ _, Tint sz sig => Some (Vint sz sig (cast_int_int sz sig n))
  | Vint _ _ n, Tint _ Signed, Tint64 sig  => Some (Vint64 sig (Int64.repr (Int.signed n)))
  | Vint _ _ n, Tint _ Unsigned, Tint64 sig => Some (Vint64 sig (Int64.repr (Int.unsigned n)))
  | Vint _ _ n, Tint _ Signed, Tfloat F32 => Some (Vfloat32 (Float32.of_int n))
  | Vint _ _ n, Tint _ Unsigned, Tfloat F32 => Some (Vfloat32 (Float32.of_intu n))
  | Vint _ _ n, Tint _ Signed, Tfloat F64 => Some (Vfloat64 (Float.of_int n))
  | Vint _ _ n, Tint _ Unsigned, Tfloat F64 => Some (Vfloat64 (Float.of_intu n))
  | Vint64 _ n, Tint64 _, Tint64 sig => Some (Vint64 sig n)
  | Vint64 _ n, Tint64 _, Tint sz sig =>
    Some (Vint sz sig (cast_int_int sz sig (Int.repr (Int64.unsigned n))))
  | Vint64 _ n, Tint64 Signed, Tfloat F32 => Some (Vfloat32 (Float32.of_long n))
  | Vint64 _ n, Tint64 Unsigned, Tfloat F32 => Some (Vfloat32 (Float32.of_longu n))
  | Vint64 _ n, Tint64 Signed, Tfloat F64 => Some (Vfloat64 (Float.of_long n))
  | Vint64 _ n, Tint64 Unsigned, Tfloat F64 => Some (Vfloat64 (Float.of_longu n))
  | Vfloat32 f, Tfloat F32, Tint sz Signed =>
    match Float32.to_int f with
    | Some i => Some (Vint sz Signed (cast_int_int sz Signed i))
    | None => None
    end
  | Vfloat32 f, Tfloat F32, Tint sz Unsigned =>
    match Float32.to_intu f with
    | Some i => Some (Vint sz Unsigned (cast_int_int sz Unsigned i))
    | None => None
    end
  | Vfloat32 f, Tfloat F32, Tint64 Signed =>
    match Float32.to_long f with
    | Some i => Some (Vint64 Signed i)
    | None => None
    end
  | Vfloat32 f, Tfloat F32, Tint64 Unsigned =>
    match Float32.to_longu f with
    | Some i => Some (Vint64 Unsigned i)
    | None => None
    end
  | Vfloat32 f, Tfloat F32, Tfloat F32 => Some v
  | Vfloat32 f, Tfloat F32, Tfloat F64 => Some (Vfloat64 (Float.of_single f))
  | Vfloat64 f, Tfloat F64, Tint sz Signed =>
    match Float.to_int f with
    | Some i => Some (Vint sz Signed (cast_int_int sz Signed i))
    | None => None
    end
  | Vfloat64 f, Tfloat F64, Tint sz Unigned =>
    match Float.to_intu f with
    | Some i => Some (Vint sz Unsigned (cast_int_int sz Unsigned i))
    | None => None
    end
  | Vfloat64 f, Tfloat F64, Tint64 Signed =>
    match Float.to_long f with
    | Some i => Some (Vint64 Signed i)
    | None => None
    end
  | Vfloat64 f, Tfloat F64, Tint64 Unsigned =>
    match Float.to_longu f with
    | Some i => Some (Vint64 Unsigned i)
    | None => None
    end
  | Vfloat64 f, Tfloat F64, Tfloat F32 => Some (Vfloat32 (Float.to_single f))
  | Vfloat64 f, Tfloat F64, Tfloat F64 => Some v
  | Vunit, Tvoid, Tvoid => Some Vunit
  | Vbool b, Tbool, Tbool => Some (Vbool b)
  | Varr idarr lv, Tarr b0 t0, Tarr b1 t1 =>
    if eqb b0 b1 && eq_typ t0 t1 then Some (Varr idarr lv) else None
  (* | Vmutarr idarr, Tarr b0 t0, Tarr b1 t1 =>
       if eqb b0 b1 && eq_typ t0 t1 then Some (Vmutarr idarr) else None *)
  | _, _, _ => None
  end.
