Require Import Coq.Lists.List.
Require Import BinNums ZArith Lia.

Import ListNotations.

From compcert Require Import Integers Floats.

Require Import Types.

Inductive value : Type :=
| Vunit
| Vbool: bool -> value
| Vint: intsize -> signedness -> int -> value
| Vint64: signedness -> int64 -> value
| Vfloat32: float32 -> value
| Vfloat64: float -> value
(* | Vmutarr: positive -> value *)
| Varr: positive -> list value -> value.

(* Definition Vzero64 := Vint64 Unsigned Int64.zero.
   Definition Vone64 := Vint64 Unsigned Int64.one.

   Definition Vzero32 := Vint I32 Unsigned Int.zero.
   Definition Vone32 := Vint I32 Unsigned Int.one.

   Definition Vzero16 := Vint I16 Unsigned Int.zero.
   Definition Vone16 := Vint I16 Unsigned Int.one.

   Definition Vzero8 := Vint I8 Unsigned Int.zero.
   Definition Vone8 := Vint I8 Unsigned Int.one. *)

Definition Vtrue := Vbool true.
Definition Vfalse := Vbool false.

Definition shrink (v: value) :=
  match v with
  | Vint I8 Unsigned n => Vint I8 Unsigned (Int.zero_ext 8 n)
  | Vint I8 Signed n => Vint I8 Signed (Int.sign_ext 8 n)
  | Vint I16 Unsigned n => Vint I16 Unsigned (Int.zero_ext 16 n)
  | Vint I16 Signed n => Vint I16 Signed (Int.sign_ext 16 n)
  | _ => v
  end.

Theorem shrink_shrink:
  forall v, shrink v = shrink (shrink v).
Proof.
  intro. destruct v; try reflexivity.
  destruct i, s; try reflexivity; simpl;
    ((rewrite Int.sign_ext_idem by lia) || (rewrite Int.zero_ext_idem by lia));
    reflexivity.
Qed.
