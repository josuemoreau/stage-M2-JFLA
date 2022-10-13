Require Import Coq.Bool.Bool.

Require Import ZArith.

From compcert Require Import Archi Maps.

Inductive intsize : Type := I8 | I16 | I32.

Scheme Equality for intsize.

Definition max_intsize s1 s2 :=
  match s1, s2 with
  | I8, _ => s2
  | I16, I8 => s1
  | I16, _ => s2
  | I32, I8 | I32, I16 => s1
  | I32, _ => s2
  end.

Definition eq_intsize s1 s2 :=
  match s1, s2 with
  | I8, I8 => true
  | I16, I16 => true
  | I32, I32 => true
  | _, _ => false
  end.

Lemma eq_intsize_correct:
  forall sz1 sz2,
    eq_intsize sz1 sz2 = true -> sz1 = sz2.
Proof. destruct sz1, sz2; simpl; intros; easy. Qed.

Inductive floatsize : Type := F32 | F64.

Definition eq_floatsize s1 s2 :=
  match s1, s2 with
  | F32, F32 => true
  | F64, F64 => true
  | _, _ => false
  end.

Inductive signedness : Type := Signed | Unsigned.

Scheme Equality for signedness.

Definition max_signedness s1 s2 :=
  match s1, s2 with
  | Signed, Signed => Signed
  | _, _ => Unsigned
  end.

Definition eq_signedness s1 s2 :=
  match s1, s2 with
  | Unsigned, Unsigned => true
  | Signed, Signed => true
  | _, _ => false
  end.

Inductive typ : Type :=
| Tvoid
| Tbool
| Tint: intsize -> signedness -> typ
| Tint64: signedness -> typ
| Tfloat: floatsize -> typ
| Tarr: bool -> typ -> typ.

Scheme Equality for typ.

Definition Tuint64 := Tint64 Unsigned.

Fixpoint eq_typ (t1 t2: typ) : bool :=
  match t1, t2 with
  | Tvoid, Tvoid => true
  | Tbool, Tbool => true
  | Tint64 s1, Tint64 s2 => eq_signedness s1 s2
  | Tint s1 Unsigned, Tint s2 Unsigned => eq_intsize s1 s2
  | Tint s1 Signed, Tint s2 Signed => eq_intsize s1 s2
  | Tfloat s1, Tfloat s2 => eq_floatsize s1 s2
  | Tarr b1 t1, Tarr b2 t2 => eq_typ t1 t2 && eqb b1 b2
  | _, _ => false
  end.

Lemma eq_typ_correct:
  forall t1 t2, eq_typ t1 t2 = true -> t1 = t2.
Proof.
  induction t1; destruct t2;
    try destruct s; try destruct i; try destruct s0; try destruct i0;
    try destruct f; try destruct f0;
    simpl; intros; try easy.
  apply andb_prop in H. destruct H. rewrite (IHt1 _ H). destruct b, b0; easy.
Qed.

Lemma eq_typ_complete:
  forall t1 t2, t1 = t2 -> eq_typ t1 t2 = true.
Proof.
  induction t1; destruct t2;
    try destruct s; try destruct i; try destruct s0; try destruct i0;
    try destruct f; try destruct f0;
    simpl; intros; try easy.
  injection H. intros [= <-] [= <-]. apply andb_true_intro. destruct b; split; eauto.
Qed.

Definition typ_sig (t: typ) : option signedness :=
  match t with
  | Tint _ sig => Some sig
  | _ => None
  end.

Definition tenv := PTree.t typ.    (* environnement des types *)

Definition typ_sizeof (t: typ) : Z :=
  match t with
  | Tvoid | Tbool => 1
  | Tint  I8 _ => 1
  | Tint I16 _ => 2
  | Tint I32 _ => 4
  | Tint64 _ => 8
  | Tfloat F32 => 4
  | Tfloat F64 => 8
  | Tarr _ _ => if Archi.ptr64 then 8 else 4
  end.
