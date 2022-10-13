Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import BinNums BinInt BinPos.

Import ListNotations.

Require Import Types Ops BValues Syntax BUtils.

From compcert Require Import Integers Floats Maps Errors.

(* Definition senv := list (ident * ident).  (* environnement des tailles de tableaux *) *)
Definition env := PTree.t value.   (* environnement des valeurs *)

Definition genv := PTree.t fundef. (* environnement global / map des définitions de fonctions *)

Fixpoint sub_map' {A: Type} (m m': PTree.t A) (l: list positive) : PTree.t A :=
  match l with
  | [] => m'
  | p :: l =>
      match m!p with
      | None => sub_map' m m' l
      | Some a => sub_map' m (PTree.set p a m') l
      end
  end.

Definition sub_map {A: Type} (m: PTree.t A) (l: list positive) := sub_map' m (PTree.empty A) l.


Fixpoint build_func_env (e: env)
                        (params: list ident)
                        (vargs: list value)
  : option env :=
  match params, vargs with
  | [], [] => Some e
  | id :: params, v :: vargs =>
      match build_func_env e params vargs with
      | None => None
      | Some e => Some (PTree.set id v e)
      end
  | _, _ => None
  end.

Definition build_env {A: Type} (env: PTree.t A) (l: list (ident * A)) : PTree.t A :=
  fold_left (fun env x => PTree.set (fst x) (snd x) env) l env.

Lemma list_in_diff {A: Type} (l: list A):
  forall x y, In x l ->
              ~In y l ->
              x <> y.
Proof.
  induction l; intros.
  + contradiction.
  + simpl in H, H0. apply Decidable.not_or in H0. destruct H0. destruct H.
    - rewrite H in H0. assumption.
    - eauto.
Qed.

Lemma build_env_correct {A: Type} (l: list (ident * A)):
  NoDup (map fst l) ->
  forall e,
    (forall id, In id (map fst l) -> e!id = None) ->
    forall x, (In x (PTree.elements e) \/ In x l) <-> In x (PTree.elements (build_env e l)).
Proof.
  induction l; cbn; intros.
  + tauto.
  + destruct a as [id a].
    simpl in H. inversion_clear H.
    specialize IHl with (1 := H2). split; intro.
    - apply IHl; intros.
      * pose proof (list_in_diff (map fst l) _ _ H3 H1).
        rewrite PTree.gsspec. rewrite Coqlib.peq_false; eauto.
      * destruct H; try destruct H.
        ** destruct x as [id0 a0]. left.
           apply PTree.elements_complete in H. specialize (H0 id0). simpl in H0.
           apply PTree.elements_correct. rewrite PTree.gsspec.
           case (Pos.eq_dec id id0); intro H'.
           *** apply or_introl with (B := In id0 (map fst l)) in H'.
               apply H0 in H'. rewrite H' in H. discriminate.
           *** rewrite Coqlib.peq_false; eauto.
        ** revert H; intros [= <-].
           left. apply PTree.elements_correct. rewrite PTree.gsspec.
           rewrite Coqlib.peq_true. reflexivity.
        ** eauto.
    - apply IHl in H; intros.
      * destruct x as [id0 a0]. destruct H.
        ** apply PTree.elements_complete in H. rewrite PTree.gsspec in H.
           case (Pos.eq_dec id0 id); intro H'.
           *** revert H'; intros [= <-]. rewrite Coqlib.peq_true in H.
               revert H; intros [= <-]. eauto.
           *** rewrite Coqlib.peq_false with (1 := H') in H.
               left. apply PTree.elements_correct. assumption.
        ** eauto.
      * pose proof (list_in_diff (map fst l) _ _ H4 H1).
        rewrite PTree.gsspec. rewrite Coqlib.peq_false; eauto.
Qed.

Lemma build_env_correct_empty {A: Type} (l: list (ident * A)):
  NoDup (map fst l) ->
  forall x, (In x l <-> In x (PTree.elements (build_env (PTree.empty A) l))).
Proof.
  intros.
  pose proof (build_env_correct _ H _ (fun id _ => PTree.gempty A id) x).
  simpl in H0. tauto.
Qed.

(* Lemma build_env_list_assoc_nodup {A: Type} (l: list (ident * A)):
     forall e,
       (forall id, In id (map fst l) -> e!id = None) ->
       (NoDup (map fst (PTree.elements e)) /\ NoDup (map fst l))
       <-> NoDup (map fst (PTree.elements (build_env e l))).
   Proof.
     induction l; simpl; intros.
     + split; intros; [| split]; try tauto. apply NoDup_nil.
     + destruct a as [id a].
       simpl. split; intro.
       - destruct H0. inversion_clear H1.
         apply (IHl (PTree.set id a e)); intros.
         pose proof (list_in_diff (map fst l) _ _ H1 H2).
         rewrite PTree.gsspec. rewrite Coqlib.peq_false.

       split; intros.
       - destruct H0. inversion_clear H1.
         apply IHl.
         intros. *)

Definition genv_of_program (p: program) : genv :=
  build_env (PTree.empty fundef) p.(prog_defs).

Definition set_optenv (e: env) (optid: option ident) (v: value) :=
  match optid with
  | None    => e
  | Some id => PTree.set id v e
  end.
