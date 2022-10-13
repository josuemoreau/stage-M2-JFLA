Require Import String.
Require Import Coq.Lists.List Coq.Lists.ListDec.
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import ZArith.
Require Import Eqdep_dec.

Import ListNotations.

From compcert Require Import Integers Maps Errors.

Definition option_get {A: Type} (o: option A) (default: A) :=
  match o with
  | None => default
  | Some a => a
  end.

Lemma option_not_None_exists {A: Type} (x: option A):
  x <> None -> exists y, x = Some y.
Proof.
  intros. induction x.
  - exists a. reflexivity.
  - exfalso. contradiction.
Qed.

Fixpoint replace_nth {A: Type} (l: list A) (n: nat) (x: A) : option (list A) :=
  match l with
  | [] => None
  | y :: l =>
      match n with
      | 0%nat => Some (x :: l)
      | S n => option_map (fun l => y :: l) (replace_nth l n x)
      end
  end.

Lemma replace_nth_Some1 {A: Type} (n: nat) (x: A):
  forall (l: list A),
    replace_nth l n x <> None -> n < length l.
Proof.
  + induction n, l.
    - intro. simpl in H. contradiction.
    - intro. simpl. lia.
    - intro. cbn in H. contradiction.
    - intro. cbn in H.
      unfold option_map in H.
      destruct (replace_nth l n x) eqn:H0; try contradiction.
      cbn. apply Lt.lt_n_S.
      specialize (IHn l). apply IHn.
      intro. rewrite H0 in H1. discriminate.
Qed.

Lemma replace_nth_Some2 {A: Type} (n: nat) (x: A):
  forall (l: list A),
    n < length l -> replace_nth l n x <> None.
Proof.
  + induction n, l.
    - intro. simpl in H. lia.
    - intro. simpl. discriminate.
    - intro. cbn in H. lia.
    - intro. cbn in H. apply Lt.lt_S_n in H.
      specialize (IHn l H). simpl.
      destruct (replace_nth l n x); try easy.
Qed.

Lemma replace_nth_Some {A: Type} (l: list A) (n: nat) (x: A):
  replace_nth l n x <> None <-> n < length l.
Proof.
  split. apply replace_nth_Some1. apply replace_nth_Some2.
Qed.

Lemma replace_nth_None1 {A: Type} (n: nat) (x: A):
  forall (l: list A),
    replace_nth l n x = None -> length l <= n.
Proof.
  + induction n, l.
    - intro. auto.
    - intro. simpl in H. discriminate.
    - intro. simpl. lia.
    - intro. simpl in H.
      unfold option_map in H.
      destruct (replace_nth l n x) eqn:H0; try discriminate.
      cbn. apply Le.le_n_S.
      specialize (IHn l H0). assumption.
Qed.

Lemma replace_nth_None2 {A: Type} (n: nat) (x: A):
  forall (l: list A),
    length l <= n -> replace_nth l n x = None.
Proof.
  + induction n, l.
    - intro. auto.
    - intro. simpl in H. lia.
    - intro. auto.
    - intro. simpl in H. apply Le.le_S_n in H.
      specialize (IHn l H). simpl.
      destruct (replace_nth l n x); try easy.
Qed.

Lemma replace_nth_None {A: Type} (l: list A) (n: nat) (x: A):
  replace_nth l n x = None <-> length l <= n.
Proof.
  split. apply replace_nth_None1. apply replace_nth_None2.
Qed.

Lemma replace_nth_length {A: Type}:
  forall (l: list A) (n: nat) (x: A) (l': list A),
    replace_nth l n x = Some l' ->
    length l = length l'.
Proof.
  induction l; simpl; intros. easy.
  destruct n. revert H; intros [= <-]. easy.
  destruct replace_nth eqn:Hr; try discriminate. revert H; intros [= <-]. simpl. eauto.
Qed.

Lemma replace_nth_nth_error_same {A: Type}:
  forall (l l': list A) (n: nat) (x: A),
    replace_nth l n x = Some l' ->
    nth_error l' n = Some x.
Proof.
  induction l; simpl; intros. easy.
  destruct n. revert H; intros [= <-]. easy.
  destruct replace_nth eqn:Hr; try discriminate. revert H; intros [= <-]. simpl. eauto.
Qed.

Lemma replace_nth_nth_error_other {A: Type}:
  forall (l l': list A) (n: nat) (x: A),
    replace_nth l n x = Some l' ->
    forall n',
      n <> n' ->
      nth_error l' n' = nth_error l n'.
Proof.
  induction l; simpl; intros. easy.
  destruct n. revert H; intros [= <-]. destruct n'. contradiction. reflexivity.
  destruct replace_nth eqn:Hr; try discriminate. revert H; intros [= <-].
  destruct n'. reflexivity. destruct (PeanoNat.Nat.eq_dec n n').
  apply eq_S in e. contradiction. simpl. eauto.
Qed.

Lemma in_map_fst_pair {A B: Type} (l: list (A * B)) (x: A):
  In x (map fst l) -> exists y, In (x, y) l.
Proof.
  induction l; cbn; intros.
  + contradiction.
  + destruct H.
    exists (snd a). rewrite <- H. eauto using surjective_pairing.
    destruct (IHl H) as [y Hy]. eauto.
Qed.

Lemma in_map_pair_fst {A B: Type} (l: list (A * B)) (x: A) (y: B):
  In (x, y) l -> In x (map fst l).
Proof.
  induction l; cbn. eauto. intros. destruct H. rewrite H. eauto. eauto.
Qed.

Lemma in_map_pair_snd {A B: Type} (l: list (A * B)) (x: A) (y: B):
  In (x, y) l -> In y (map snd l).
Proof.
  induction l; cbn. eauto. intros. destruct H. rewrite H. eauto. eauto.
Qed.


Fixpoint list_assoc_pos {A: Type} (l: list (positive * A)) (x: positive) : option A :=
  match l with
  | [] => None
  | (k, v) :: l =>
      if (k =? x)%positive then Some v
      else list_assoc_pos l x
  end.

Lemma list_assoc_pos_Some:
  forall A l x (y : A),
    list_assoc_pos l x = Some y -> In (x, y) l.
Proof.
  induction l; intros.
  + easy.
  + simpl. simpl in H. destruct a as [k v].
    case ((k =? x)%positive) eqn:Heq in H.
    - apply Peqb_true_eq in Heq. revert Heq H; intros [= ->] [= ->]. left. reflexivity.
    - eauto.
Qed.

Lemma list_assoc_pos_Some2:
  forall A l x (y: A),
    In (x, y) l -> exists z, list_assoc_pos l x = Some z.
Proof.
  induction l; cbn; intros.
  + easy.
  + destruct a as [k v]. destruct H.
    - inversion_clear H. rewrite Pos.eqb_refl. eexists. reflexivity.
    - specialize (IHl _ _ H). destruct IHl as [z Hz].
      case ((k =? x)%positive); eexists; eauto.
Qed.

(* Inductive list_assoc_nodup {A: Type}: list (positive * A) -> Prop :=
   | LANoDup_nil: list_assoc_nodup []
   | LANoDup_cons: forall x y l,
       list_assoc_pos l x = None ->
       list_assoc_nodup l ->
       list_assoc_nodup ((x, y) :: l). *)

Definition list_assoc_nodup {A: Type} (l: list (positive * A)) :=
  NoDup (map fst l).

(* Lemma list_assoc_pos_split {A: Type} (l1 l2: list (positive * A)) (x: positive) (y: A):
     exists y, list_assoc_pos (l1 ++ (x, y) :: l2) x = Some z. *)

(* Lemma list_assoc_pos_Some_nodup {A: Type} (l: list (positive * A)):
     forall x y,
       list_assoc_nodup l ->
       In (x, y) l ->
       list_assoc_pos l x = Some y.
   Proof.
     induction l; simpl; intros.
     + contradiction.
     + destruct a. destruct H0.
       - inversion_clear H0. rewrite Pos.eqb_refl. reflexivity.
       - inversion_clear H. destruct ((p =? x)%positive) eqn:Heq.
         * apply Peqb_true_eq in Heq. rewrite Heq in H1.
           rewrite (IHl _ _ H2 H0) in H1. discriminate.
         * eauto.
   Qed. *)

Lemma list_assoc_pos_Some_nodup {A: Type} (l: list (positive * A)):
  forall x y,
    list_assoc_nodup l ->
    In (x, y) l ->
    list_assoc_pos l x = Some y.
Proof.
  induction l; simpl; intros.
  + contradiction.
  + destruct a. destruct H0.
    - inversion_clear H0. rewrite Pos.eqb_refl. reflexivity.
    - inversion_clear H. destruct ((p =? x)%positive) eqn:Heq.
      * apply Peqb_true_eq in Heq. rewrite Heq in H1.
        apply in_map_pair_fst in H0. exfalso. exact (H1 H0).
      * eauto.
Qed.

Lemma list_assoc_nodup_injective {A: Type} (l: list (positive * A)):
  forall x y y',
    list_assoc_nodup l ->
    In (x, y) l ->
    In (x, y') l ->
    y = y'.
Proof.
  intros. apply list_assoc_pos_Some_nodup in H0, H1; try eassumption.
  revert H0 H1; intros [= ->] [= <-]. reflexivity.
Qed.

Local Open Scope bool_scope.

Declare Scope option_bool_monad_scope.

Definition option_bind {A B: Type} (o: option A) (f: A -> option B) : option B :=
  match o with
  | Some x => f x
  | None => None
  end.

Definition option_bool_bind {A: Type} (o: option A) (f: A -> bool) : bool :=
  match o with
  | Some x => f x
  | None => false
  end.

Definition option_res_bind {A B: Type} (o: option A) (f: A -> res B) : res B :=
  match o with
  | Some x => f x
  | None => Error [ MSG "" ]
  end.

Notation "'do' X <- A ; B" :=
  (option_bind A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200) : option_bool_monad_scope.

Notation "'do*' X <- A ; B" :=
  (option_bool_bind A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200) : option_bool_monad_scope.

Notation "'do**' X <- A ; B" :=
  (option_res_bind A (fun X => B))
    (at level 200, X name, A at level 100, B at level 200) : option_bool_monad_scope.

Ltac rewrite_one_equality :=
  match goal with
  | H: ?A = ?B |- _ =>
    try (revert H; intros [= <-]);
    try (revert H; intros [= ->])
  end.

Ltac rewrite_equalities :=
  repeat (rewrite_one_equality).

(* Parameter m: PTree.t nat.
   Parameter k: positive.
   Compute (PTree.xelements (PTree.set 100000 0 (PTree.set 5 15 PTree.Empty)) 8). *)

Lemma PTree_keys_set {A: Type} (k: positive) (v: A) (x: positive) (m: PTree.t A):
  In x (map fst (PTree.elements m)) ->
  In x (map fst (PTree.elements (PTree.set k v m))).
Proof.
  intros. apply in_map_fst_pair in H. destruct H as [y Hy].
  apply PTree.elements_complete in Hy.
  destruct (Pos.eq_dec x k).
  + apply in_map_pair_fst with (y := v).
    revert e; intros [= <-].
    apply PTree.elements_correct.
    rewrite PTree.gsspec. apply Coqlib.peq_true.
  + apply in_map_pair_fst with (y := y).
    apply PTree.elements_correct.
    rewrite PTree.gsspec. rewrite Hy. apply Coqlib.peq_false with (1 := n).
Qed.

Lemma PTree_map'_set0 {A B: Type} (i j: positive) (x: A) (f: positive -> A -> B):
  PTree.map' f (PTree.set0 i x) j
  = PTree.set0 i (f (PTree.prev (PTree.prev_append i j)) x).
Proof. revert j. induction i; simpl; intros; try (rewrite IHi); eauto. Qed.

Lemma PTree_map'_set' {A B: Type} (i j: positive) (x: A) (m: PTree.tree' A) (f: positive -> A -> B):
  PTree.map' f (PTree.set' i x m) j
  = PTree.set' i (f (PTree.prev (PTree.prev_append i j)) x) (PTree.map' f m j).
Proof.
  revert j m. induction i; simpl; intros; destruct m; simpl; try eauto;
    try rewrite IHi; try rewrite PTree_map'_set0; reflexivity.
Qed.

Lemma PTree_map_set {A B: Type} (i: positive) (x: A) (m: PTree.t A) (f: positive -> A -> B):
  PTree.map f (PTree.set i x m) = PTree.set i (f i x) (PTree.map f m).
Proof.
  intros. destruct m as [|m]; simpl.
  + rewrite PTree_map'_set0. unfold PTree.set.
    rewrite PTree.prev_append_prev. reflexivity.
  + rewrite PTree_map'_set'. rewrite PTree.prev_append_prev. reflexivity.
Qed.

Local Open Scope error_monad_scope.

Fixpoint list_map_error {A B: Type} (f: A -> res B) (l: list A) : res (list B) :=
  match l with
  | [] => OK []
  | x :: l =>
      do y  <- f x;
      do l' <- list_map_error f l;
      OK (y :: l')
  end.

Lemma in_list_map_error {A B: Type} (f: A -> res B) (l1: list A) (l2: list B) (x: A):
  list_map_error f l1 = OK l2 ->
  In x l1 -> exists y, f x = OK y /\ In y l2.
Proof.
  intros. apply in_split in H0. destruct H0 as [u1 [u2 H0]].
  revert H0; intros [= ->]. revert l2 H. induction u1; simpl; intros.
  + destruct f eqn:Hf, list_map_error; try discriminate.
    revert H; intros [= <-]. simpl. eexists. tauto.
  + destruct (f a), list_map_error eqn:H0; try discriminate.
    revert H; intros [= <-]. specialize (IHu1 _ eq_refl).
    destruct IHu1 as [y [H1 H2]]. eexists. simpl. eauto.
Qed.

Lemma in_list_map_error_iff {A B: Type} (f: A -> res B) (l1: list A) (l2: list B) (y: B):
  list_map_error f l1 = OK l2 ->
  In y l2 <-> exists x, f x = OK y /\ In x l1.
Proof.
  split; intro.
  + apply in_split in H0. destruct H0 as [u1 [u2 [= ->]]].
    revert l1 H. induction u1; simpl; intros.
    - destruct l1; try discriminate.
      simpl in H. destruct f eqn:Hf, list_map_error; try discriminate.
      revert H; intros [= <-]. exists a. split; simpl; tauto.
    - destruct l1; try discriminate.
      simpl in H. destruct f, list_map_error eqn:H'; try discriminate.
      revert H; intros [= <-]. revert H0; intros [= ->].
      destruct (IHu1 _ H') as [x [H1 H2]]. exists x. split; simpl; tauto.
  + destruct H0 as [x [H1 H2]]. apply in_split in H2.
    destruct H2 as [u1 [u2 [= ->]]].
    revert l2 H. induction u1; simpl; intros.
    - destruct f eqn:Hf, list_map_error; try discriminate.
      revert H; intros [= <-]. revert H1; intros [= <-]. simpl. tauto.
    - destruct (f a), list_map_error eqn:H'; try discriminate.
      revert H; intros [= <-]. simpl. eauto.
Qed.

Lemma length_succ_cons {A: Type}:
  forall (l: list A) n,
    S n = length l <-> exists x l', l = x :: l' /\ n = length l'.
Proof.
  intros. split; intros.
  + destruct l. discriminate. exists a, l. split; eauto.
  + destruct H as [x [l' [H1 H2]]]. rewrite H1, H2. reflexivity.
Qed.

Theorem in_split_last_length {A: Type}:
  (forall x y: A, {x = y} + {x <> y}) ->
  forall x (n: nat) (l: list A),
    n = length l -> In x l -> exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l2.
Proof.
  intros Hdec x.
  change (forall (n: nat),
             (fun n => forall l,
                  n = Datatypes.length l ->
                  In x l ->
                  exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l2) n).
  apply (well_founded_induction Wf_nat.lt_wf). intros.
  destruct x0.
  + apply eq_sym in H0. apply length_zero_iff_nil in H0.
    rewrite H0 in H1. contradiction.
  + apply length_succ_cons in H0. destruct H0 as [a [l' [[= ->] H0]]].
    specialize (H x0 (PeanoNat.Nat.lt_succ_diag_r x0) l' H0).
    destruct H1. revert H1; intros [= ->].
    destruct (In_dec Hdec x l').
    - specialize (H i). destruct H as [l1 [l2 [[= ->] H]]].
      exists (x :: l1), l2. eauto.
    - exists [], l'. eauto.
    - specialize (H H1). destruct H as [l1 [l2 [[= ->] H]]].
      exists (a :: l1), l2. eauto.
Qed.

Theorem in_split_last {A: Type}:
  (forall x y: A, {x = y} + {x <> y}) ->
  forall x (l: list A),
    In x l -> exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l2.
Proof.
  intros Heqdec x l Hin.
  exact (in_split_last_length Heqdec x _ l eq_refl Hin).
Qed.

Fixpoint map_error' {A B} (f: positive -> A -> res B) (m: PTree.tree' A) (i: positive)
  {struct m} : (res (PTree.tree' B)) :=
    match m with
    | PTree.Node001 r =>
        do m' <- map_error' f r (xI i); OK (PTree.Node001 m')
    | PTree.Node010 x =>
        do x' <- f (PTree.prev i) x;
        OK (PTree.Node010 x')
    | PTree.Node011 x r =>
        do m' <- map_error' f r (xI i);
        do x' <- f (PTree.prev i) x;
        OK (PTree.Node011 x' m')
    | PTree.Node100 l =>
        do m' <- map_error' f l (xO i); OK (PTree.Node100 m')
    | PTree.Node101 l r =>
        do m1 <- map_error' f l (xO i);
        do m2 <- map_error' f r (xI i);
        OK (PTree.Node101 m1 m2)
    | PTree.Node110 l x =>
        do m' <- map_error' f l (xO i);
        do x' <- f (PTree.prev i) x;
        OK (PTree.Node110 m' x')
    | PTree.Node111 l x r =>
        do m1 <- map_error' f l (xO i);
        do m2 <- map_error' f r (xI i);
        do x' <- f (PTree.prev i) x;
        OK (PTree.Node111 m1 x' m2)
    end.

Definition map_error {A B} (f: positive -> A -> res B) (m: PTree.t A) : res (PTree.t B) :=
    match m with
    | PTree.Empty => OK PTree.Empty
    | PTree.Nodes m =>
        do m' <- map_error' f m xH; OK (PTree.Nodes m')
    end.

Lemma map_error'_OK_f:
  forall {A B} (f: positive -> A -> res B) (i j : positive)
         (m: PTree.tree' A) (m': PTree.tree' B) (x: A),
    map_error' f m j = OK m' ->
    PTree.get' i m = Some x ->
    exists y, f (PTree.prev (PTree.prev_append i j)) x = OK y.
Proof.
  induction i; intros; destruct m; simpl;
    ((simpl in H; destruct (map_error') eqn:H2, (map_error') eqn:H3 in H)
     || (simpl in H; destruct (map_error') eqn:H2 in H)
         || idtac);
    (discriminate
     || (simpl in H; destruct f eqn:Hf in H; try discriminate)
     || idtac);
    revert H; intros [= <-];
    eauto || revert H0; intros [= <-]; exists b; assumption.
Qed.

Lemma get_map_error'_Some:
  forall {A B} (f: positive -> A -> res B) (i j : positive)
         (m: PTree.tree' A) (m': PTree.tree' B) (x: A) (y: B),
    map_error' f m j = OK m' ->
    PTree.get' i m = Some x ->
    f (PTree.prev (PTree.prev_append i j)) x = OK y ->
    PTree.get' i m' = Some y.
Proof.
  induction i; intros; destruct m; simpl;
    ((simpl in H; destruct (map_error') eqn:H2, (map_error') eqn:H3 in H)
     || (simpl in H; destruct (map_error') eqn:H2 in H)
         || idtac);
    (discriminate
     || (simpl in H; destruct f eqn:Hf in H; try discriminate)
     || idtac);
    revert H; intros [= <-];
    eauto || revert H0 H1 Hf; intros [= ->] [= ->] [= ->]; eauto.
Qed.

Lemma get_map_error'_None:
  forall {A B} (f: positive -> A -> res B) (i j : positive)
         (m: PTree.tree' A) (m': PTree.tree' B),
    map_error' f m j = OK m' ->
    PTree.get' i m = None ->
    PTree.get' i m' = None.
Proof.
  induction i; intros; destruct m; simpl;
  ((simpl in H; destruct (map_error') eqn:H2, (map_error') eqn:H3 in H)
     || (simpl in H; destruct (map_error') eqn:H2 in H)
         || idtac);
    (discriminate
     || (simpl in H; destruct f eqn:Hf in H; try discriminate)
     || idtac);
    revert H; intros [= <-]; eauto.
Qed.

Theorem map_error_OK_f:
  forall {A B} (f: positive -> A -> res B) (i : positive)
         (m: PTree.t A) (m': PTree.t B) (x: A),
    map_error f m = OK m' ->
    PTree.get i m = Some x ->
    exists y, f i x = OK y.
Proof.
  intros; destruct m as [|m]; simpl. revert H; intros [= <-]; discriminate.
  simpl in H. destruct map_error' eqn:H2; try discriminate.
  revert H; intros [= <-]. unfold PTree.get.
  destruct (map_error'_OK_f f i 1 m t x H2 H0) as [y Hy].
  exists y. rewrite PTree.prev_append_prev in Hy. assumption.
Qed.

Theorem get_map_error_Some:
  forall {A B} (f: positive -> A -> res B) (i: positive) (m: PTree.t A) (m': PTree.t B) (x : A) (y : B),
    map_error f m = OK m' ->
    PTree.get i m = Some x ->
    f i x = OK y ->
    PTree.get i m' = Some y.
Proof.
  intros; destruct m as [|m]; simpl. revert H; intros [= <-]; discriminate.
  simpl in H. destruct map_error' eqn:H2; try discriminate.
  revert H; intros [= <-]. unfold PTree.get.
  rewrite (get_map_error'_Some _ i _ _ _ x y H2); try auto.
  repeat f_equal. rewrite PTree.prev_append_prev. eauto.
Qed.

Theorem get_map_error_None:
  forall {A B} (f: positive -> A -> res B) (i: positive) (m: PTree.t A) (m': PTree.t B),
    map_error f m = OK m' ->
    PTree.get i m = None ->
    PTree.get i m' = None.
Proof.
  intros; destruct m as [|m]; simpl. revert H; intros [= <-]; eauto.
  simpl in H. destruct map_error' eqn:H2; try discriminate.
  revert H; intros [= <-]. unfold PTree.get.
  rewrite (get_map_error'_None _ i _ _ _ H2); try auto.
Qed.

Lemma map_error'_set0 {A B: Type} (i j: positive) (x: A) (f: positive -> A -> res B):
  map_error' f (PTree.set0 i x) j =
  do v <- f (PTree.prev (PTree.prev_append i j)) x;
  OK (PTree.set0 i v).
Proof.
  revert j. induction i; simpl; intros; try rewrite IHi; destruct f; reflexivity.
Qed.

Local Close Scope error_monad_scope.

Lemma option_None_not_Some:
  forall A x,
    x = None <-> forall (y: A), x <> Some y.
Proof.
  split; intros.
  + intro. rewrite H0 in H. discriminate.
  + destruct x. specialize (H a). contradiction. reflexivity.
Qed.

Lemma PTree_elements_empty:
  forall A (t: PTree.t A),
    PTree.elements t = [] -> t = PTree.empty A.
Proof.
  intros.
  apply PTree.extensionality_empty. intro.
  apply option_None_not_Some. intros y H1.
  apply PTree.elements_correct in H1.
  rewrite H in H1. contradiction.
Qed.

Fixpoint index_of_rec {A: Type} (eq_dec: forall x y: A, {x = y} + {x <> y})
                                (l: list A) (x: A) (i: nat) : option nat :=
  match l with
  | [] => None
  | y :: l => if eq_dec x y then Some i
              else index_of_rec eq_dec l x (i + 1)
  end.

Definition index_of {A: Type} (eq_dec: forall x y: A, {x = y} + {x <> y})
                              (l: list A) (x: A) : option nat :=
  index_of_rec eq_dec l x 0.

Lemma index_of_rec_S_Some_0 {A: Type}:
  forall eq_dec (l: list A) x i,
    ~(index_of_rec eq_dec l x (S i) = Some 0).
Proof. induction l; simpl; intros; [| destruct eq_dec]; easy. Qed.

Lemma index_of_rec_le_Some {A: Type}:
  forall eq_dec (l: list A) x n i,
    index_of_rec eq_dec l x n = Some i ->
    n <= i.
Proof.
  induction l; simpl; intros.
  + discriminate.
  + destruct (eq_dec x a).
    revert H; intros [= <-]. easy.
    specialize (IHl _ _ _ H). lia.
Qed.

Lemma index_of_nth_error {A: Type}:
  forall eq_dec i (l: list A) x,
    index_of eq_dec l x = Some i ->
    nth_error l i = Some x.
Proof.
  unfold index_of. intros until x. rewrite (Minus.minus_n_O i) at 2.
  generalize 0. revert l i. induction l; simpl; intros i n H0.
  + discriminate.
  + unfold index_of in H0. simpl in H0.
    destruct (eq_dec x a).
    revert H0 e; intros [= <-] [= <-]. rewrite PeanoNat.Nat.sub_diag. reflexivity.
    destruct i.
    - destruct l. discriminate.
      rewrite PeanoNat.Nat.add_1_r in H0.
      apply index_of_rec_S_Some_0 in H0. contradiction.
    - specialize (IHl _ _ H0). rewrite PeanoNat.Nat.add_1_r in IHl. simpl in IHl.
      apply index_of_rec_le_Some in H0.
      rewrite <- Minus.minus_Sn_m. eauto. lia.
Qed.

Lemma Zcomparison_eq_dec:
  forall x y: Datatypes.comparison, {x = y} + {x <> y}.
Proof. decide equality. Qed.

Lemma Z_lt_eq_proofs:
  forall (n m : Z) (x y: (n < m)%Z), x = y.
Proof. intros. unfold Z.lt in x, y. exact (UIP_dec Zcomparison_eq_dec x y). Qed.

Lemma Int64_neq_unsigned (x y: int64):
  x <> y ->
  Int64.unsigned x <> Int64.unsigned y.
Proof.
  intros H H0. apply H.
  destruct x, y. simpl in *. revert H0; intros [= <-].
  destruct intrange as [low high], intrange0 as [low0 high0].
  now rewrite (Z_lt_eq_proofs _ _ low low0), (Z_lt_eq_proofs _ _ high high0).
Qed.

Lemma Int64_neq_lt_or_gt (x y: int64):
  x <> y ->
  Int64.ltu x y = true \/ Int64.ltu y x = true.
Proof.
  intro. apply Int64_neq_unsigned, Z.lt_gt_cases in H.
  destruct H; unfold Int64.ltu; rewrite Coqlib.zlt_true with (1 := H); eauto.
Qed.

Lemma Zmult_le_nonneg_nonneg_r:
  forall (m n p : Z),
    (0 < m)%Z -> (0 < p)%Z ->
    (m * n <= p)%Z ->
    (n <= p)%Z.
Proof.
  intros. apply Zorder.Zmult_le_reg_r with (p := m). lia.
  rewrite Z.mul_comm. assert (p <= p * m)%Z.
  apply Z.le_mul_diag_r. lia. lia. lia.
Qed.

Lemma Ptrofs_max_unsigned_gt_8:
  (8 < Ptrofs.max_unsigned)%Z.
Proof.
  unfold Ptrofs.max_unsigned, Ptrofs.modulus, Ptrofs.wordsize, Wordsize_Ptrofs.wordsize;
    destruct Archi.ptr64; simpl; lia.
Qed.

Definition list_rect_In {A: Type} (l: list A) (P: list A -> Type)
  (f: forall (l0: list A) (a: P l0) (x: A), In x l -> P (x :: l0)) : P [] -> P l.
  induction l.
  + intro a0. exact a0.
  + intro a0.
    assert (forall l0 : list A, P l0 -> forall x : A, In x l -> P (x :: l0)).
    intros. exact (f l0 X x (or_intror _ H)).
    specialize (IHl X a0). exact (f l IHl a (or_introl _ eq_refl)).
Defined.

(* Definition foldi_left_H {A B: Type} (l: list B) (idx: nat) (Hidx: (idx = O))
     (f: forall (a: A) (idx: nat) (x: B), (idx < length l)%nat -> In x l -> A) : A -> A.
     pose proof (eq_refl (length l)).
     rewrite <- plus_O_n in H at 1. rewrite <- Hidx in H. revert H f. clear Hidx.
     generalize (length l) at 2 3. intros N. revert idx.
     induction l; simpl; intros idx HN f a0.
     + exact a0.
     + assert (idx < N)%nat as Hidx. lia.
       pose proof (f a0 idx a Hidx (or_introl _ eq_refl)) as a1.
       rewrite <- PeanoNat.Nat.add_succ_comm in HN.
       refine (IHl _ HN _ a1). intros.
       exact (f a2 idx0 x H (or_intror _ H0)).
   Defined.

   Definition foldi_left_HO {A B: Type} (l: list B) f (a: A) :=
     foldi_left_H l O eq_refl f a.

   Compute (fold_left_H [1; 2; 3] (fun l x Hin => x :: l) []).
   Compute (foldi_left_H [1; 2; 3] 0 eq_refl (fun l idx x Hidx Hin => x :: l) []).
   Compute (foldi_left_HO [1; 2; 3] (fun l idx x Hidx Hin => x :: l) []). *)

Lemma Coqlib_list_norepet_cons_inv:
  forall {A: Type} (a: A) l,
    Coqlib.list_norepet (a :: l) ->
    ~In a l /\ Coqlib.list_norepet l.
Proof. intros. inversion H. tauto. Qed.

Lemma Coqlib_list_norepet_NoDup {A: Type}:
  forall (l: list A), NoDup l -> Coqlib.list_norepet l.
Proof.
  induction l; intro. apply Coqlib.list_norepet_nil.
  inversion_clear H. apply Coqlib.list_norepet_cons; eauto.
Qed.
