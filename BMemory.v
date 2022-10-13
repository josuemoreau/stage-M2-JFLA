Require Import Coq.Lists.List.
Require Import BinNums BinInt BinPos.

Import ListNotations.

Require Import Types Ops BValues Syntax BUtils BEnv Typing.

From compcert Require Import Integers Maps.

Record memory_block := {
    blk_type: typ;
    blk_values: list value;
    blk_not_void: blk_type <> Tvoid;
    blk_valid_size: (typ_sizeof blk_type * Z.of_nat (Datatypes.length blk_values)
                                <= Ptrofs.max_unsigned)%Z;
    blk_well_typed: Forall (fun v => well_typed_value v blk_type) blk_values;
    blk_values_shrunk: Forall (fun v => v = shrink v) blk_values
  }.

Definition mem := PTree.t memory_block.

Definition empty_mem := PTree.empty memory_block.

Definition write_array (m: mem) (e: env) (id: ident) (n: Z) (v: value) : option (mem * env).
  refine (match e!id with
          | None => None
          | Some (Varr idarr lv) =>
              match m!idarr with
              | None => None
              | Some blk =>
                  match well_typed_value_bool v (blk_type blk) as wt
                        return well_typed_value_bool v (blk_type blk) = wt -> option (mem * env) with
                  | false => fun _ => None
                  | true => fun Hwt =>
                  match replace_nth (blk_values blk) (Z.to_nat n) (shrink v) as l
                        return replace_nth (blk_values blk) (Z.to_nat n) (shrink v) = l
                               -> option (mem * env) with
                  | None => fun _ => None
                  | Some lv' => fun H =>
                                    Some (PTree.set idarr {| blk_type := blk.(blk_type);
                                                             blk_values := lv';
                                                             blk_not_void := blk.(blk_not_void);
                                                             blk_valid_size := _ |} m,
                                          PTree.set id (Varr idarr lv') e)
                  end eq_refl
                  end eq_refl
              end
          | Some _ => None
          end).
  - rewrite <- replace_nth_length with (1 := H). exact blk.(blk_valid_size).
  - apply well_typed_value_bool_correct in Hwt.
    pose proof (blk_well_typed blk). revert lv' H H0. generalize (Z.to_nat n).
    induction (blk_values blk); simpl; intros. discriminate. destruct n0.
    * revert H; intros [= <-]. apply Forall_inv_tail in H0.
      apply Forall_cons with (2 := H0). exact (well_typed_value_shrink _ _ Hwt).
    * specialize (IHl n0). destruct replace_nth; try discriminate.
      revert H; intros [= <-]. apply Forall_cons.
      exact (Forall_inv H0). exact (IHl _ eq_refl (Forall_inv_tail H0)).
  - pose proof (blk_values_shrunk blk). revert lv' H H0. generalize (Z.to_nat n).
    induction (blk_values blk); simpl; intros. discriminate. destruct n0.
    * revert H; intros [= <-]. apply Forall_inv_tail in H0.
      apply Forall_cons with (2 := H0). rewrite <- shrink_shrink. reflexivity.
    * specialize (IHl n0). destruct replace_nth; try discriminate.
      revert H; intros [= <-]. apply Forall_cons.
      exact (Forall_inv H0). exact (IHl _ eq_refl (Forall_inv_tail H0)).
Defined.

Theorem write_array_modifs:
  forall m m' e e' id n v idarr blk,
    write_array m e id n v = Some (m', e') ->
    e!id = Some (Varr idarr (blk_values blk)) ->
    m!idarr = Some blk ->
    (exists blk',
        replace_nth (blk_values blk) (Z.to_nat n) (shrink v) = Some (blk_values blk') /\
        blk_type blk' = blk_type blk /\
        e'!id = Some (Varr idarr (blk_values blk')) /\
        m'!idarr = Some blk') /\
    (forall id', id' <> id -> e'!id' = e!id') /\
    (forall idarr', idarr' <> idarr -> m'!idarr' = m!idarr').
Proof.
  intros. unfold write_array in H. rewrite H0, H1 in H. simpl in H.
  revert H.
  generalize (eq_refl (well_typed_value_bool v (blk_type blk))).
  generalize (well_typed_value_bool_correct (blk_type blk) v).
  destruct (well_typed_value_bool v (blk_type blk)) eqn:Hwt; try discriminate.
  simpl; intros w e0.
  generalize (eq_refl (replace_nth (blk_values blk) (Z.to_nat n) (shrink v))).
  generalize (replace_nth_length (blk_values blk) (Z.to_nat n) (shrink v)).
  generalize (list_ind (fun l : list value =>
                  forall (n0 : nat) (lv'0 : list value),
                  @replace_nth value l n0 (shrink v) = @Some (list value) lv'0 ->
                  @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk)) l ->
                  @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk)) lv'0)
           (fun (_ : nat) (lv'0 : list value)
                    (H2 : @None (list value) = @Some (list value) lv'0)
                    (_ : @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk)) []) =>
                  False_ind
                    (@Forall value (fun v0 : value => well_typed_value v0 (blk_type blk)) lv'0)
                    (@eq_ind (option (list value)) (@None (list value))
                       (fun e3 : option (list value) =>
                        match e3 with
                        | Some _ => False
                        | None => True
                        end) I (@Some (list value) lv'0) H2)) (fun (a : value) (l : list value)
                    (IHl : forall (n0 : nat) (lv'0 : list value),
                           @replace_nth value l n0 (shrink v) = @Some (list value) lv'0 ->
                           @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk)) l ->
                           @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk)) lv'0)
                    (n0 : nat) (lv'0 : list value)
                    (H2 : match n0 with
                          | 0 => @Some (list value) (shrink v :: l)
                          | S n1 =>
                              @option_map (list value) (list value) (fun l0 : list value => a :: l0)
                                (@replace_nth value l n1 (shrink v))
                          end = @Some (list value) lv'0)
                    (H3 : @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk))
                            (a :: l)) =>
                  match
                    n0 as n1
                    return
                      (match n1 with
                       | 0 => @Some (list value) (shrink v :: l)
                       | S n2 =>
                           @option_map (list value) (list value) (fun l0 : list value => a :: l0)
                             (@replace_nth value l n2 (shrink v))
                       end = @Some (list value) lv'0 ->
                       @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk)) lv'0)
                  with
                  | 0 =>
                      fun H4 : @Some (list value) (shrink v :: l) = @Some (list value) lv'0 =>
                      @eq_ind (list value) (shrink v :: l)
                        (fun lv'1 : list value =>
                         @Some (list value) (shrink v :: l) = @Some (list value) lv'1 ->
                         @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk)) lv'1)
                        (fun
                           _ : @Some (list value) (shrink v :: l) =
                               @Some (list value) (shrink v :: l) =>
                         @Forall_cons value (fun v0 : value => well_typed_value v0 (blk_type blk))
                           (shrink v) l (well_typed_value_shrink v (blk_type blk) (w e0))
                           (@Forall_inv_tail value
                              (fun v0 : value => well_typed_value v0 (blk_type blk)) a l H3)) lv'0
                        (@f_equal (option (list value)) (list value)
                           (fun e3 : option (list value) =>
                            match e3 with
                            | Some l0 => l0
                            | None => shrink v :: l
                            end) (@Some (list value) (shrink v :: l)) (@Some (list value) lv'0) H4)
                        H4
                  | S n1 =>
                      fun
                        H4 : @option_map (list value) (list value) (fun l0 : list value => a :: l0)
                               (@replace_nth value l n1 (shrink v)) = @Some (list value) lv'0 =>
                      match
                        @replace_nth value l n1 (shrink v) as o
                        return
                          ((forall lv'1 : list value,
                            o = @Some (list value) lv'1 ->
                            @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk)) l ->
                            @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk)) lv'1) ->
                           @option_map (list value) (list value) (fun l0 : list value => a :: l0) o =
                           @Some (list value) lv'0 ->
                           @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk)) lv'0)
                      with
                      | Some a0 =>
                          fun
                            (IHl0 : forall lv'1 : list value,
                                    @Some (list value) a0 = @Some (list value) lv'1 ->
                                    @Forall value
                                      (fun v0 : value => well_typed_value v0 (blk_type blk)) l ->
                                    @Forall value
                                      (fun v0 : value => well_typed_value v0 (blk_type blk)) lv'1)
                            (H5 : @Some (list value) (a :: a0) = @Some (list value) lv'0) =>
                          @eq_ind (list value) (a :: a0)
                            (fun lv'1 : list value =>
                             @Some (list value) (a :: a0) = @Some (list value) lv'1 ->
                             @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk))
                               lv'1)
                            (fun _ : @Some (list value) (a :: a0) = @Some (list value) (a :: a0) =>
                             @Forall_cons value
                               (fun v0 : value => well_typed_value v0 (blk_type blk)) a a0
                               (@Forall_inv value
                                  (fun v0 : value => well_typed_value v0 (blk_type blk)) a l H3)
                               (IHl0 a0 (@eq_refl (option (list value)) (@Some (list value) a0))
                                  (@Forall_inv_tail value
                                     (fun v0 : value => well_typed_value v0 (blk_type blk)) a l H3)))
                            lv'0
                            (@f_equal (option (list value)) (list value)
                               (fun e3 : option (list value) =>
                                match e3 with
                                | Some l0 => l0
                                | None => a :: a0
                                end) (@Some (list value) (a :: a0)) (@Some (list value) lv'0) H5) H5
                      | None =>
                          fun
                            (_ : forall lv'1 : list value,
                                 @None (list value) = @Some (list value) lv'1 ->
                                 @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk))
                                   l ->
                                 @Forall value (fun v0 : value => well_typed_value v0 (blk_type blk))
                                   lv'1) (H5 : @None (list value) = @Some (list value) lv'0) =>
                          False_ind
                            (@Forall value (fun v0 : value => well_typed_value v0 (blk_type blk))
                               lv'0)
                            (@eq_ind (option (list value)) (@None (list value))
                               (fun e3 : option (list value) =>
                                match e3 with
                                | Some _ => False
                                | None => True
                                end) I (@Some (list value) lv'0) H5)
                      end (IHl n1) H4
                  end H2) (blk_values blk) (Z.to_nat n)).
  generalize (list_ind
                 (fun l : list value =>
                  forall (n0 : nat) (lv'0 : list value),
                  @replace_nth value l n0 (shrink v) = @Some (list value) lv'0 ->
                  @Forall value (fun v0 : value => v0 = shrink v0) l ->
                  @Forall value (fun v0 : value => v0 = shrink v0) lv'0)
                 (fun (_ : nat) (lv'0 : list value)
                    (H3 : @None (list value) = @Some (list value) lv'0)
                    (_ : @Forall value (fun v0 : value => v0 = shrink v0) []) =>
                  False_ind (@Forall value (fun v0 : value => v0 = shrink v0) lv'0)
                    (@eq_ind (option (list value)) (@None (list value))
                       (fun e3 : option (list value) =>
                        match e3 with
                        | Some _ => False
                        | None => True
                        end) I (@Some (list value) lv'0) H3))
                 (fun (a : value) (l : list value)
                    (IHl : forall (n0 : nat) (lv'0 : list value),
                           @replace_nth value l n0 (shrink v) = @Some (list value) lv'0 ->
                           @Forall value (fun v0 : value => v0 = shrink v0) l ->
                           @Forall value (fun v0 : value => v0 = shrink v0) lv'0)
                    (n0 : nat) (lv'0 : list value)
                    (H3 : match n0 with
                          | 0 => @Some (list value) (shrink v :: l)
                          | S n1 =>
                              @option_map (list value) (list value) (fun l0 : list value => a :: l0)
                                (@replace_nth value l n1 (shrink v))
                          end = @Some (list value) lv'0)
                    (H4 : @Forall value (fun v0 : value => v0 = shrink v0) (a :: l)) =>
                  match
                    n0 as n1
                    return
                      (match n1 with
                       | 0 => @Some (list value) (shrink v :: l)
                       | S n2 =>
                           @option_map (list value) (list value) (fun l0 : list value => a :: l0)
                             (@replace_nth value l n2 (shrink v))
                       end = @Some (list value) lv'0 ->
                       @Forall value (fun v0 : value => v0 = shrink v0) lv'0)
                  with
                  | 0 =>
                      fun H5 : @Some (list value) (shrink v :: l) = @Some (list value) lv'0 =>
                      @eq_ind (list value) (shrink v :: l)
                        (fun lv'1 : list value =>
                         @Some (list value) (shrink v :: l) = @Some (list value) lv'1 ->
                         @Forall value (fun v0 : value => v0 = shrink v0) lv'1)
                        (fun
                           _ : @Some (list value) (shrink v :: l) =
                               @Some (list value) (shrink v :: l) =>
                         @Forall_cons value (fun v0 : value => v0 = shrink v0)
                           (shrink v) l
                           (@eq_ind value (shrink v) (fun v0 : value => shrink v = v0)
                              (@eq_refl value (shrink v)) (shrink (shrink v))
                              (shrink_shrink v))
                           (@Forall_inv_tail value (fun v0 : value => v0 = shrink v0) a l H4)) lv'0
                        (@f_equal (option (list value)) (list value)
                           (fun e3 : option (list value) =>
                            match e3 with
                            | Some l0 => l0
                            | None => shrink v :: l
                            end) (@Some (list value) (shrink v :: l)) (@Some (list value) lv'0) H5)
                        H5
                  | S n1 =>
                      fun
                        H5 : @option_map (list value) (list value) (fun l0 : list value => a :: l0)
                               (@replace_nth value l n1 (shrink v)) = @Some (list value) lv'0 =>
                      match
                        @replace_nth value l n1 (shrink v) as o
                        return
                          ((forall lv'1 : list value,
                            o = @Some (list value) lv'1 ->
                            @Forall value (fun v0 : value => v0 = shrink v0) l ->
                            @Forall value (fun v0 : value => v0 = shrink v0) lv'1) ->
                           @option_map (list value) (list value) (fun l0 : list value => a :: l0) o =
                           @Some (list value) lv'0 ->
                           @Forall value (fun v0 : value => v0 = shrink v0) lv'0)
                      with
                      | Some a0 =>
                          fun
                            (IHl0 : forall lv'1 : list value,
                                    @Some (list value) a0 = @Some (list value) lv'1 ->
                                    @Forall value (fun v0 : value => v0 = shrink v0) l ->
                                    @Forall value (fun v0 : value => v0 = shrink v0) lv'1)
                            (H6 : @Some (list value) (a :: a0) = @Some (list value) lv'0) =>
                          @eq_ind (list value) (a :: a0)
                            (fun lv'1 : list value =>
                             @Some (list value) (a :: a0) = @Some (list value) lv'1 ->
                             @Forall value (fun v0 : value => v0 = shrink v0) lv'1)
                            (fun _ : @Some (list value) (a :: a0) = @Some (list value) (a :: a0) =>
                             @Forall_cons value (fun v0 : value => v0 = shrink v0) a a0
                               (@Forall_inv value (fun v0 : value => v0 = shrink v0) a l H4)
                               (IHl0 a0 (@eq_refl (option (list value)) (@Some (list value) a0))
                                  (@Forall_inv_tail value (fun v0 : value => v0 = shrink v0) a l H4)))
                            lv'0
                            (@f_equal (option (list value)) (list value)
                               (fun e3 : option (list value) =>
                                match e3 with
                                | Some l0 => l0
                                | None => a :: a0
                                end) (@Some (list value) (a :: a0)) (@Some (list value) lv'0) H6) H6
                      | None =>
                          fun
                            (_ : forall lv'1 : list value,
                                 @None (list value) = @Some (list value) lv'1 ->
                                 @Forall value (fun v0 : value => v0 = shrink v0) l ->
                                 @Forall value (fun v0 : value => v0 = shrink v0) lv'1)
                            (H6 : @None (list value) = @Some (list value) lv'0) =>
                          False_ind (@Forall value (fun v0 : value => v0 = shrink v0) lv'0)
                            (@eq_ind (option (list value)) (@None (list value))
                               (fun e3 : option (list value) =>
                                match e3 with
                                | Some _ => False
                                | None => True
                                end) I (@Some (list value) lv'0) H6)
                      end (IHl n1) H5
                  end H3) (blk_values blk) (Z.to_nat n)).
  destruct (replace_nth (blk_values blk) (Z.to_nat n) (shrink v)); try discriminate.
  intros. injection H. intros [= <-] [= <-]. do 2 rewrite PTree.gss. split.
  eexists. split; [|split; [|split; [|reflexivity]]]; reflexivity.
  split; intros; rewrite PTree.gso; easy.
Qed.

Theorem write_array_same:
  forall m m' e e' id n v idarr blk,
    write_array m e id n v = Some (m', e') ->
    e!id = Some (Varr idarr (blk_values blk)) ->
    m!idarr = Some blk ->
    (exists blk',
        replace_nth (blk_values blk) (Z.to_nat n) (shrink v) = Some (blk_values blk') /\
        blk_type blk' = blk_type blk /\
        e'!id = Some (Varr idarr (blk_values blk')) /\
        m'!idarr = Some blk').
Proof. intros. specialize write_array_modifs with (1 := H) (2 := H0). tauto. Qed.

Theorem write_array_other:
  forall m m' e e' id n v idarr blk,
    write_array m e id n v = Some (m', e') ->
    e!id = Some (Varr idarr (blk_values blk)) ->
    m!idarr = Some blk ->
    (forall id', id' <> id -> e'!id' = e!id') /\
    (forall idarr', idarr' <> idarr -> m'!idarr' = m!idarr').
Proof. intros until blk. intros H H0 H1.
       specialize write_array_modifs with (1 := H) (2 := H0). tauto. Qed.
