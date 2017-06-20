Require Import List.
Require Import Omega.
Require Import Tactics.
Require Import VerdiTactics.
Require Import Setoid.
Require Import Classes.RelationClasses.
Import ListNotations.

Set Implicit Arguments.

Section lists.

  Hint Rewrite app_nil_r.


  Ltac deex :=
    match goal with
    | [ H: exists varname, _ |- _ ] =>
      let newvar := fresh varname in
      destruct H as (newvar, H); intuition (subst_max)
    end.

  Lemma skipn_app : forall T (a b : list T),
    skipn (length a) (a ++ b) = b.
  Proof.
    induction a; firstorder.
  Qed.

  Lemma firstn_all: forall A (l : list A) n,
    length l <= n -> firstn n l = l.
  Proof.
    unfold firstn; induction l; destruct n; intros; firstorder.
    rewrite IHl; firstorder.
  Qed.

  Lemma skipn_all: forall T n (l : list T),
    length l <= n -> skipn n l = nil.
  Proof.
    unfold skipn; induction n; destruct l; intros; auto.
    inversion H.
    apply IHn; firstorder.
  Qed.


  Lemma cons_nil_app : forall A l r (a : A),
    (l ++ (a :: nil)) ++ r = l ++ a :: r.
  Proof.
    intros.
    rewrite app_assoc_reverse.
    simpl; auto.
  Qed.

  Hint Resolve cons_nil_app.

  Lemma firstn_app : forall T n (a b: list T),
    firstn n (a ++ b) = firstn n a ++ firstn (n - length a) b.
  Proof.
    induction n; intuition.
    destruct a; cbn; [ | rewrite IHn ]; reflexivity.
  Qed.

  (* from coq-ext-lib *)
  Lemma firstn_app_R : forall T n (a b : list T),
    length a <= n ->
    firstn n (a ++ b) = a ++ firstn (n - length a) b.
  Proof.
    induction n; destruct a; simpl in *; intros; auto.
    exfalso; omega.
    f_equal. eapply IHn; eauto. omega.
  Qed.

  Lemma firstn_app_r : forall T i (b a : list T),
    firstn (length a + i) (a ++ b) = a ++ (firstn i b).
  Proof.
    intros. rewrite firstn_app_R.
    f_equal. f_equal. omega.
    omega.
  Qed.


  Lemma firstn_app_L : forall T n (a b : list T),
    n <= length a ->
    firstn n (a ++ b) = firstn n a.
  Proof.
    induction n; destruct a; simpl in *; intros; auto.
    exfalso; omega.
    f_equal. eapply IHn; eauto. omega.
  Qed.

  Lemma skipn_app_R : forall T n (a b : list T),
    length a <= n ->
    skipn n (a ++ b) = skipn (n - length a) b.
  Proof.
    induction n; destruct a; simpl in *; intros; auto.
    exfalso; omega.
    eapply IHn. omega.
  Qed.

  Lemma skipn_app_r : forall T i (b a : list T),
    skipn (length a + i) (a ++ b) = skipn i b.
  Proof.
    intros. rewrite skipn_app_R.
    f_equal. f_equal. omega.
    omega.
  Qed.

  Lemma skipn_app_L : forall T n (a b : list T),
    n <= length a ->
    skipn n (a ++ b) = (skipn n a) ++ b.
  Proof.
    induction n; destruct a; simpl in *; intros; auto.
    exfalso; omega.
    eapply IHn. omega.
  Qed.

  Lemma skipn_length: forall A n (l : list A),
    n <= length l
    -> length (skipn n l) = length l - n.
  Proof.
    induction n; destruct l; intros; firstorder.
  Qed.

  Lemma skipn_skipn : forall T a (ls : list T) b,
    skipn b (skipn a ls) = skipn (b + a) ls.
  Proof.
    induction a; simpl; intros.
    rewrite Plus.plus_0_r. auto.
    rewrite Plus.plus_comm. simpl. destruct ls; auto. destruct b; auto.
    rewrite IHa. rewrite Plus.plus_comm. auto.
  Qed.

  Definition concat A (l: list (list A)) : list A := fold_right (@app A) [] l.

  Definition repeat_list A n (l: list A) : list A := concat (repeat l n).

  Lemma repeat_list_app : forall A n m (l: list A),
    repeat_list n l ++ repeat_list m l = repeat_list (n + m) l.
  Proof.
    unfold repeat_list.
    induction n; crush.
  Qed.

  Lemma repeat_list_chop_last : forall A n (l: list A),
    0 < n -> repeat_list n l = repeat_list (n - 1) l ++ l.
  Proof.
    intros.
    remember (n - 1) as m.
    replace n with (S m) in * by omega.
    clear n Heqm.
    unfold repeat_list.
    clear H.
    induction m. simpl. apply app_nil_r.
    simpl in *. rewrite IHm. rewrite app_assoc. rewrite IHm. reflexivity.
  Qed.

  Lemma repeat_list_tail: forall A n (l: list A),
    0 < n -> repeat_list n l = l ++ repeat_list (n - 1) l.
  Proof.
    unfold repeat_list.
    intros.
    remember (n - 1) as m.
    replace n with (S m) in * by omega.
    reflexivity.
  Qed.

  Lemma repeat_repeat : forall A n m (l: list A),
    repeat_list n (repeat_list m l) = repeat_list (n * m) l.
  Proof.
    induction n; intuition.
    simpl. rewrite <- repeat_list_app.
    cbn. f_equal. apply IHn.
  Qed.

  Inductive suffix A : list A -> list A -> Prop :=
  | suf_refl : forall l, suffix l l
  | suf_cons : forall c l' l, suffix l' l -> suffix l' (c::l).
  Hint Constructors suffix.

  Inductive prefix A : list A -> list A -> Prop :=
  | pre_nil : forall l, prefix [] l
  | pre_cons : forall c l' l, prefix l' l -> prefix (c::l') (c::l).
  Hint Constructors prefix.

  Lemma suffix_app: forall A (l l': list A), suffix l (l' ++ l).
  Proof.
    induction l'; crush.
  Qed.
  Hint Resolve suffix_app.

  Lemma suffix_defn: forall A (l l2: list A),
    suffix l2 l <-> exists l', l = l' ++ l2.
  Proof.
    intuition.
    + induction H. eexists. instantiate (1 := nil). reflexivity.
      destruct IHsuffix. eexists.
      rewrite H0. rewrite app_comm_cons. reflexivity.
    + destruct H. crush.
  Qed.
  Hint Resolve suffix_defn.

  Lemma prefix_app: forall A (l l': list A), prefix l (l ++ l').
  Proof.
    induction l; crush.
  Qed.
  Hint Resolve prefix_app.

  Lemma prefix_defn: forall A (l l': list A),
    prefix l' l <-> exists l'', l = l' ++ l''.
  Proof.
    intuition.
    + induction H. eexists. reflexivity.
      destruct IHprefix. eexists.
      rewrite H0. reflexivity.
    + destruct H. crush.
  Qed.
  Hint Resolve prefix_defn.

  Instance prefix_trans {A}: Transitive (@prefix A).
  Proof.
    unfold Transitive.
    intros.
    apply prefix_defn. apply prefix_defn in H. apply prefix_defn in H0.
    repeat deex. eexists. rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma skipn_suffix: forall A n (l: list A), suffix (skipn n l) l.
  Proof.
    induction n; crush.
    destruct l; crush.
  Qed.

  Lemma firstn_prefix: forall A n (l: list A), prefix (firstn n l) l.
  Proof.
    induction n; crush.
    destruct l; crush.
  Qed.


  Inductive sublist A : list A -> list A -> Prop :=
  | subl_prefix : forall l' l, prefix l' l -> sublist l' l
  | subl_cons : forall c l' l, sublist l' l -> sublist l' (c::l).
  Hint Constructors sublist.

  Lemma sublist_app : forall A (l l' l'': list A), sublist l (l' ++ l ++ l'').
  Proof.
    induction l'; crush.
  Qed.
  Hint Resolve sublist_app.

  Lemma sublist_defn : forall A (l l': list A),
    sublist l' l <-> exists l2 l3, l = l2 ++ l' ++ l3.
  Proof.
    intuition.
    + induction H.
      apply prefix_defn in H.
      deex. repeat eexists. rewrite app_nil_l. reflexivity.
      repeat deex. repeat eexists. rewrite app_comm_cons. reflexivity.
    + repeat deex. auto.
  Qed.
  Hint Resolve sublist_defn.

  Instance sublist_trans {A}: Transitive (@sublist A).
  Proof.
    unfold Transitive.
    intros.
    apply sublist_defn. apply sublist_defn in H. apply sublist_defn in H0.
    repeat deex. repeat eexists. do 2 rewrite <- app_assoc. rewrite app_assoc. reflexivity.
  Qed.

  Inductive divides A : list A -> list A -> Prop :=
  | div_0 : forall l, divides l []
  | div_cons : forall l' l, divides l' l -> divides l' (l' ++ l).
  Hint Constructors divides.

  Notation "( x | y )" := (divides x y) (at level 0).

  Lemma divides_id : forall A (l: list A), (l | l).
  Proof.
    intros.
    replace l with (l ++ []) at 2 by (apply app_nil_r).
    auto.
  Qed.
  Hint Resolve divides_id.


  Inductive repetition A : list A -> list A -> Prop :=
  | rep_2 : forall l, repetition l (l ++ l)
  | rep_cons : forall l' l, repetition l' l -> repetition l' (l' ++ l).
  Hint Constructors repetition.

  Inductive repeating A : list A -> Prop :=
  | rep : forall l' l, repetition l' l -> repeating l.
  Hint Constructors repeating.

  Lemma repeating_repeat_list: forall A n (l: list A), n > 1 -> repeating (repeat_list n l).
  Proof.
    econstructor. instantiate (l' := l).
    revert H.
    induction n; crush.
    unfold repeat_list. simpl.
    inversion H. simpl. autorewrite with core.
    econstructor. constructor.
    crush.
  Qed.
  Hint Resolve repeating_repeat_list.

  Lemma repeating_defn : forall A (l: list A),
    repeating l <-> exists l' n, 1 < n /\ l = repeat_list n l'.
  Proof.
    intuition.
    - destruct H.
      exists l'.
      induction H.
      + repeat eexists. instantiate (n := 2). omega.
        unfold repeat_list.
        simpl. autorewrite with core. reflexivity.
      + repeat deex.
        exists (1 + n). crush.
    - repeat deex. auto.
  Qed.

  Lemma divides_defn : forall A (l l': list A),
    divides l' l <-> exists n, l = repeat_list n l'.
  Proof.
    intuition.
    + induction H.
      - exists 0; cbn; intuition.
      - deex.
        exists (S n).
        intuition.
    + deex. induction n.
      - constructor.
      - cbn. constructor. apply IHn.
  Qed.

  Instance divides_trans {A}: Transitive (@divides A).
  Proof.
    unfold Transitive.
    intros.
    apply divides_defn. apply divides_defn in H. apply divides_defn in H0.
    repeat deex. exists (n * n0).
    apply repeat_repeat.
  Qed.

  Fixpoint chop_last A (l: list A) :=
    match l with
    | [] => []
    | [x] => []
    | x :: xs => x :: chop_last xs
    end.

  Lemma chop_last_last: forall A l (c: A),
    chop_last (l ++ [c]) = l.
  Proof.
    induction l.
    auto.
    intros; simpl. rewrite IHl.
    remember (l ++ [c]) as lc.
    destruct lc. induction l; discriminate. trivial.
  Qed.
  Hint Resolve chop_last_last.

  Lemma chop_last_parts: forall A (l l': list A),
    0 < length l -> chop_last l = l' <-> exists c, l = l' ++ [c].
  Proof.
    intuition.
    + subst.
      induction l. crush.
      destruct l. eexists. crush.
      destruct IHl. simpl. omega.
      eexists. rewrite H0 at 1. reflexivity.
    + deex. crush.
  Qed.

  Lemma tl_parts: forall A (l l': list A),
    0 < length l -> tl l = l' <-> exists c, l = c :: l'.
  Proof.
    intuition.
    + subst.
      induction l. crush.
      destruct l. eexists. crush.
      destruct IHl. simpl. omega.
      eexists. rewrite H0 at 1. crush.
    + deex. crush.
  Qed.

  Lemma tail_app: forall A (l l': list A),
    length l > 0 -> tail (l ++ l') = tail l ++ l'.
  Proof.
    intros.
    destruct l; intuition.
    cbn in *. omega.
  Qed.

  Lemma chop_last_app: forall A (l l': list A),
    0 < length l' -> chop_last (l ++ l') = l ++ chop_last l'.
  Proof.
    induction l; intuition.
    destruct l'. cbn in *. omega.
    induction l; crush.
  Qed.

  Lemma length_tl: forall A (l: list A), length (tl l) = length l - 1.
  Proof.
    induction l; crush.
  Qed.
  Hint Rewrite length_tl.

  Lemma length_chop_last: forall A (l: list A), length (chop_last l) = length l - 1.
    induction l; crush.
    destruct l; crush.
  Qed.
  Hint Rewrite length_chop_last.

  Lemma length_repeat : forall A n (l: list A),
    length (repeat_list n l) = n * length l.
  Proof.
    induction n; intuition.
    unfold repeat_list in *. simpl. rewrite app_length.
    rewrite IHn. omega.
  Qed.
  Hint Rewrite length_repeat.

  Lemma length_repeating : forall A (l: list A),
    repeating l -> length l = 0 \/ 2 <= length l.
  Proof.
    intros.
    apply repeating_defn in H.
    destruct l; intuition.
    right. repeat deex. rewrite H1.
    rewrite length_repeat.
    destruct l'.
    assert (length (@repeat_list A n []) = 0).
    rewrite length_repeat. auto.
    destruct (repeat_list n []); discriminate.
    simpl. rewrite Nat.mul_succ_r. rewrite plus_comm. remember (n + n * length l') as tl.
    destruct tl. destruct n; intuition.
    etransitivity. instantiate (1 := n). omega. apply le_plus_l.
  Qed.

  Lemma repeat_list_prefix: forall A (l: list A) n m,
    n <= m -> prefix (repeat_list n l) (repeat_list m l).
  Proof.
    intros.
    replace m with (n + (m - n)) by omega.
    remember (m - n) as m'.
    clear m H Heqm'.
    induction n. constructor.
    unfold repeat_list in *; simpl.
    apply prefix_defn. apply prefix_defn in IHn.
    repeat deex. eexists. crush.
  Qed.
  Hint Resolve repeat_list_prefix.

  Lemma equal_length_prefix: forall A (l' l: list A),
    length l = length l' -> prefix l' l -> l' = l.
  Proof.
    induction l'; destruct l; crush.
    inversion H0. subst.
    erewrite IHl'; eauto.
  Qed.

  Lemma firstn_app_r': forall A n (l l': list A),
    length l <= n -> firstn n (l ++ l') = l ++ firstn (n - length l) l'.
  Proof.
    intros.
    replace n with (length l + (n - length l)) by omega.
    rewrite firstn_app_r.
    f_equal. f_equal. omega.
  Qed.


  Lemma firstn_firstn : forall A (l:list A) n1 n2, firstn n1 (firstn n2 l) = firstn (Nat.min n1 n2) l.
  Proof.
    induction l.
    + intros.
      destruct n1; destruct n2; reflexivity.
    + intros.
      destruct n1.
      * simpl. reflexivity.
      * destruct n2.
        simpl.
        reflexivity.
        simpl.
        rewrite IHl.
        reflexivity.
  Qed.

  Lemma divides_repeat_list : forall A n (l: list A),
    divides l (repeat_list n l).
  Proof.
    induction n.
    - constructor.
    - cbn. constructor. apply IHn.
  Qed.

  Lemma divides_app : forall A (l' l1 l2: list A),
    divides l' l1 -> divides l' l2 -> divides l' (l1 ++ l2).
  Proof.
    intros.
    induction H; intuition.
    rewrite <- app_assoc. constructor. auto.
  Qed.

  Lemma divides_subtract : forall A (l' l1 l2: list A),
    divides l' l1 -> divides l' (l1 ++ l2) -> divides l' l2.
  Proof.
    intros.
    induction H; intuition.
    apply IHdivides.
    inversion H0.
    destruct l', l, l2; try discriminate. auto.
    subst.
    rewrite <- app_assoc in *.
    find_apply_lem_hyp app_inv_head.
    subst.
    auto.
  Qed.

  Lemma divides_repeating: forall A (l: list A),
    (exists l', divides l' l /\ length l' < length l) -> repeating l.
  Proof.
    intuition.
    deex.
    apply repeating_defn.
    find_apply_lem_hyp divides_defn.
    deex.
    exists l'. exists n.
    split; auto.
    destruct n.
    cbn in H1. omega.
    destruct n.
    cbn in H1. rewrite app_nil_r in H1. omega.
    omega.
  Qed.

  Theorem strong_induction: forall P : nat -> Prop,
    (forall n, (forall k, (k < n -> P k)) -> P n) ->
    forall n, P n.
  Proof.
    intros.
    apply H.
    induction n; intros.
    + solve_by_inversion.
    + destruct (lt_dec k n); auto.
      replace k with n by omega.
      auto.
  Qed.

  Ltac lengths :=
    repeat rewrite skipn_length by lengths;
    repeat rewrite firstn_length by lengths;
    repeat rewrite app_length;
    repeat rewrite Nat.min_id;
    repeat rewrite Nat.min_l by lengths;
    repeat rewrite Nat.min_r by lengths;
    omega.

  Lemma rot_eq_repeating: forall A (a b: list A),
    0 < length a -> 0 < length b -> a ++ b = b ++ a -> repeating (a ++ b).
  Proof.
    intros. apply divides_repeating.
    remember (length a + length b) as n.
    remember (length b) as m.
    assert (exists l', (l' | (a ++ b)) /\ (l' | b) /\ length l' < length (a ++ b)).
    revert a b Heqn H H0 H1 Heqm.
    generalize dependent m.
    induction n using strong_induction.
    induction m using strong_induction.
    intuition.
    destruct (Nat.eq_dec (length a) (length b)).
    2: destruct (lt_dec (length b) (length a)).
    + apply (f_equal (firstn (length a))) in H3.
      do 2 rewrite firstn_app_L in * by lengths.
      rewrite firstn_all in * by lengths.
      rewrite e in *.
      rewrite firstn_all in * by lengths.
      exists a. subst. intuition.
      lengths.
    + rename H3 into Heq.
      generalize Heq; intro Heq2.
      apply (f_equal (skipn (length b))) in Heq.
      do 2 rewrite skipn_app_L in Heq by lengths.
      rewrite skipn_all with (l := b) in Heq by lengths.
      cbn in Heq.
      apply (f_equal (firstn (length b))) in Heq2.
      do 2 rewrite firstn_app_L in Heq2 by lengths.
      rewrite firstn_all with (l := b) in Heq2 by lengths.

      edestruct H with (m := length b) (b := b) (a := skipn (length b) a); trivial; try rewrite skipn_length; try lengths.
      rewrite Heq. rewrite <- Heq2 at 1. rewrite firstn_skipn. reflexivity.

      exists x.
      intuition.
      apply divides_app; auto.
      congruence.
      rewrite app_length in H6.
      rewrite skipn_length in H6 by lengths.
      lengths.
    + rename H3 into Heq.
      edestruct H0 with (b := a) (a := b); trivial; try lengths.
      congruence.

      exists x.
      intuition.
      rewrite Heq; auto.
      eapply divides_subtract; eauto.
      rewrite Heq; auto.
      rewrite Heq; auto.
    + deex. exists l'. intuition.
  Qed.
  Hint Resolve rot_eq_repeating.

  Theorem repeating_in_self : forall A (l: list A),
    repeating l <-> sublist l (chop_last (tail (l ++ l))).
  Proof.
    intuition.
    + destruct (length_repeating H). destruct l; crush.
      apply repeating_defn in H. repeat deex.
      rewrite repeat_list_app.
      remember (repeat_list n l') as rl.
      rewrite repeat_list_tail by omega.
      destruct l'. subst. rewrite length_repeat in *. rewrite Nat.mul_0_r in H0. omega.
      rewrite tail_app by (simpl; omega).
      rewrite chop_last_app.
      rewrite repeat_list_chop_last by omega.
      rewrite chop_last_app by (simpl; omega).
      etransitivity; [ | apply sublist_defn; repeat eexists ].
      constructor. crush.
      autorewrite with core. simpl.
      remember (n + n - 1) as fa.
      destruct fa; crush.
    + destruct l. econstructor. replace (@nil A) with (@repeat_list A 2 []) by auto. constructor.
      apply sublist_defn in H.
      repeat deex.
      apply chop_last_parts in H. deex.
      2: destruct l; simpl; omega.
      apply tl_parts in H. deex.
      2: destruct l; simpl; omega.
      repeat rewrite app_comm_cons in H.
      remember (c0 :: l2) as l'.
      rename l into ltail.
      remember (a :: ltail) as l.
      assert (0 < length l' < length l). {
        generalize (f_equal (@length A) H).
        autorewrite with core. repeat rewrite app_length. simpl. intros.
        assert (length l > 0) by (destruct l; cbn in *; omega).
        split; subst; simpl in *; omega.
      }
      generalize (f_equal (@skipn A (length l')) H).
      repeat rewrite <- app_assoc.
      rewrite skipn_app. rewrite skipn_app_L by omega.
      intro Hs.
      generalize (f_equal (@firstn A (length l)) Hs).
      rewrite firstn_app with (a := l) by auto.
      rewrite firstn_app_r' by (repeat rewrite skipn_length by omega; omega).
      repeat rewrite skipn_length by omega. replace (length l - (length l - length l')) with (length l') by omega.
      replace (length l - length l) with 0 by omega. rewrite firstn_all with (n := length l) by auto. rewrite app_nil_r.
      intros. rewrite <- H1. eapply rot_eq_repeating; eauto.
      lengths.
      lengths.
      rewrite firstn_skipn. auto.
  Qed.