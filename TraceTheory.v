Require Import List Bool Classical_Prop.

Require Import CpdtTactics Facts.

Section EventTraces.

  Parameter process : Set.
  Axiom eq_proc_dec : forall (x y : process), {x = y} + {x <> y}.

  Definition event := prod process nat.

  Definition proc_of (e : event) : process := fst e.

  Fixpoint next_index w p :=
    match w with
      | nil => 0
      | (q, i) :: t => if eq_proc_dec p q then S i else next_index t p
    end.

  Definition exec_event (w : list event) (p : process) : list event :=
    ((p, next_index w p) :: w).

  Inductive is_event_seq : list event -> Prop :=
  | is_event_empty : is_event_seq nil
  | is_event_step :
      forall w p, is_event_seq w -> is_event_seq (exec_event w p).

  Lemma pred_in_event_seq_help:
    forall w p i, next_index w p = S i -> In (p, i) w.
  Proof.
    intros; induction w.
    - crush.
    - crush; destruct a; case eq_proc_dec in *; crush.
  Qed.

  Lemma pred_in_event_seq:
    forall p i w, is_event_seq w -> In (p, S i) w -> In (p, i) w.
  Proof.
    intros; induction w.
    - crush.
    - inversion H; crush; apply pred_in_event_seq_help in H1; crush.
  Qed.

  Lemma all_preds_in_event_seq:
    forall p i j w, is_event_seq w -> In (p, i) w -> j < i -> In (p, j) w.
  Proof.
    intros; induction H1;
    match goal with
      | [ H : is_event_seq ?W, H1 : In (?P, S ?J) ?W |- _ ] =>
        apply pred_in_event_seq with (p := P) (i := J) in H; crush
    end.
  Qed.

  Definition next_maybe E p := head (exec_event E p).
  Definition next E p := (p, next_index E p).

  Lemma is_event_seq_cons:
    forall a l,
      is_event_seq (a :: l) -> is_event_seq l /\ a = next l (proc_of a).
  Proof.
    intros ? ? H; inversion H; crush.
  Qed.

  Lemma is_event_seq_app:
    forall E w, is_event_seq (E +++ w) -> is_event_seq E.
  Proof.
    intros; induction w.
    - crush.
    - inversion H; crush.
  Qed.

  Lemma next_greater:
    forall p E i, is_event_seq E -> In (p, i) E -> next_index E p > i.
  Proof.
    intros; induction E.
    - crush.
    - apply in_inv in H0; inversion H; crush; case eq_proc_dec; crush.
  Qed.

  Lemma next_not_less:
    forall p a E,
      is_event_seq (a :: E) -> next_index (a :: E) p >= next_index E p.
  Proof.
    intros; destruct a; simpl; inversion H; case eq_proc_dec; crush.
  Qed.

  Lemma not_less_app:
    forall p w E,
      is_event_seq (w ++ E) -> next_index E p <= next_index (w ++ E) p.
  Proof.
    intros; induction w.
    - crush.
    - rewrite <- app_comm_cons in H.
      pose proof H as H'.
      apply is_event_seq_cons in H'.
      apply next_not_less with (p := p) in H.
      crush.
  Qed.

  Lemma diff_q_same_index:
    forall E p q,
      is_event_seq (exec_event E q) ->
      p <> q ->
      next_index E p = next_index (exec_event E q) p.
  Proof.
    crush; destruct eq_proc_dec; crush.
  Qed.

  Lemma events_unique_help:
    forall E w p i,
      is_event_seq (E +++ w) -> In (p, i) w -> forall j, In (p, j) E -> j < i.
  Proof.
    intros; in_splitter;
    rewrite <- app_assoc in H; apply is_event_seq_app in H; inversion H;
    crush; apply next_greater with (p := p) (i := j) in H3; crush.
  Qed.

  Theorem events_unique:
    forall E e w, is_event_seq (E +++ w) -> In e w -> ~ In e E.
  Proof.
    intros; destruct e; crush;
    apply events_unique_help with (p := p) (i := n) (j := n) in H; crush.
  Qed.

  Theorem events_unique_neq:
    forall E w e e', is_event_seq (E +++ w) -> In e w -> In e' E -> e <> e'.
  Proof.
    intros; contradict H1; pose proof (events_unique E e' w); crush.
  Qed.

  Definition in_seq (p : process) w := exists (i : nat), In (p, i) w.

  Lemma not_in_seq_cons:
    forall p a w,  ~ in_seq p (a :: w) -> (~ proc_of a = p) /\ (~ in_seq p w).
  Proof.
    unfold in_seq; crush; contradiction H;
    match goal with
      | i : nat |- _ => exists i; crush
    end.
  Qed.

  Lemma not_in_seq_same_index:
    forall E p w,
      is_event_seq (E +++ w) -> ~ in_seq p w ->
      next_index E p = next_index (E +++ w) p.
  Proof.
    intros; induction w.
    - crush.
    - rewrite <- app_comm_cons in *; apply is_event_seq_cons in H;
      destruct H, a; unfold next in H1; apply not_in_seq_cons in H0; crush;
      case eq_proc_dec; crush.
  Qed.

End EventTraces.

Notation "E ** p" :=
  (exec_event E p) (at level 58, left associativity, only parsing).

Section States.

  Parameter state : Set.
  Axiom eq_state_dec : forall (x y : process), {x = y} + {x <> y}.

  Parameter s0 : state.
  Parameter execute : state -> process -> option state.

  Definition blocked s p := execute s p = None.
  Definition enabled s p := ~ blocked s p.
  Definition maximal s := forall p, blocked s p.

  Inductive reachable: state -> Prop :=
  | is_initial : reachable s0
  | is_next :
      forall s s' p, reachable s' -> execute s' p = Some s -> reachable s.

  Axiom states_are_reachable : forall s, reachable s.
  Axiom s0_is_initial: forall p, ~ exists s, execute s p = Some s0.

  Ltac enabled_as_option s p:=
    unfold enabled, blocked; intros s p; generalize (execute s p).

  Theorem enabled_has_next:
    forall s p, enabled s p -> exists s', execute s p = Some s'.
  Proof.
    enabled_as_option s p; induction o.
    - exists a; reflexivity.
    - crush.
  Qed.

  Theorem enabled_dec:
    forall s p, enabled s p + blocked s p.
  Proof.
    enabled_as_option s p; induction o.
    - left; unfold not; intro H; inversion H.
    - right; reflexivity.
  Qed.

  Fixpoint state_after_maybe (l : list event) : option state :=
    match l with
      | nil => Some s0
      | (p, _) :: w =>
        match state_after_maybe w with
          | None => None
          | Some s => execute s p
        end
    end.

  Definition enabled_after E p :=
    match state_after_maybe E with
      | None => False
      | Some s => enabled s p
    end.

  Theorem enabled_after_has_state_rev:
    forall E p s,
      state_after_maybe E = Some s -> enabled s p -> enabled_after E p.
  Proof.
    intros; red; rewrite -> H; crush.
  Qed.

  Theorem enabled_after_has_state:
    forall E p,
      enabled_after E p ->
      exists s, state_after_maybe E = Some s /\ enabled s p.
  Proof.
    unfold enabled_after; intro E; generalize dependent (state_after_maybe E);
    destruct o; crush; exists s; crush.
  Qed.

End States.

Section ExSeqs.

  Inductive is_ex_seq: list event -> Prop :=
  | is_ex_empty : is_ex_seq nil
  | is_ex_step :
      forall E p,
        is_ex_seq E -> enabled_after E p -> is_ex_seq (exec_event E p).

  Theorem ex_seq_is_event_seq: forall E, is_ex_seq E -> is_event_seq E.
  Proof.
    intros E H; induction H.
    - exact is_event_empty.
    - apply is_event_step with E p in IHis_ex_seq; assumption.
  Qed.

  Definition valid E := exists s, state_after_maybe E = Some s.

  Theorem valid_ex_seq:
    forall E, is_ex_seq E -> valid E.
  Proof.
    intros ? H; induction H.
    - exists s0; crush.
    - destruct IHis_ex_seq; unfold enabled_after in H0; rewrite H1 in H0;
      apply enabled_has_next in H0; destruct H0;
      exists x0; crush.
  Qed.

  Lemma is_ex_seq_cons:
    forall a w,
      is_ex_seq (a :: w) <->
      is_ex_seq w /\ enabled_after w (proc_of a) /\
      (proc_of a, next_index w (proc_of a)) = a.
  Proof.
    split.
    - intros; inversion H; crush.
    - intros; destruct H; destruct H0; pose proof (is_ex_step w (proc_of a));
      apply H2 in H.
      + unfold exec_event in H; rewrite H1 in H; assumption.
      + assumption.
  Qed.

  Lemma is_ex_seq_app:
    forall E w, is_ex_seq (E +++ w) -> is_ex_seq E.
  Proof.
    intros; induction w; crush.
    apply is_ex_seq_cons in H; crush.
  Qed.

  Lemma ex_seq_none:
    forall E, is_ex_seq E -> state_after_maybe E <> None.
  Proof.
    intros; apply valid_ex_seq in H; unfold valid in H; crush.
  Qed.

  Definition state_after E : is_ex_seq E -> state.
    intros; apply ex_seq_none in H; apply just in H; exact H.
  Defined.

  Theorem state_has_ex_seq:
    forall s, exists E, state_after_maybe E = Some s.
  Proof.
    intros; pose proof states_are_reachable s as H; induction H.
    - exists nil; crush.
    - crush; exists (exec_event x p); crush.
  Qed.

  Definition ex_seq := {E | is_ex_seq E}.

End ExSeqs.

Section Dep.

  Parameter dependent : list event -> event -> event -> bool.

  Definition is_after_in (E : list event) a b :=
    exists l1 l2 l3, E = l1 +++ [a] +++ l2 +++ [b] +++ l3.

  Lemma heads_after:
    forall E a b c,
      In c E ->
      is_after_in (a :: E) c a /\
      is_after_in (a :: b :: E) c b.
  Proof.
    intros; in_splitter; unfold is_after_in; crush.
    - exists x0, x, nil; crush.
    - exists x0, x, ([a]); crush.
  Qed.

  Lemma both_orders_dup:
    forall E a b,
      is_after_in E a b -> is_after_in E b a -> a <> b ->
      exists A B c, E = A ++ B /\ In c A /\ In c B.
  Proof.
    unfold is_after_in; intros; destruct_exs.
    pose proof (not_appears_after_dec _ a b E); destruct H2; crush.
    - rewrite <- H0; crush.
    - apply not_appears_after_split in H2; crush.
      exists x4, ([b] ++ x3 ++ [a] ++ x2), a; crush.
    - rewrite H0 in H2.
      apply not_appears_after_split in H2; crush.
      exists x1, ([a] ++ x0 ++ [b] ++ x), b; crush.
  Qed.

  Lemma is_after_cons:
    forall e a b l,
      is_after_in (e :: l) a b -> is_after_in l a b \/ e = b /\ In a l.
  Proof.
    intros; unfold is_after_in in H; crush; destruct x1.
    - crush.
    - assert (forall l', e :: l = e0 :: l' -> e = e0 /\ l = l').
      + crush.
      + rewrite <- app_comm_cons in H; apply H0 in H; destruct H.
        left; unfold is_after_in; exists x, x0, x1; crush.
  Qed.

  Lemma is_after_cases:
    forall l1 l2 a b,
      is_after_in (l1 ++ l2) a b ->
      is_after_in l1 a b \/
      (In b l1 /\ In a l2) \/
      is_after_in l2 a b.
  Proof.
    intros; induction l1.
    - unfold is_after_in in H; crush.
    - rewrite <- app_comm_cons in H; apply is_after_cons in H; destruct H.
      + apply IHl1 in H; destruct H; crush.
        left; unfold is_after_in in *.
        destruct_exs; rewrite H; exists x, x0, (a0::x1); crush.
      + destruct H; apply in_app_iff in H0; destruct H0; crush.
        left; unfold is_after_in; in_splitter; exists x0, x, nil; crush.
  Qed.

  Axiom dep_is_total:
    forall E a b, Is_true (dependent E a b) -> is_after_in E a b.

  Lemma dep_is_in:
    forall E a b, Is_true (dependent E a b) -> In a E /\ In b E.
  Proof.
    intros; apply dep_is_total with (a := a) (b := b) in H;
    unfold is_after_in in *; crush; apply in_or_app; crush.
  Qed.

  Theorem dep_not_refl:
    forall E a, is_ex_seq E -> ~ Is_true (dependent E a a).
  Proof.
    crush; apply dep_is_total in H0; apply ex_seq_is_event_seq in H;
    unfold is_after_in in H0; crush;
    pose proof (events_unique (a :: x) a (x1 ++ a :: x0)); crush.
  Qed.

  Theorem before_not_dep:
    forall E a b,
      is_ex_seq E -> is_after_in E a b -> ~ Is_true (dependent E b a).
  Proof.
    crush.
    apply ex_seq_is_event_seq in H.
    apply dep_is_total in H1; pose proof (both_orders_dup E a b); crush.
    unfold is_after_in in H0; crush.
    pose proof (events_unique_neq (a :: x) (x1 ++ b :: x0) b a).
    destruct H2; crush.
    rewrite H3 in H.
    apply events_unique with (e:=x4) in H; crush.
  Qed.

  Theorem dep_not_before:
    forall E a b,
      is_ex_seq E -> Is_true (dependent E a b) -> ~ is_after_in E b a.
  Proof.
    crush; apply before_not_dep with (a:=b) (b:=a) in H; crush.
  Qed.

  Axiom dep_transitive:
    forall E a b c,
      Is_true (dependent E a b) -> Is_true (dependent E b c) ->
      Is_true (dependent E a c).

  Axiom dep_prefix:
    forall E E' a b,
      In a E -> In b E -> (rev_prefix _ E E') ->
      (Is_true (dependent E' a b) <-> Is_true (dependent E a b)).

  Axiom dep_same_proc_consec:
    forall E p i,
      is_ex_seq E -> In (p, S i) E -> Is_true (dependent E (p, i) (p, S i)).

  Theorem dep_same_proc:
    forall E p i,
      is_ex_seq E -> In (p, i) E ->
      forall j, j < i -> Is_true (dependent E (p, j) (p, i)).
  Proof.
    intros; induction H1.
    - apply dep_same_proc_consec; crush.
    - apply dep_same_proc_consec in H0.
      + pose proof H0 as H0'; apply dep_is_in in H0'; crush;
        apply dep_transitive with (b := (p, m)); crush.
      + crush.
  Qed.

  Definition have_same_events E E' :=
    forall (a : event), In a E <-> In a E'.

  Definition keeps_dep_order E E' :=
    forall a b,
      Is_true (dependent E a b) -> In a E' -> In b E' -> is_after_in E' a b.

  Axiom linearization_is_ex_seq:
    forall E E', is_ex_seq E -> keeps_dep_order E E' -> is_ex_seq E'.

  Lemma solve_dep_prefix:
    forall E a b a0 b0,
      is_ex_seq (a :: b :: E) ->
      In a0 E ->
      In b0 E ->
      Is_true (dependent (a :: b :: E) a0 b0) ->
      is_after_in (b :: a :: E) a0 b0.
  Proof.
    intros; apply dep_is_total.
    assert (rev_prefix _ E (a :: b :: E)).
    - unfold rev_prefix; exists (a :: b :: nil); crush.
    - assert (rev_prefix _ E (b :: a :: E)).
      + unfold rev_prefix; exists (b :: a :: nil); crush.
      + pose proof (dep_prefix E (a :: b :: E) a0 b0); crush.
        pose proof (dep_prefix E (b :: a :: E) a0 b0); crush.
  Qed.

  Ltac dep_works :=
    match goal with
      | H: Is_true (dependent _ ?A ?A) |- _ =>
        contradict H; intros; apply dep_not_refl; crush
      | H: Is_true (dependent (_ :: ?A :: _) ?A _) |- _ =>
        contradict H; apply before_not_dep; crush
      | H: Is_true (dependent (?A :: _ :: _) ?A _) |- _ =>
        contradict H; apply before_not_dep; crush
      | H: Is_true (dependent (?A :: _ ++ _) ?A _) |- _ =>
        contradict H; apply before_not_dep; crush
      | _ : _ |- _ => idtac
    end;
    match goal with
      | _ : _ |- is_after_in (?A :: ?B :: ?C) ?B ?A =>
        unfold is_after_in; exists C, nil, nil; crush
      | _ : _ |- is_after_in (_ :: ?A :: ?E) ?B ?A =>
        apply heads_after; crush
      | _ : _ |- is_after_in (?A :: _) _ ?A =>
        apply heads_after; crush
      | _ : _ |- _ => apply solve_dep_prefix; crush
    end.

  Theorem indep_flip_is_ex_seq:
    forall E a b,
      is_ex_seq (E +++ [a] +++ [b]) ->
      ~ Is_true (dependent (E +++ [a] +++ [b]) a b) ->
      is_ex_seq (E +++ [b] +++ [a]).
  Proof.
    crush.
    apply linearization_is_ex_seq with (E := (E +++ [a] +++ [b])); crush.
    unfold keeps_dep_order; crush; dep_works.
  Qed.

  Definition hb_equiv E E' :=
    have_same_events E E' /\ keeps_dep_order E E'.

  Lemma hb_equiv_is_ex_seq:
    forall E E',
      is_ex_seq E -> hb_equiv E E' -> is_ex_seq E'.
  Proof.
    unfold hb_equiv; intros;
    apply linearization_is_ex_seq with (E := E); crush.
  Qed.

  Theorem independent_step_hb_equiv:
    forall E a b,
      is_ex_seq (E +++ [a] +++ [b]) ->
      ~ Is_true (dependent (E +++ [a] +++ [b]) a b) ->
      hb_equiv (E +++ [a] +++ [b]) (E +++ [b] +++ [a]).
  Proof.
    unfold hb_equiv; crush.
    - unfold have_same_events; crush.
    - unfold keeps_dep_order; crush; dep_works.
  Qed.

  Axiom hb_equiv_same_dep:
    forall E E', hb_equiv E E' -> dependent E = dependent E'.

  Lemma hb_equiv_reflexive:
    forall E, hb_equiv E E.
  Proof.
    unfold hb_equiv, have_same_events, keeps_dep_order; crush.
    apply dep_is_total; crush.
  Qed.

  Lemma hb_equiv_symmetric:
    forall E E',
      hb_equiv E E' -> hb_equiv E' E.
  Proof.
    intros; unfold hb_equiv, have_same_events, keeps_dep_order.
    split.
    - unfold hb_equiv, have_same_events in *; intros.
      destruct H; specialize (H a); crush.
    - intros; apply hb_equiv_same_dep in H; rewrite <- H in H0;
      apply dep_is_total in H0; assumption.
  Qed.

  Lemma hb_equiv_transitive:
    forall E E1 E2,
      hb_equiv E E1 -> hb_equiv E1 E2 -> hb_equiv E E2.
  Proof.
    intros; unfold hb_equiv, have_same_events, keeps_dep_order.
    split.
    - unfold hb_equiv, have_same_events, keeps_dep_order in *; crush.
      specialize (H1 a); specialize (H a); crush.
    - unfold hb_equiv, have_same_events, keeps_dep_order in H0; crush.
      apply hb_equiv_same_dep in H; rewrite <- H in H2; crush.
  Qed.

  Axiom hb_equiv_extensible:
    forall E E' w,
      is_ex_seq (E +++ w) ->
      (hb_equiv E E' <-> hb_equiv (E +++ w) (E' +++ w)).

  Definition in_dom_after (a : event) E w := In a (E +++ w) /\ ~ In a E.

  Lemma in_dom_after_in:
    forall a E w, in_dom_after a E w -> In a w.
  Proof.
    unfold in_dom_after; crush; apply in_app_iff in H0; crush.
  Qed.

  Lemma in_dom_after_uniq:
    forall e E w,
      is_ex_seq (w ++ E) -> In e w -> in_dom_after e E w.
  Proof.
    intros.
    unfold in_dom_after; crush.
    apply ex_seq_is_event_seq in H.
    apply events_unique with (e := e) in H; crush.
  Qed.

  Definition indep_after_seq_core E p w :=
    forall e,
      in_dom_after e (E ** p) w ->
      ~ Is_true (dependent (E ** p +++ w) (next E p) e).

  Definition indep_after_seq E p w :=
    is_ex_seq (E +++ w) /\
    is_ex_seq (E ** p +++ w) /\ indep_after_seq_core E p w.

  Definition indep_after_proc E p q := indep_after_seq E p ([next E q]).

  Definition dep_after_seq E p w :=
    is_ex_seq (E +++ w) /\ is_ex_seq (E ** p +++ w) /\ ~ indep_after_seq E p w.

  Definition initial E w p :=
    is_ex_seq (E +++ w) /\ In (next E p) w /\
    forall e',
      in_dom_after e' E w -> ~ Is_true (dependent (E +++ w) e' (next E p)).

  Definition weak_initial p E w :=
    initial E w p \/ (enabled_after E p /\ indep_after_seq E p w).

  Lemma indep_after_seq_no_p:
    forall E p w,
      is_ex_seq (E ** p +++ w) -> in_seq p w -> ~ indep_after_seq E p w.
  Proof.
    intros; unfold indep_after_seq; destruct H0;
    repeat (apply or_not_and; right);
    apply not_forall_exists.
    exists (p, x); apply not_implies; split.
    - unfold in_dom_after; split.
      + crush.
      + apply ex_seq_is_event_seq in H;
        apply events_unique with (e := (p, x)) in H;
        crush.
    - in_splitter; intuition; contradict H1;
      unfold exec_event in H; remember (next_index E p) as j;
      apply dep_same_proc.
      + crush.
      + crush.
      + apply ex_seq_is_event_seq in H;
        apply events_unique_help with
        (E := (p, j) :: E)
          (w := (p, x) :: x1 +++ x0)
          (p := p) (j := j) (i := x) in H;
        crush.
  Qed.

  Lemma indep_after_seq_not_in:
    forall E p w, indep_after_seq E p w -> ~ in_seq p w.
  Proof.
    unfold not; intros; pose proof H as H'; destruct H';
    apply indep_after_seq_no_p in H; crush.
  Qed.

  Lemma indep_after_seq_cons:
    forall E p a w, indep_after_seq E p (a :: w) -> indep_after_seq E p w.
  Proof.
    unfold indep_after_seq; crush.
    - inversion H0; crush.
    - apply is_ex_seq_cons in H; crush.
    - unfold indep_after_seq_core in *; crush; contradiction H2 with (e:=e).
      + unfold in_dom_after in *; crush.
      + inversion H0; unfold in_dom_after in H.
        pose proof dep_prefix.
        destruct H8 with
        (E' := ((p0, next_index (w ++ E) p0) :: w ++ exec_event E p))
          (E := (w ++ exec_event E p))
          (a := (next E p))
          (b := e).
        * unfold exec_event, next; crush.
        * unfold in_dom_after in H1; crush.
        * unfold prefix.
          exists ((p0, next_index (w ++ E) p0) :: nil); crush.
        * crush.
  Qed.

  Lemma indep_after_not_eq:
    forall E p q, indep_after_proc E p q -> p <> q.
  Proof.
    unfold indep_after_proc; crush; apply indep_after_seq_no_p in H.
    - crush.
    - unfold indep_after_seq in H; crush.
    - unfold in_seq, next; exists (next_index E q); crush.
  Qed.

  Lemma indep_after_dep_false:
    forall E p q,
      indep_after_proc E p q ->
      ~ Is_true (dependent (E ** p ** q) (next E p) (next E q)).
  Proof.
    intros; pose proof H as H'; apply indep_after_not_eq in H'.
    unfold
      indep_after_proc, indep_after_seq, indep_after_seq_core, in_dom_after in *.
    destruct H as [H H1]; destruct H1 as [H1 H2]; specialize (H2 (next E q)).
    apply ex_seq_is_event_seq in H; apply ex_seq_is_event_seq in H1; simpl in H2.
    unfold exec_event at 1; rewrite <- diff_q_same_index.
    - unfold next at 7 in H2; apply H2; clear H2; crush.
      + unfold next in H2; crush.
      + assert (forall E q, next E q :: E = [next E q] ++ E).
        * crush.
        * rewrite H0 in H; apply events_unique with (e := next E q) in H; crush.
    - apply is_event_seq_cons in H1; crush.
    - crush.
  Qed.

  Lemma indep_after_seq_same_index:
    forall E p w,
      indep_after_seq E p w -> next_index E p = next_index (E +++ w) p.
  Proof.
    intros; pose proof H as H'; apply indep_after_seq_not_in in H'.
    unfold indep_after_seq in *; destruct H; destruct H0.
    apply ex_seq_is_event_seq in H.
    apply not_in_seq_same_index with (p:=p) in H; crush.
  Qed.

  Lemma indep_after_seq_next:
    forall E p a w,
      indep_after_seq E p ([a] +++ w) -> indep_after_seq E p ([a]).
  Proof.
    intros; induction w.
    - crush.
    - simpl in H; apply indep_after_seq_cons in H; crush.
  Qed.

  Lemma indep_after_seq_exec:
    forall E p a w,
      indep_after_seq E p ([a] +++ w) -> indep_after_seq (E +++ [a]) p w.
  Proof.
    intros; pose proof H as H'.
    unfold indep_after_seq; unfold indep_after_seq in H.
    assert (hb_equiv (a :: exec_event E p) (exec_event (a :: E) p)).
    - crush.
      unfold exec_event.
      rewrite (cons_as_app _ a E).
      rewrite <- indep_after_seq_same_index.
      + apply is_ex_seq_app in H.
        apply is_ex_seq_app in H0.
        apply independent_step_hb_equiv.
        * crush; unfold exec_event in H; assumption.
        * { unfold indep_after_seq_core in H2; specialize (H2 a).
            assert (in_dom_after a (exec_event E p) (w ++ [a])).
            - split.
              + crush.
              + apply events_unique with (w := [a]); crush.
                apply ex_seq_is_event_seq; crush.
            - crush. contradict H4.
              pose proof (dep_prefix  (a :: (p, next_index E p) :: E) (w ++ a :: exec_event E p) (next E p) a).
              destruct H2; crush.
              unfold rev_prefix; exists w; crush.
          }
      + apply indep_after_seq_next with (w := w); crush.
    - crush.
      + apply hb_equiv_is_ex_seq with (E := w ++ a :: exec_event E p); crush.
        apply hb_equiv_extensible; crush.
      + unfold indep_after_seq_core in *.
        intros.
        specialize (H3 e).
        unfold in_dom_after in *.
        assert
          ((In e (w ++ exec_event (a :: E) p) /\ ~ In e (exec_event (a :: E) p)) ->
           In e ((w ++ [a]) ++ exec_event E p) /\ ~ In e (exec_event E p)).
        * { crush.
            - unfold exec_event in *.
              rewrite (cons_as_app _ a E) in H5.
              rewrite <- indep_after_seq_same_index in H5.
              + simpl in H5; apply in_app_or in H5; crush.
              + apply indep_after_seq_next with (w := w); assumption.
            - destruct a.
              apply indep_after_seq_not_in in H'.
              unfold in_seq in H'.
              apply not_exists_forall with (x := n) in H'.
              apply not_in_app in H'.
              destruct H'.
              simpl in H12.
              apply not_or_and in H12.
              destruct H12.
              apply pair_ineq_fst in H12.
              contradict H3; case eq_proc_dec; crush.
          }
        * { crush.
            contradict H2.
            unfold next in H5.
            rewrite (cons_as_app _ a E) in H5.
            rewrite <- indep_after_seq_same_index in H5.
            - unfold next.
              rewrite hb_equiv_same_dep with (E' := w ++ exec_event (([a]) ++ E) p).
              + assumption.
              + apply hb_equiv_extensible; assumption.
            - apply indep_after_seq_next with (w := w); assumption.
          }
  Qed.

  Lemma rev_unit_2:
    forall (A : Type) (l : list A) (a : A), rev (a :: l) = rev l ++ [a].
  Proof.
    intros; induction l; crush.
  Qed.

  Lemma indep_after_seq_app:
    forall E p w w',
      indep_after_seq E p (w +++ w') -> indep_after_seq (E +++ w) p w'.
  Proof.
    intros; generalize dependent E; induction w using rev_ind.
    - rewrite app_nil_r; crush.
    - intros; rewrite app_assoc in H; apply indep_after_seq_exec in H.
      rewrite <- app_assoc; apply IHw in H; assumption.
  Qed.

  Lemma indep_swappable:
    forall E p w,
      indep_after_seq E p w -> is_ex_seq ((E +++ w) ** p).
  Proof.
    intros; rewrite <- app_nil_l in H;
    apply indep_after_seq_app in H;
    unfold indep_after_seq in H;
    crush.
  Qed.

  Lemma in_cons_app:
    forall (t : Type) (a b: t) l1 l2,
      In a (l1 ++ b :: l2) <-> In a (b :: l1 ++ l2).
  Proof.
    crush.
    apply in_app_iff in H; crush.
    apply in_app_iff in H0; crush.
  Qed.

  Lemma indep_after_seq_hb_eq:
    forall E p w,
      indep_after_seq E p w -> hb_equiv (E ** p +++ w) ((E +++ w) ** p).
  Proof.
    intros; unfold hb_equiv, exec_event;
    rewrite <- indep_after_seq_same_index; crush.
    - unfold have_same_events; intros; apply in_cons_app.
    - unfold keeps_dep_order.
      unfold indep_after_seq in H.
      crush.
      + dep_works.
      + apply in_app_iff in H3; crush.
        * unfold indep_after_seq_core in H2.
          crush.
          specialize (H2 b).
          crush.
          assert (in_dom_after b (exec_event E p) w).
          { unfold in_dom_after; crush.
            - unfold exec_event in H.
              apply ex_seq_is_event_seq in H.
              apply events_unique with (e := (p, next_index E p)) in H; crush.
            - apply ex_seq_is_event_seq in H0.
              apply events_unique with (e := b) in H0; crush.
          }
          crush.
        * contradict H1.
          { apply before_not_dep.
            - crush.
            - unfold is_after_in; in_splitter; exists x0, x, w; crush.
          }
      + dep_works.
      + unfold exec_event in H.
        rewrite app_comm_cons in *.
        apply in_app_iff in H3.
        apply in_app_iff in H5.
        crush.
        * Lemma solve_dep_prefix_2:
            forall E w a0 b0,
              is_ex_seq (w ++ E) ->
              Is_true (dependent (w ++ E) a0 b0) ->
              ~ In a0 E ->
              ~ In b0 E ->
              is_after_in w a0 b0.
          Proof.
            intros.
            apply dep_is_total in H0.
            apply is_after_cases in H0.
            Lemma is_after_is_in:
              forall l a b,
                is_after_in l a b -> In a l /\ In b l.
              unfold is_after_in; crush.
              apply in_or_app; crush.
            Qed.
            destruct H0.
            assumption.
            crush.
            apply is_after_is_in in H3.
            crush.
          Qed.
          pose proof H as H'.
          pose proof H1 as H1'.
          apply ex_seq_is_event_seq in H.
          pose proof H as H''.
          apply events_unique with (e:=a) in H; crush.
          apply events_unique with (e:=b) in H''; crush.
          apply dep_is_total in H1.
          apply solve_dep_prefix_2 with (E := (p, next_index E p) :: E) (a0 := a) (b0 := b) in H'.
          unfold is_after_in in *.
          crush.
          exists (x++E),x0,((p, next_index E p) :: x1).
          crush.
          crush.
          crush.
          crush.
        * contradict H1.
          crush.
          apply dep_not_before with (a:=a) (b:=b) in H; crush.
          assert (is_after_in (w ++ (p, next_index E p) :: E) b a).
          unfold is_after_in.
          in_splitter.
          exists x0, (x2 ++ (p, next_index (x ++ b :: x0) p) :: x), x1.
          crush.
          crush.
        * unfold is_after_in.
          in_splitter.
          exists x2, (x0 ++ x1), ((p, next_index (x1 ++ a :: x2) p) :: x).
          crush.
        * Lemma solve_dep_prefix_3:
            forall E w a w' a0 b0,
              is_ex_seq (w ++ a :: E) ->
              In a0 E ->
              In b0 E ->
              Is_true (dependent (w ++ a :: E) a0 b0) ->
              is_after_in (w' ++ E) a0 b0.
          Proof.
            intros; apply dep_is_total.
            assert (rev_prefix _ E (w ++ a :: E)).
            - unfold rev_prefix; exists (w ++ [a]); crush.
            - assert (rev_prefix _ E (w' ++ E)).
              + unfold rev_prefix; exists w'; crush.
              + pose proof (dep_prefix E (w ++ a :: E) a0 b0); crush.
                pose proof (dep_prefix E (w' ++ E) a0 b0); crush.
          Qed.
          rewrite app_comm_cons.
          apply solve_dep_prefix_3 with (w := w) (a := (p, next_index E p));
            crush.
  Qed.

  Lemma in_dom_after_cons:
    forall e E a w,
      in_dom_after e E w -> in_dom_after e E (a::w).
    unfold in_dom_after; crush.
  Qed.

  Lemma is_ex_seq_in_dom_after:
    forall E w a,
      is_ex_seq (E +++ w) -> In a w -> in_dom_after a E w.
    intros; unfold in_dom_after; apply ex_seq_is_event_seq in H.
    apply events_unique with (e := a) in H; crush.
  Qed.

  Lemma initial_ex_seq:
    forall E w p, initial E w p -> is_ex_seq (E ** p).
  Proof.
    unfold initial; unfold in_seq; crush; induction w.
    - crush.
    - induction w; crush.
      pose proof H2 as H2'.
      specialize (H2' a0).
      assert (next E p :: a0 :: w ++ E = ((next E p :: a0 :: w) ++ E)). crush.
      pose proof H0 as H0'.
      rewrite H in H0' at 1.
      apply is_ex_seq_in_dom_after with (a := a0) in H0'; crush.
      pose proof (independent_step_hb_equiv (w ++ E) a0 (next E p)); crush.
      + apply IHw0; clear IHw0.
        * apply hb_equiv_is_ex_seq with (E' := a0 :: next E p :: w ++ E) in H0; crush.
          apply is_ex_seq_cons in H0; crush.
        * crush.
        * intros.
          pose proof (dep_prefix (next E p :: w ++ E) (a0 :: next E p :: w ++ E) e' (next E p)).
          { apply in_dom_after_in in H4; destruct H6.
            - crush.
            - crush.
            - unfold rev_prefix; exists ([a0]); crush.
            - apply H7 in H5.
              apply hb_equiv_same_dep in H3.
              pattern (dependent (a0 :: next E p :: w ++ E)) in H5.
              rewrite <- H3 in H5.
              specialize H2 with e'.
              crush.
              + apply dep_not_refl in H5; crush.
              + apply is_ex_seq_in_dom_after with (E := E) (w:= next E p :: a0 :: w) (a := e') in H0; crush.
          }
        * intros; apply ex_seq_is_event_seq in H0.
          assert (next E p :: a0 :: w ++ E = ((next E p :: [a0]) ++ (w ++ E))). crush.
          rewrite H7 in H0 at 1; apply events_unique with (e:=next E p) in H0; crush.
      + apply is_ex_seq_cons in H0; apply IHw; crush.
        specialize (H2 e').
        pose proof H4 as H4'; apply in_dom_after_cons with (a := a) in H4'.
        crush.
        pose proof (dep_prefix (next E p :: w ++ E) (a :: next E p :: w ++ E) e' (next E p)).
        destruct H2.
        * apply in_dom_after_in in H4; crush.
        * crush.
        * unfold rev_prefix; exists ([a]); crush.
        * crush.
      + apply IHw.
        * apply is_ex_seq_cons in H0; crush.
        * crush.
        * crush; specialize (H2 e').
          pose proof H1 as H1'; apply in_dom_after_cons with (a := a) in H1'.
          crush.
          pose proof (dep_prefix (a0 :: w ++ E) (a :: a0 :: w ++ E) e' (next E p)).
          { destruct H2.
            - apply in_dom_after_in in H1; crush.
            - crush.
            - unfold rev_prefix; exists ([a]); crush.
            - crush.
          }
  Qed.

  Lemma in_dom_after_in_sub:
    forall w w1 w2 w3 w4 a b,
      is_ex_seq (w1 ++ w ++ w2) ->
      Is_true (dependent (w1 ++ w ++ w2) a b) ->
      In a w ->
      In b w ->
      is_after_in (w3 ++ w ++ w4) a b.
  Proof.
    intros; apply dep_is_total in H0.
    apply ex_seq_is_event_seq in H.
    apply is_after_cases in H0; crush.
    - apply is_after_is_in in H3.
      apply events_unique with (e := a) in H; crush.
    - apply events_unique with (e := b) in H; crush.
    - apply is_after_cases in H0; destruct H0.
      + unfold is_after_in in *; crush.
        exists (x ++ w4), x0, (w3 ++ x1); crush.
      + rewrite app_assoc in H; destruct H0.
        * apply events_unique with (e:=a) in H; crush.
        * apply is_after_is_in in H0.
          apply events_unique with (e:=a) in H; crush.
  Qed.

  Lemma initials_ext:
    forall E w p,
      is_ex_seq (E +++ w) ->
      (initial E w p <-> exists w', hb_equiv (E +++ w) (E ** p +++ w')).
  Proof.
    unfold initial; crush.
    - unfold in_seq in H0.
      crush.
      in_splitter.
      clear_dups.
      exists (x ++ x0).
      rewrite <- ?app_assoc.
      apply hb_equiv_extensible; crush.
      unfold exec_event.
      apply is_ex_seq_app in H.
      unfold hb_equiv, have_same_events, keeps_dep_order; crush.
      + apply in_app_iff in H1; crush.
      + apply in_app_iff in H0; crush.
      + apply in_app_iff in H1.
        apply in_app_iff in H2.
        Lemma in_dom_after_app:
          forall e E a w,
            in_dom_after e E w -> in_dom_after e E (a ++ w).
          unfold in_dom_after; crush.
        Qed.
        crush.
        * rewrite <- app_nil_l with (l:=(x0 ++ (p, next_index E p) :: E)).
          apply in_dom_after_in_sub with (w1 := [next E p]) (w2 := E); crush.
        * specialize (H3 a).
          rewrite app_comm_cons in H.
          apply is_ex_seq_in_dom_after with (a := a) in H; crush.
          apply in_dom_after_app with (a := x) in H.
          crush.
          unfold next at 2 in H1.
          Check dep_prefix.
          pose proof (dep_prefix (next E p :: x0 ++ E) (x ++ next E p :: x0 ++ E) a (p, next_index E p)).
          destruct H2; crush.
          unfold rev_prefix; exists x; crush.
        * contradict H0; apply before_not_dep; crush.
          in_splitter; unfold is_after_in.
          exists x2, (x4 ++ x1), (next (x1 ++ b :: x2) p :: x3); crush.
        * contradict H0.
          apply before_not_dep; crush.
          unfold is_after_in.
          in_splitter.
          exists (x2 ++ E), x1, nil.
          unfold next.
          crush.
        * in_splitter; unfold is_after_in.
          exists x2, (x4 ++ (p, next_index (x1 ++ a :: x2) p) :: x1), x3; crush.
        * dep_works.
        * contradict H0; apply before_not_dep; crush.
          in_splitter; unfold is_after_in.
          unfold next.
          exists x2, (x0 ++ x1), nil; crush.
        * in_splitter; unfold is_after_in.
          exists x2, x1, x0; crush.
        * rewrite <- app_nil_r with (l:=(x0 ++ (p, next_index E p) :: E)).
          rewrite cons_as_app.
          rewrite app_assoc.
          rewrite <- app_assoc.
          apply in_dom_after_in_sub with (w1 := (next E p :: x0)) (w2 := nil); crush.
          rewrite app_nil_r; crush.
          rewrite app_nil_r; crush.

    - unfold exec_event in H0.
      unfold in_seq.
      unfold next.
      generalize dependent (p, (next_index E p)).
      intros.
      apply hb_equiv_is_ex_seq with (E' := x ++ p0 :: E) in H.
      unfold hb_equiv in H0.
      unfold have_same_events in H0.
      crush.
      clear H2.
      specialize (H1 p0).
      crush.
      clear H0.
      assert (In p0 (x ++ p0 :: E)); crush.
      apply in_app_iff in H1; crush.
      apply ex_seq_is_event_seq in H.
      rewrite cons_as_app in H.
      rewrite app_assoc in H.
      apply events_unique with (e := p0) in H; crush.
      crush.
    - pose proof H0 as H0'.
      pose proof H0 as H0''.
      unfold hb_equiv in H0'.
      unfold have_same_events in H0'.
      crush.
      unfold in_dom_after in H1.
      crush.
      specialize (H3 e').
      crush.
      unfold exec_event in H3.
      rewrite cons_as_app in H3.
      rewrite app_assoc in H3.
      apply in_app_iff in H3; crush.

      apply hb_equiv_same_dep in H0.
      rewrite H0 in H2.

      unfold exec_event in H2.
      unfold next in H2.

      apply in_app_iff in H7; crush.
      + contradict H2.
        apply before_not_dep.
        apply hb_equiv_is_ex_seq with (E' := (x ++ (p, next_index E p) :: E)) in H; crush.
        apply in_split in H3.
        crush.
        unfold is_after_in.
        exists E, x1, x0.
        crush.
      + apply dep_not_refl in H2.
        crush.
        apply hb_equiv_is_ex_seq with (E':=(x ++ (p, next_index E p) :: E)) in H.
        crush.
        unfold exec_event in H4.
        crush.
  Qed.

  Lemma weak_initials_ext:
    forall E w p,
      is_ex_seq (E +++ w) ->
      (weak_initial p E w <->
       exists w' w'', hb_equiv (E +++ w +++ w') (E ** p +++ w'')).
  Admitted.

  Theorem indep_after_proc_hb_eq:
    forall E p q,
      indep_after_proc E p q -> hb_equiv (E ** p ** q) (E ** q ** p).
  Admitted.

  Theorem indep_after_proc_enabled:
    forall E p q,
      indep_after_proc E p q -> enabled_after (E ** q) p.
  Admitted.

  Theorem indep_after_proc_symmetric:
    forall E p q,
      indep_after_proc E p q -> indep_after_proc E q p.
  Admitted.

  Axiom dependent_step_swap:
    forall E a b,
      Is_true (dependent (E +++ [a] +++ [b]) a b) <->
      Is_true (dependent (E +++ [b] +++ [a]) b a).

  Axiom hb_equiv_same_state:
    forall E E',
      hb_equiv E E' <-> state_after_maybe E = state_after_maybe E'.

End Dep.
