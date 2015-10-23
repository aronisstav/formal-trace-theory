Require Import Bool Classical_Prop List.

Require Import CpdtTactics.

Notation "[ a ]" := (a :: nil) (at level 60).
Notation "E +++ w" := (w ++ E) (at level 61, left associativity, only parsing).

Ltac in_splitter :=
  repeat
    match goal with
      | H: In _ _ |- _ => apply in_split in H
      | H: ex _   |- _ => destruct H
      | H: eq _ _ |- _ => rewrite H in *
    end.

Ltac destruct_exs :=
  repeat
    match goal with
      | H: ex _   |- _ => destruct H
    end.

Ltac clear_dup :=
  match goal with
    | [ H : ?X |- _ ] =>
      match goal with
        | [ H' : ?Y |- _ ] =>
          match H with
            | H' => fail 2
            | _ => unify X Y ; (clear H' || clear H)
          end
      end
  end.

Ltac clear_dups := repeat clear_dup.

Definition prefix (t : Type) (a b : list t) := exists c, b = a ++ c.
Definition rev_prefix (t : Type) (a b : list t) := exists c, b = c ++ a.

Lemma not_forall_exists:
  forall T P, (exists x:T, ~ P x) -> ~ forall x, P x.
  crush.
Qed.

Lemma not_implies:
  forall P Q, (P /\ ~Q) -> ~ (P -> Q).
  tauto.
Qed.

Lemma not_in_cons:
  forall (t : Type) (a b : t) l, a <> b /\ ~ In a l -> ~ In a (b :: l).
  crush.
Qed.

Lemma not_in_app:
  forall (t : Type) (a : t) l l', ~ In a (l ++ l') -> ~ In a l /\ ~ In a l'.
  crush.
Qed.

Lemma is_true_help:
  forall a b, Is_true (eqb a b) <-> (Is_true a <-> Is_true b).
  intros; induction a, b; crush.
Qed.

Lemma eq_split:
  forall (t : Type) (a : t) l1 l2 t1 t2,
    l1 ++ a :: l2 = t1 ++ t2 -> In a t1 \/ In a t2.
Proof.
  intros; apply in_app_or; rewrite <- H; crush.
Qed.

Lemma in_inv_rev:
  forall (A : Type) (a b : A) (l : list A),
    In b (l ++ [a]) -> a = b \/ In b l.
Proof.
  intros; apply in_rev in H; rewrite rev_unit in H; apply in_inv in H;
  destruct H.
  - left; assumption.
  - right; apply in_rev; assumption.
Qed.

Fixpoint not_appears_after t (a b : t) l :=
  match l with
    | nil => True
    | h :: l' => h = a \/ (h <> b /\ not_appears_after t a b l')
  end.

Lemma not_appears_after_dec:
  forall (t : Type) (a b: t) l,
    In a l -> In b l -> a <> b ->
    not_appears_after t a b l \/ not_appears_after t b a l.
Proof.
  intros; induction l; crush.
  + classical_left; crush.
  + classical_right; crush.
Qed.

Lemma not_appears_after_split:
  forall t a b l l',
    not_appears_after t a b (l ++ b :: l') -> a <> b -> In a l.
Proof.
  intros; induction l; crush.
Qed.

Lemma neq_elements_ordered:
  forall (t : Type) (a b: t) l1 l2 t1 t2,
    a <> b -> l1 ++ a :: l2 = t1 ++ b :: t2 -> In a t1 \/ In b l1.
Proof.
  intros; pose proof (not_appears_after_dec t a b (l1 ++ a :: l2)).
  destruct H1; crush.
  - left; rewrite H0 in H1;
    apply not_appears_after_split with (b := b) (l' := t2);
    crush.
  - right;
    apply not_appears_after_split with (b := a) (l' := l2);
    crush.
Qed.

Lemma none_none:
  forall A, (None :option A) <> None -> False.
  crush.
Qed.

Definition just T (A:option T) : A <> None -> T :=
  match A return A <> None -> T with
    | None => fun pf: None <> None => match none_none T pf with end
    | Some t => fun _ => t
  end.

Lemma cons_as_app:
  forall (t : Type) (a : t) l,
    a :: l = [a] ++ l.
  crush.
Qed.

Lemma not_exists_forall:
  forall T P, (~ exists x:T, P x) -> forall x, ~ P x.
Proof.
  intros; contradict H; exists x; assumption.
Qed.

Lemma pair_ineq_fst :
  forall (t t' : Type) (a : t) (b b' : t'),
    (b, a) <> (b', a) -> b <> b'.
  crush.
Qed.

Lemma ge_lt_dec:
  forall n m, {n < m} + {n >= m}.
Proof.
  intros.
  pose proof (Compare_dec.gt_eq_gt_dec n m).
  crush.
Qed.
