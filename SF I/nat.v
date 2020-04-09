
Inductive nat :=
  | zero : nat
  | S : nat -> nat.


Fixpoint plus (m n : nat) :=
  match n with
  | zero => m
  | S n' => S (plus m n')
  end.


Lemma n_plus_zero_is_n :
  forall n, plus n zero = n.
Proof.
  intros n0.
  simpl.
  reflexivity.
Qed.

Lemma zero_plus_n_is_n :
  forall n, plus zero n = n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn.
    reflexivity.
Qed.

Lemma plus_comm:
  forall m n, plus m n = plus n m.
Proof.
  induction m.
  - intros.
    rewrite n_plus_zero_is_n.
    rewrite zero_plus_n_is_n.
    reflexivity.
  - induction n.
    -- simpl.
       rewrite zero_plus_n_is_n.
       reflexivity.
    -- simpl.
       rewrite IHn.
       rewrite <- IHm.
       simpl.
       rewrite IHm.
       reflexivity.
Qed.




Fixpoint mult (n m : nat) : nat :=
  match n with
    | zero => zero
    | S n' => plus m (mult n' m)
  end.


Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | zero , _ => zero
  | S _ , zero => n
  | S n', S m' => minus n' m'
  end.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat.

Check ((0 + 1) + 1).

