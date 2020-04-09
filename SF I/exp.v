From LF Require Export Basics.
Require Import String.

Inductive Exp :=
| id : string -> Exp
| const : nat -> Exp
| plus : Exp -> Exp -> Exp
| times : Exp -> Exp -> Exp.

Check (id "x").
Check (const 5).
Check (plus (id "x") (const 5)).


Definition state1 (x : string)
  : nat :=
  if (string_dec x "x")
  then 10
  else 0.

Eval compute in (state1 "y").

Fixpoint interpret
         (e : Exp)
         (state : string -> nat) : nat :=
  match e with
  | const n => n
  | id x => (state x)
  | plus e1 e2 => (interpret e1 state) + (interpret e2 state)
  | times e1 e2 => (interpret e1 state) * (interpret e2 state)
  end.

Eval compute in (interpret (id "x") state1).
Eval compute in (interpret (const 5) state1).
Eval compute in (interpret (plus (const 5) (id "x")) state1).


(* Stack machine *)
Inductive instr :=
| push_const : nat -> instr
| push_var : string -> instr
| add : instr
| mul : instr.

Require Import List.

Fixpoint run
         (i : instr)
         (state : string -> nat)
         (stack : list nat) : list nat :=
  match i with
  | push_const n => (n :: stack)
  | push_var x => (state x) :: stack
  | add => match stack with
           | (n1 :: n2 :: s') =>
             (n1 + n2) :: s'
           | _ => stack
           end
  | mul => match stack with
           | (n1 :: n2 :: s') =>
             (n1 * n2) :: s'
           | _ => stack
           end
  end.

Eval compute in run (push_const 4) state1 nil.
Eval compute in run (push_var "x") state1 nil.
Eval compute in run mul state1 (2 :: 3 :: nil).

Fixpoint run_all (l : list instr)
         (state : string -> nat)
         (stack : list nat) : list nat :=
  match l with
  | nil => stack
  | i :: l' =>
    run_all l' state (run i state stack)
  end.

Eval compute in
    run_all
      (push_const 4 :: push_var "x" :: add :: nil)
      state1
      nil.


Fixpoint compile (e : Exp) : list instr :=
  match e with
  | const n => (push_const n :: nil)
  | id x => (push_var x :: nil)
  | plus e1 e2 => (compile e1) ++ (compile e2) ++ (add :: nil)
  | times e1 e2 => (compile e1) ++ (compile e2) ++ (mul :: nil)
  end.

Eval compute in
    compile (plus (id "x") (const 5)).

Eval compute in
    run_all
      (compile (plus (id "x") (const 5)))
      state1 nil.


Lemma compiler_correct':
  forall e state stack is',
    run_all is' state (interpret e state :: stack) =
    run_all (compile e ++ is') state stack.
Proof.
  induction e; simpl; intros.
  - reflexivity.
  - reflexivity.
  - rewrite app_assoc_reverse.
    rewrite <- IHe1.
    rewrite app_assoc_reverse.
    rewrite <- IHe2.
    simpl.
    rewrite PeanoNat.Nat.add_comm.
    trivial.
  - rewrite app_assoc_reverse.
    rewrite <- IHe1.
    rewrite app_assoc_reverse.
    rewrite <- IHe2.
    simpl.
    rewrite PeanoNat.Nat.mul_comm.
    trivial.
Qed. 

Theorem compiler_correct:
  forall e state,
    (interpret e state) :: nil =
    run_all (compile e) state nil.
Proof.
  intros.
  rewrite <- app_nil_r with (l := (compile e)).
  rewrite <- compiler_correct'.
  simpl.
  trivial.
Qed.

Require Extraction.
Extraction Language OCaml.
Recursive Extraction compile.