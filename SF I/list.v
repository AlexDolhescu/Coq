Module NatList. 

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Definition fst (p : natprod) : nat := 
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat := 
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition fst' (p : natprod) : nat := 
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat := 
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod := 
  match p with
  | (x,y) => (y,x)
  end.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. 
  destruct p as [n m].  
  simpl. 
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),  (* 1 star *)
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p.
  reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.


Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Fixpoint nonzeros (l:natlist) : natlist :=    (* 2 star *)
match l with
| nil => nil
| O :: a => nonzeros a
| a :: b => a :: (nonzeros b)
end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.  reflexivity. Qed.

Fixpoint alternate (L1 L2 : natlist) : natlist :=  
 match L1 with
| nil => L2
| a :: L1' => match L2 with
| nil => L1
| b :: L2' => a :: b :: (alternate L1' L2')
end
end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. 
  reflexivity. 
Qed.

Definition bag := natlist.

Notation beq_nat := Nat.eqb (only parsing).

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t => if(beq_nat v h) then 1 + (count v t) else count v t end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. 
  reflexivity. 
Qed.

Definition sum : bag -> bag -> bag :=
  fun l1 l2 => app l1 l2.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof.
  simpl. 
  reflexivity. 
Qed.

Definition add (v:nat) (s:bag) : bag := app [v] s.
  
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. 
  simpl. 
  reflexivity. 
Qed.

Fixpoint member (v:nat) (s:bag) : bool :=
  match s with
  | nil => false
  | h :: t => if(beq_nat v h) then true else member v t end.

Example test_member1: member 1 [1;4;1] = true.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => if(beq_nat v h) then t else h :: (remove_one v t) end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => if(beq_nat v h) then remove_all v t else h :: remove_all v t end.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Theorem rev_snoc : forall l: natlist, forall n : nat,
rev (snoc l n) = n :: (rev l).
Proof.
  intros l n.
  induction l.
  -reflexivity.
  -simpl.
   rewrite -> IHl.
   reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l.
  - simpl. reflexivity.
  - simpl. rewrite -> IHl. reflexivity.
Qed.


Theorem rev_involutive : forall l : natlist,   (* 3 star *)
rev (rev l) = l.
Proof.
  intros l.
  induction l.
  -reflexivity.
  -simpl.
   rewrite -> rev_snoc.
   rewrite -> IHl.
   reflexivity.
Qed.


Theorem rev_func : forall (l1 l2 : natlist), l1 = l2 -> rev l1 = rev l2.
Proof.
  intros.
  rewrite -> H.
  reflexivity.
Qed.


Theorem rev_inj : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.  (* 4 stars *)
Proof.
  intros.
  rewrite <- rev_involutive with (l := l1).
  rewrite <- rev_involutive with (l := l2).
  apply rev_func.
  apply H.
Qed.

Notation "a <=? b" := (Nat.leb b a)
                          (at level 70, only parsing) : nat_scope.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s. induction s.
  - simpl. reflexivity.
  - simpl. { induction n.
             - simpl. 
Abort.






