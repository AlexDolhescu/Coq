Require Import Omega.


Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros.
  induction n.
  -simpl.
   reflexivity.
  -simpl.
   rewrite IHn.   (*  apply IHn.   *)
   reflexivity.
Qed.

Theorem plus_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  -reflexivity.
  -simpl. 
   rewrite -> IHn'. 
   reflexivity.  
Qed.


Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof. 
  intros.
  induction n.
  -simpl.
   reflexivity.
  -simpl.
   rewrite -> IHn.
   reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
   -reflexivity.
   -simpl.
    rewrite -> IHn.
    reflexivity. 
Qed.

Lemma plus_distr : forall n m: nat, S (n + m) = n + (S m).
Proof.
  intros. 
  induction n.
  -reflexivity.
  -simpl.
   rewrite -> IHn. 
   reflexivity. 
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n.
  -simpl.
   rewrite -> plus_0_r.
   reflexivity.
  -simpl.
   rewrite ->IHn.
   rewrite -> plus_distr.
   reflexivity.
Qed.


Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  assert(H: m + (n + p) = (m + n) + p).
  -rewrite -> plus_assoc.
   reflexivity.
  -rewrite -> H.
   assert(H2: m + n = n + m).
   --rewrite -> plus_comm.
     reflexivity.
   --rewrite -> H2.
     reflexivity.
Qed.

Lemma mult_distr : forall n m: nat, (n*m) + n = n*(S m).
Proof.
  intros. 
  induction n.
  -reflexivity.
  -simpl.
   rewrite <- plus_n_Sm.
   rewrite <- IHn.
   rewrite -> plus_assoc.
   reflexivity. 
Qed.

Lemma mult_distr2 : forall n m: nat, (n*m) + m = (S n)*m.
Proof.
  intros. 
  induction n.
  -simpl.
   rewrite -> plus_0_r.
   reflexivity.
  -simpl.
   rewrite -> plus_assoc.
   assert (n*m + m = m + n*m).
   --rewrite -> plus_comm.
     reflexivity.
   --rewrite -> Nat.add_comm.
     rewrite Nat.add_assoc.
     reflexivity.
Qed.


