Lemma add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mul_0_r : forall n:nat, 
    n * 0 = 0. 
Proof. 
    intros n. induction n as [| n' IHn'].
    (* n = 0 *)
    - reflexivity. 
    - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat, 
    S (n + m) = n + (S m). 
Proof. 
    intros n. induction n as [| n' IHn']. 
    (* S(0 + m) = 0 + S m *)
    - simpl. reflexivity. 

    (* S(S n' + m) = S n' + S m *)
    - induction m as [| m' IHm'].
     + simpl. rewrite -> IHn'. reflexivity. 
     + simpl. rewrite -> IHn'. reflexivity.
    Qed.

Theorem add_comm : forall n m : nat, 
    n + m = m + n. 
Proof. 
    intros n. induction n as [| n' IHn']. 
    - induction m as [| m' IHm'].
     + reflexivity. 
     + rewrite -> add_0_r. reflexivity.
    - induction m as [| m' IHm'].
     + rewrite -> add_0_r. reflexivity.
     + simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. simpl. reflexivity. Qed.

Theorem add_assoc : forall n m p : nat, 
    n + (m + p) = (n + m) + p. 
Proof. 
    intros n m p. induction n as [| n' IHn'].
    - rewrite <- add_0_r. simpl. rewrite -> add_0_r. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
    Qed. 