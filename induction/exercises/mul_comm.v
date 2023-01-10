(* proofs i have written previously will just use Admitted in the future  *)

Lemma add_comm : forall n m : nat,
  n + m = m + n.
Proof.
    Admitted.

Lemma add_assoc : forall n m p : nat, 
    n + (m + p) = (n + m) + p. 
Proof. 
    Admitted.

Lemma mul_0_r : forall n:nat, 
    n * 0 = 0. 
Proof. 
    Admitted. 

Lemma plus_n_Sm : forall n m : nat, 
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

Lemma S_n_1 : forall n : nat, 
    S n = 1 + n. 
Proof.
    intros n. 
    - simpl. reflexivity. Qed.

Lemma n_x_S_k : forall n k : nat, 
    n * (S k) = n + n*k.
Proof. 
    intros n k. induction n as [| n' IHn'].
    - 
     simpl. reflexivity.
    - 
     simpl. 
     rewrite -> plus_n_Sm.
     rewrite -> IHn'.
     rewrite <- plus_n_Sm.
     rewrite -> add_assoc.
     rewrite -> add_assoc.
     assert (H: k + n' = n' + k).
     { 
      rewrite -> add_comm. reflexivity.
     }
     rewrite -> H.
     reflexivity. Qed.

    
Theorem add_shuffle3 : forall n m p : nat, 
    n + (m + p) = m + (n + p). 
Proof. 
    intros n m p. 
    rewrite <- add_comm. 
    assert (H: n + p = p + n).
     { rewrite add_comm. reflexivity. }
    rewrite -> H.
    rewrite -> add_assoc.
    reflexivity. Qed.

Theorem mul_comm : forall m n : nat, 
    m * n = n * m. 
Proof. 
    intros n m. 
    induction n as [| n' IHn'].
    - simpl. rewrite -> mul_0_r. reflexivity.
    - 
     rewrite -> n_x_S_k. 
     rewrite -> S_n_1. simpl. 
     rewrite -> add_comm. 
     rewrite -> IHn'. 
     rewrite -> add_comm. 
     reflexivity.
    Qed.