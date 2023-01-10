Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.


Lemma S_double_n : forall n, 
    S(double n) = 1 + double n.
Proof. 
    intros n. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. reflexivity. 
    Qed. 

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

Lemma double_plus : forall n, 
    double n = n + n. 
Proof. 
    intros n. induction n as [| n' IHn'].
    - reflexivity.
    - 
     simpl. 
     rewrite -> S_double_n. 
     rewrite -> IHn'. simpl. 
     rewrite -> plus_n_Sm. reflexivity.
    Qed.