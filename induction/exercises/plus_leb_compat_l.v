Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Lemma add_0_r : forall n : nat, 
    n + 0 = n. 
Proof. 
    Admitted. 

Lemma add_0_l : forall n : nat, 
    0 + n = n. 
Proof. 
    Admitted. 

Theorem n_leb_n_plus_m : forall n m : nat, 
    n <=? (n + m) = true. 
Proof.
    intros n m. 
    induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity. 
    Qed. 

Theorem plus_leb_compat_1 : forall n m p : nat, 
    n <=? m = true -> (p + n) <=? (p + m) = true. 
Proof. 
    intros n m p. 
    intros H.
    destruct n.
    - rewrite <- H. destruct p. 
     + simpl. reflexivity.
     + simpl. rewrite <- H. simpl. rewrite -> add_0_r. rewrite -> n_leb_n_plus_m. reflexivity.
    - induction p as [| p' IHp'].
     + rewrite -> add_0_l. rewrite -> add_0_l. rewrite -> H. reflexivity.
     + simpl. rewrite -> IHp'. reflexivity.
    Qed.

