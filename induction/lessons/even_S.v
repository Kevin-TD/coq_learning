Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Lemma negb_negb_b : forall b : bool, 
    negb (negb b) = b.
Proof. 
    intros n. destruct n.
    - simpl. reflexivity.
    - simpl. reflexivity.
    Qed.

Theorem even_S : forall n : nat, 
    even (S n) = negb (even n).
Proof. 
    intros n. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - 
     rewrite -> IHn'. simpl. 
     rewrite -> negb_negb_b. reflexivity.
    Qed.