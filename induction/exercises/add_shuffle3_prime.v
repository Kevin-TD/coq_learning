Lemma add_comm : forall n m : nat,
  n + m = m + n.
Proof. Admitted.

Lemma add_assoc : forall n m p : nat, 
    n + (m + p) = (n + m) + p. 
Proof. Admitted.

Theorem add_shuffle3' : forall n m p : nat, 
    n + (m + p) = m + (n + p). 
Proof. 
    intros n m p. 
    rewrite <- add_comm. 
    replace (n + p) with (p + n).
    - rewrite -> add_assoc. reflexivity.
    - rewrite -> add_comm. reflexivity.
    Qed.