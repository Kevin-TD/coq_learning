Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Fixpoint eqb (n m : nat) : bool :=
match n with
| O => match m with
        | O => true
        | S m' => false
        end
| S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
end.


Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem leb_refl : forall n : nat, 
    (n <=? n) = true. 
Proof. 
    intros n. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
    Qed. 

Theorem zero_neqb_S : forall n : nat, 
    0 =? (S n) = false. 
Proof. 
    intros n. destruct n.
    - reflexivity.
    - reflexivity.
    Qed. 

Theorem andb_false_r : forall b : bool, 
    andb b false = false. 
Proof. 
    intros b. destruct b. 
    - reflexivity.
    - reflexivity.
    Qed. 

Theorem S_neqb_0 : forall n : nat, 
    (S n) =? 0 = false. 
Proof. 
    intros n. destruct n. 
    - reflexivity.
    - reflexivity. Qed.

Lemma add_0_r : forall n : nat, 
    n + 0 = n.
Proof. Admitted. 

Theorem mult_1_1 : forall n : nat, 
    1 * n = n. 
Proof. 
    intros n. induction n as [| n' IHn']. 
    - reflexivity.
    - simpl. rewrite -> add_0_r. reflexivity.
    Qed. 

Theorem all3_spec : forall b c : bool, 
    orb (andb b c)(orb (negb b)(negb c)) = true. 
    (* b&&c || (~b||~c) == true *)
Proof. 
    intros b c. destruct b. 
    - destruct c. 
     + reflexivity.
     + reflexivity.
    - destruct c. 
     + reflexivity.
     + reflexivity.
    Qed. 

Lemma add_assoc : forall n m p : nat, 
    n + (m + p) = (n + m) + p. 
Proof. Admitted.

Theorem mult_plus_distr_r : forall n m p : nat, 
    (n + m) * p = (n * p) + (m * p). 
Proof. 
    intros n m p. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. rewrite -> add_assoc. reflexivity.
    Qed. 

Theorem mult_assoc : forall n m p : nat, 
    n * (m * p) = (n * m) * p. 
Proof. 
    intros n m p. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> mult_plus_distr_r. rewrite -> IHn'. reflexivity.
    Qed. 