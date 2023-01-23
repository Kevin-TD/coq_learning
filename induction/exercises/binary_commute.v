Inductive bin : Type :=
  | Z 
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m : bin) : bin :=
   match m with 
   | Z => B1 Z 
   | B0 n => B1 n  
   | B1 n => B0 (incr n)
   end. 
  
Fixpoint bin_to_nat (m:bin) : nat :=
  match m with 
  | Z => O 
  | B0 n => 2 * bin_to_nat n 
  | B1 n => 1 + 2 * bin_to_nat n 
  end. 

Lemma add_shuffle3 : forall n m p : nat, 
    n + (m + p) = m + (n + p). 
Proof. Admitted.


Lemma one_plus_btn_b : forall b : bin, 
  1 + bin_to_nat b = S (bin_to_nat b). 
Proof.
  intros b. induction b as [| b' | b'].
  - reflexivity.
  - reflexivity.
  - 
  assert (H: bin_to_nat(B1 b') = 1 + 2 * bin_to_nat b'). 
   { simpl. reflexivity. }
  rewrite -> H. simpl. reflexivity.
  Qed.
  
Lemma btn_b1_b : forall b : bin, 
  bin_to_nat(B1 b) = 1 + 2 * bin_to_nat b. 
Proof. 
  intros b. 
  - reflexivity.
  Qed. 


Lemma n_plus_0_eq_n : forall n : nat, 
  n + 0 = n. 
Proof. 
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
  Qed. 

Lemma btn_b_plus_0 : forall b : bin, 
  bin_to_nat b + 0 = bin_to_nat b.
Proof.
  intros b. induction b as [| b' | b'].
  - reflexivity.
  - rewrite -> n_plus_0_eq_n. reflexivity.
  - rewrite -> n_plus_0_eq_n. reflexivity.
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

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
    intros b. induction b as [| b' | b'].
    - reflexivity.
    - reflexivity.
    - rewrite -> btn_b1_b. simpl. rewrite -> IHb'. simpl. rewrite -> btn_b_plus_0. rewrite <-plus_n_Sm. reflexivity.
    Qed. 