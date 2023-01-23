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

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with 
  | O => Z 
  | S n' => incr (nat_to_bin n')
  end. 
  
Lemma n_plus_0_eq_n : forall n : nat, 
  n + 0 = n. 
Proof. 
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
  Qed. 

Lemma plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m). 
Proof. 
  intros n. induction n as [| n' IHn']. 
  - simpl. reflexivity. 
  - induction m as [| m' IHm'].
    + simpl. rewrite -> IHn'. reflexivity. 
    + simpl. rewrite -> IHn'. reflexivity.
  Qed.

Lemma btn_incr_b_eq_S_btn_b : forall b : bin, 
  bin_to_nat (incr b) = S(bin_to_nat b).
Proof. 
  intros b. induction b as [| b' | b'].
  - reflexivity.
  - reflexivity.
  - 
  simpl. rewrite -> n_plus_0_eq_n. rewrite -> n_plus_0_eq_n. 
  rewrite -> IHb'. 
  rewrite -> plus_n_Sm. 
  reflexivity.
  Qed.

Theorem nat_bin_nat : forall n, 
  bin_to_nat (nat_to_bin n) = n.
Proof.
    intros n. induction n as [| n' IHn'].
    - reflexivity.
    - simpl. rewrite -> btn_incr_b_eq_S_btn_b. rewrite -> IHn'. reflexivity.
    Qed.