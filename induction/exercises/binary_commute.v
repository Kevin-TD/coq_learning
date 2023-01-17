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




Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
    intros b. induction b as [| b' | b'].
    - reflexivity.
    - reflexivity.
    - rewrite -> btn_b1_b. simpl. rewrite -> IHb'. simpl.