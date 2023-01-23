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

Fixpoint double (n:nat) :=
    match n with
    | O => O
    | S n' => S (S (double n'))
    end.
    

Lemma double_incr : forall n : nat,
    double (S n) = S (S (double n)).
Proof.
    intros n. induction n as [| n' IHn'].
    - reflexivity.
    - rewrite -> IHn'. simpl. reflexivity.
    Qed. 

    
Definition double_bin (b:bin) : bin :=
    match b with 
    | Z => Z
    | n => B0 n
    end.

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros b. induction b as [| b' | b'].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  Qed. 

Compute nat_to_bin(bin_to_nat (B1(B0(B1(B1(B0 Z)))))  ).
(* B1 B1 B0 Z turns into B1 B1 Z *)
(* B0 Z turns into Z *)
(* "equivalent bin" as in same value but not same representation, such as how n + 0 is equivalent to n but not representation wise *)