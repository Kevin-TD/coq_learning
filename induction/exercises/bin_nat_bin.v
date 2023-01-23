Inductive bin : Type :=
  | Z 
  | B0 (n : bin)
  | B1 (n : bin).

Definition double_bin (b:bin) : bin :=
    match b with 
    | Z => Z
    | n => B0 n
    end.


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

Fixpoint normalize (b:bin) : bin :=
    match b with 
    | Z => Z 
    | B0 Z => Z 
    | B0 n => B0(normalize(n))
    | B1 n => B1(normalize(n))
    end.

 Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  intros b. induction b as [| b' | b'].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  Qed. 

Lemma n_plus_0_eq_n : forall n : nat, 
  n + 0 = n. 
Proof. 
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
  Qed. 

Lemma l8r : forall b : bin, 
  bin_to_nat b + bin_to_nat b = 2 * bin_to_nat b.
Proof.
    intros b. simpl. rewrite -> n_plus_0_eq_n. reflexivity.
    Qed.

Lemma l9r : forall b : bin, 
    bin_to_nat(B0 b) = 2 * bin_to_nat b. 
Proof. 
    intros b. reflexivity.
    Qed.

Lemma add_assoc : forall n m p : nat, 
    n + (m + p) = (n + m) + p. 
Proof. Admitted.

Lemma l12r : forall b : bin, 
  nat_to_bin(2 * bin_to_nat b) = double_bin(nat_to_bin(bin_to_nat b)).
Proof.
  intros b. induction b as [| b' | b'].
  - simpl. reflexivity.
  - simpl. rewrite -> n_plus_0_eq_n. rewrite -> n_plus_0_eq_n. rewrite -> l8r. rewrite <- l9r. rewrite -> l8r.

Lemma kk : forall b : bin, 
    nat_to_bin (bin_to_nat (B0 b)) = double_bin(nat_to_bin (bin_to_nat b)).
Proof. 
    intros b. induction b as [| b' | b'].
    - simpl. reflexivity.
    - simpl. rewrite -> n_plus_0_eq_n. rewrite -> n_plus_0_eq_n. rewrite -> l8r. rewrite <- l9r. rewrite -> IHb'. rewrite -> l8r. rewrite ->  l9r.

(* Lemma jj : forall b : bin, 
    normalize(B0 b) = normalize(double_bin(normalize(b))).
Proof. 
  intros b. induction b as [| b' | b'].
  - reflexivity.
  -  *)

(* Lemma l10r : forall b : bin, 
    double_bin(normalize b) = normalize(double_bin b).
Proof. 
  intros b. induction b as [| b' | b'].
  - reflexivity.
  - *)

(* Lemma l11r : forall b : bin, 
    normalize(normalize b) = normalize b. 
Proof. 
  intros b. induction b as [| b' | b'].
  - simpl. reflexivity.
  -  *)



Lemma l13r : forall b : bin, 
  incr(double_bin (b)) = B1 b.
Proof.
  intros b. induction b as [| b' | b'].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  Qed.

Theorem bin_nat_bin : forall b, 
    nat_to_bin (bin_to_nat b) = normalize b.
Proof.
    intros b. induction b as [| b' | b'].
    - reflexivity.
    - rewrite -> kk. rewrite -> IHb'. rewrite -> jj. 
    rewrite -> l10r. rewrite -> l11r. reflexivity.
    - simpl. rewrite -> n_plus_0_eq_n. rewrite -> l8r. rewrite <- IHb'.
    rewrite -> l12r. rewrite -> IHb'. rewrite -> l13r. reflexivity. 
    Qed.
