(* "especially useful" *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Definition bag := natlist.

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
  
Fixpoint count (v : nat) (s : bag) : nat :=
    match s with 
    | nil => O 
    | h :: t => match eqb v h with 
        | true => 1 + count v t
        | false => count v t
        end
    end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Definition sum : bag -> bag -> bag := app.

Definition add (v : nat) (s : bag) : bag :=
  v :: s.

Lemma eqb_n_n_true : forall n : nat,
  eqb n n = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
  Qed.

Theorem add_inc_count : forall v : nat, forall s : bag, 
  count v (add v s)  = 1 + count v s.
Proof. 
  intros v s. destruct s.  
  - simpl. 
    rewrite -> eqb_n_n_true. 
    reflexivity.
  - simpl.
    rewrite -> eqb_n_n_true.
    reflexivity.
  Qed.
