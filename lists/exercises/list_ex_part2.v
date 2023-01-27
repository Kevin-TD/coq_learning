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
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Fixpoint remove_one (v : nat) (s: bag) : bag :=
    match s with 
    | nil => nil 
    | h :: t => match eqb v h with
        | true => t
        | false => h :: remove_one v t
        end
    end.
Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

(* EXERCISE *)
Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
    intros s. simpl. reflexivity. Qed.

(* The following lemma about leb might help you in the next exercise (it will also be useful in later chapters). *)
Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. Qed.


(* EXERCISE *)
(* the previous lemma ended up helping! *)
Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
    intros s. induction s as [| n s' IHs'].
    - simpl. reflexivity.
    - destruct n. 
     + simpl. rewrite -> leb_n_Sn. reflexivity.
     + simpl. rewrite -> IHs'. reflexivity.
    Qed.

(* EXERCISE *)
(*  An injective function is one-to-one: it maps distinct inputs to distinct outputs, without any collisions. *)
Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
    intros f H0 n1 n2 H1.
    rewrite -> H0.
    rewrite <- H1.
    rewrite <- H0.
    reflexivity.
    Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof. Admitted.

(* EXERCISE *)
Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. intros H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
  Qed.
  
  
  