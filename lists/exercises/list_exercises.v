Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.
Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Fixpoint nonzeros (l:natlist) : natlist := 
    match l with 
    | nil => nil 
    | O :: t => nonzeros t
    | n :: t => n :: nonzeros t
    end.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof. Admitted.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof. Admitted.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof. Admitted. 

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof. Admitted.

(* EXERCISE *)
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
    intros l. induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite -> IHl'. reflexivity.
    Qed.

(* EXERCISE *)
Theorem rev_app_distr : forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1'. rewrite -> app_assoc. reflexivity.
  Qed.

(* An involution is a function that is its own inverse. That is, applying the function twice yield the original input. *)
(* EXERCISE *)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
    intros l. induction l as [| n l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite -> rev_app_distr. rewrite -> IHl'. simpl. reflexivity. 
    Qed.

(* EXERCISE *)
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
    intros l1 l2 l3 l4. induction l1 as [| n l1' IHl1'].
    - simpl. rewrite -> app_assoc. reflexivity.
    - simpl. rewrite -> app_assoc. rewrite -> app_assoc. reflexivity.
    Qed.

(* ADDITIONAL LEMMAS *)
Lemma app_assoc_with_nat : forall n : nat, forall l1 l2 : natlist,
    (n :: l1) ++ l2 = n :: (l1 ++ l2).
Proof. 
    intros n. intros l1 l2. simpl. reflexivity.
    Qed.

Lemma nonzeros_Sn_l1 : forall n : nat, forall l1 : natlist, 
    nonzeros(S n :: l1) = S n :: nonzeros l1.
Proof.
    intros n. intros l1. simpl. reflexivity. Qed.

Lemma nonzeros_Sn_l1_l2 : forall n : nat, forall l1 l2 : natlist,
    nonzeros(S n :: l1 ++ l2) = S n :: nonzeros(l1 ++ l2).
Proof. 
    intros n. intros l1 l2. simpl. reflexivity. Qed.

Lemma Sn_app_l1_l2_assoc : forall n : nat, forall l1 l2 : natlist, 
    (S n :: l1) ++ l2 = S n :: (l1 ++ l2).
Proof. 
    intros n. intros l1 l2. simpl. reflexivity. Qed.

(* EXERCISE *)
Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
    intros l1 l2. induction l1 as [| n l1' IHl'].
    - simpl. reflexivity.
    - rewrite -> app_assoc_with_nat. destruct n.
     + simpl. rewrite -> IHl'. reflexivity.
     + rewrite -> nonzeros_Sn_l1_l2. 
       rewrite -> nonzeros_Sn_l1. 
       rewrite -> IHl'.
       rewrite -> Sn_app_l1_l2_assoc.
       reflexivity.
    Qed.
