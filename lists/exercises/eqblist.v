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

Definition and (b1 b2 : bool) : bool := 
    match b1 with 
    | false => false 
    | true => match b2 with 
        | false => false 
        | true => true
        end 
    end.

Lemma eqb_n_n_true : forall n : nat,
  eqb n n = true.
Proof. Admitted.

(* EXERCISE *)
Fixpoint eqblist (l1 l2 : natlist) : bool :=
    match l1 with 
    | nil => match l2 with 
        | nil => true 
        | _ => false
        end
    | h :: t => match l2 with 
        | nil => false 
        | m :: n => and (eqb h m) (eqblist t n)
        end 
    end.

Example test_eqblist1 :
    (eqblist nil nil = true).
Proof. simpl. reflexivity. Qed.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. simpl. reflexivity. Qed.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. simpl. reflexivity. Qed.

(* EXERCISE *)
Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
    intros l. induction l as [| n l' IHl'].
    - simpl. reflexivity. 
    - simpl. 
      rewrite -> IHl'. 
      rewrite -> eqb_n_n_true. 
      rewrite <- IHl'. simpl. 
      reflexivity.
    Qed.