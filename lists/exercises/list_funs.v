(* "especially useful" *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint nonzeros (l:natlist) : natlist := 
    match l with 
    | nil => nil 
    | O :: t => nonzeros t
    | S n :: t => S n :: nonzeros t
    end.

Example test_nonzeros:
    nonzeros [0;1;0;2;3;0;0] = [1;2;3].
simpl. reflexivity. Qed.


Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n:nat) : bool :=
    negb (even n).

Fixpoint oddmembers (l:natlist) : natlist :=
    match l with 
    | nil => nil
    | O :: t => oddmembers t 
    | S n :: t => match odd(S n) with
        | true => S n :: oddmembers t 
        | false => oddmembers t 
        end
    end.


Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Definition countoddmembers (l:natlist) : nat :=
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.