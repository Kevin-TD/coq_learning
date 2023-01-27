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

Fixpoint remove_one (v : nat) (s: bag) : bag :=
    match s with 
    | nil => nil 
    | h :: t => match eqb v h with
        | true => t
        | false => h :: remove_one v t
        end
    end.

Example test_remove_one1:
    count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with 
    | nil => nil 
    | h :: t => match eqb v h with
        | true => remove_all v t
        | false => h :: remove_all v t
        end
    end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.


Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Fixpoint member (v : nat) (s : bag) : bool :=
  match s with 
  | nil => false 
  | h :: t => match eqb h v with
    | true => true
    | false => member v t
    end
  end.
  
Fixpoint included (s1 : bag) (s2 : bag) : bool :=
    match s1 with
    | nil => true 
    | h :: t => match member h s2 with
        | true => included t (remove_one h s2)
        | false => false 
        end
    end.

(* Question: is there a more precise syntax than  
  match true|false with   
  | true => ... 
  | false => ... 

*)


Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.