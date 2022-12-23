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

Fixpoint leb (n m : nat) : bool :=
    match n with 
    | O => true 
    | S n' => 
        match m with 
        | O => false 
        | S m' => leb n' m' 
        end 
    end. 

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

(*  ltb function tests natural numbers for less-than, yielding a boolean *)
Definition ltb (n m : nat) : bool :=
    negb (m <=? n).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.


Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed. 

Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed. 

Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed. 