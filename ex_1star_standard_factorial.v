Module Ex1. 
Fixpoint factorial (n:nat) : nat :=
    match n with 
    | 0 => 1
    | S n => (n+1) * factorial (n)
    end.


Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed. 

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed. 


End Ex1. 