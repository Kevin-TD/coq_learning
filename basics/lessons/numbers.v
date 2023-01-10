(* https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html *)
Module NatPlayground. 
    (* unary # sys impl *)
    (* S is the successor *)
    Inductive nat : Type := 
        | O 
        | S (n : nat). 
    (* 0 is rep by O, 1 by S O, 2 by S(S O), and so *)

    Definition pred (n : nat) : nat :=
        match n with 
        | O => O 
        | S n' => n' 
        end. 
End NatPlayground.

(* now we will be using nat as defined in std lib *)
Check (S (S (S (S O)))). (* 4: nat *)
(* Coq prints nums in decimal form by default *)

Definition minustwo (n : nat) : nat :=
    match n with 
    | O => O 
    | S O => O 
    | S (S n') => n' 
    end. 
Compute (minustwo 4).

(* The constructor S has the type nat → nat, just like functions such as pred and minustwo *)
Check S : nat -> nat.
Check pred : nat -> nat. 
Check minustwo : nat -> nat.

(* functions like pred and minustwo are defined by giving computation rules -- e.g., the definition of pred says that pred 2 can be simplified to 1 -- while the definition of S has no such behavior attached. Although it is like a function in the sense that it can be applied to an argument, it does not do anything at all! It is just a way of writing down numbers. *)
(* Think about standard decimal numerals: the numeral 1 is not a computation; it's a piece of data *)

(*  to check that a number n is even, we may need to recursively check whether n-2 is even. Such functions are introduced with the keyword Fixpoint instead of Definition. *)
Fixpoint even (n : nat) : bool := 
    match n with 
    | O => true 
    | S O => false 
    | S (S n') => even n' 
    end. 

Definition odd (n : nat) : bool :=
    negb (even n). 
Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.

(*  in these proofs simpl actually has no effect on the goal -- all of the work is done by reflexivity. We'll discuss why that is shortly. *)

(* Naturally, we can also define multi-argument functions by recursion. *)
Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with 
    | O => m 
    | S n' => S (plus n' m)
    end. 
Compute (plus 3 2).

(* As a notational convenience, if two or more arguments have the same type, they can be written together *)
Fixpoint mult (n m : nat) : nat := 
    match n with 
    | O => O 
    | S n' => plus m (mult n' m)
    end. 

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

(* You can match two expressions at once by putting a comma between them: *)
Fixpoint minus (n m: nat) : nat := 
    match n, m with 
    | O , _ => O 
    | S _ , O => n 
    | S n', S m' => minus n' m' 
    end. 

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
    match power with  
    | O => S O 
    | S p => mult base (exp base p)
    end. 

(* Again, we can make numerical expressions easier to read and write by introducing notations for addition, multiplication, and subtraction. *)

Notation "x + y" := (plus x y)
    (at level 50, left associativity)
    : nat_scope.
Notation "x - y" := (minus x y)
    (at level 50, left associativity)
    : nat_scope.
Notation "x * y" := (mult x y)
    (at level 40, left associativity)
    : nat_scope.

(* The level, associativity, and nat_scope annotations control how these notations are treated by Coq's parser. The details are not important for present purposes, but interested readers can refer to the "More on Notation" section at the end of this chapter *)

(* When we say that Coq comes with almost nothing built-in, we really mean it: even equality testing is a user-defined operation! Here is a function eqb, which tests natural numbers for equality, yielding a boolean. Note the use of nested matches (we could also have used a simultaneous match, as we did in minus.) *)
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

(* Similarly, the leb function tests whether its first argument is less than or equal to its second argument, yielding a boolean. *)
Fixpoint leb (n m : nat) : bool :=
    match n with 
    | O => true 
    | S n' => 
        match m with 
        | O => false 
        | S m' => leb n' m' 
        end 
    end. 

(*  x = y is a logical claim -- a "proposition" -- that we can try to prove, while x =? y is an expression whose value (either true or false) we can compute. *)