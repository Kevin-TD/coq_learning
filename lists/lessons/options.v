https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html

(* Suppose we want to write a function that returns the nth element of some list. If we give it type nat → natlist → nat, then we'll have to choose some number to return when the list is too short... *)

(* This solution is not so good: If nth_bad returns 42, we can't tell whether that value actually appears on the input without further processing. A better alternative is to change the return type of nth_bad to include an error value as a possible outcome. We call this type natoption. *)

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

(* We can then change the above definition of nth_bad to return None when the list is too short and Some a when the list has enough members and a appears at position n. We call this new function nth_error to indicate that it may result in an error. As we see here, constructors of inductive definitions can be capitalized. *)
Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.
  
(* The function below pulls the nat out of a natoption, returning a supplied default in the None case. *)
Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.