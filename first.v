Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday). 
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed. (* The assertion we've just made 
can be proved by observing that both sides of the equality 
evaluate to the same thing *)


(* def bool type *)

Inductive bool : Type :=
  | true 
  | false. 

(* functions over booleans *)
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

(* using Notation *) 
Notation "x && y" := (andb x y). 
Notation "x || y" := (orb x y). 
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* conditional expressions *) 
Definition negb' (b:bool) : bool :=
  if b then false 
  else true. 





