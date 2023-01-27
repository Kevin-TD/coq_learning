(* Generalizing the definition of pairs, we can describe the type of lists of numbers like this: "A list is either the empty list or else a pair of a number and another list." *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

(* For example, here is a three-element list: *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(* As with pairs, it is more convenient to write lists in familiar programming notation. The following declarations allow us to use :: as an infix cons operator and square brackets as an "outfix" notation for constructing lists. *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* all equivalent *)
Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].


(* Next let's look at several functions for constructing and manipulating lists. First, the repeat function takes a number n and a count and returns a list of length count in which every element is n. *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(* The length function calculates the length of a list. *)
Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* The app function concatenates (appends) two lists. *)
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

(* Since app will be used extensively, it is again convenient to have an infix operator for it. *)
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
                    
(* Here are two smaller examples of programming with lists. The hd function returns the first element (the "head") of the list, while tl returns everything but the first element (the "tail"). Since the empty list has no first element, we pass a default value to be returned in that case. *)

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.
  
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.