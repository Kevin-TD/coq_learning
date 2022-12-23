Check true. (* ===> true : bool *)

(* If the expression after Check is followed by a 
colon and a type, 
Coq will verify that the type of the expression matches 
the given type and halt with an error if not. *) 

Check true
  : bool.
Check (negb true)
  : bool.

(* Functions like negb itself are also data values, 
just like true and false.
Their types are called function types, 
and they are written with arrows. *) 

Check negb
  : bool => bool.

(* can be read, "
Given an input of type bool, this function produces 
an output of type bool." Similarly, 
the type of andb, written bool \u2192 bool \u2192 bool, 
can be read, "Given two inputs, each of type bool, 
this function produces an output of type bool." *) 

(* Inductive is an enumerated type, 
their defs explicitly enumerate a finite 
set of elements, called constructors *) 


(* constructor takes arg *) 
Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).


Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.
  (* Since the primary constructor
 takes an argument, a pattern matching primary 
should include either a variable 
(as above -- note that we can choose its name freely) *)

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.
(* he wildcard pattern _ has the same 
effect as the dummy pattern variable p 
in the definition of monochrome.) *)




