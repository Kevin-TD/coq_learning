(* In this chapter we continue our development of basic concepts of functional programming. The critical new ideas are polymorphism (abstracting functions over the types of the data they manipulate) and higher-order functions (treating functions as data). We begin with polymorphism. *)

(* For the last chapter, we've been working with lists containing just numbers. Obviously, interesting programs also need to be able to manipulate lists with elements from other types -- lists of booleans, lists of lists, etc. We could just define a new inductive datatype for each of these ... but this would quickly become tedious, partly because we have to make up different constructor names for each datatype, but mostly because we would also need to define new versions of all our list manipulating functions (length, rev, etc.) and all their properties (rev_length, app_assoc, etc.) for each new datatype definition.*)
(* To avoid all this repetition, Coq supports polymorphic inductive type definitions. For example, here is a polymorphic list datatype. *)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(* What sort of thing is list itself? A good way to think about it is that the definition of list is a function from Types to Inductive definitions; or, to put it more concisely, list is a function from Types to Types. For any particular type X, the type list X is the Inductively defined set of lists whose elements are of type X. *)
Check list : Type -> Type.

(* The X in the definition of list automatically becomes a parameter to the constructors nil and cons -- that is, nil and cons are now polymorphic constructors; when we use them, we must now provide a first argument that is the type of the list they are building. For example, nil nat constructs the empty list of type nat. *)
Check (nil nat) : list nat.

(* Similarly, cons nat adds an element of type nat to a list of type list nat. Here is an example of forming a list containing just the natural number 3. *)
Check (cons nat 3 (nil nat)) : list nat.

(* What might the type of nil be? We can read off the type list X from the definition, but this omits the binding for X which is the parameter to list. Type → list X does not explain the meaning of X. (X : Type) → list X comes closer. Coq's notation for this situation is ∀ X : Type, list X. *)
Check nil : forall X : Type, list X.

(* Similarly, the type of cons from the definition looks like X → list X → list X, but using this convention to explain the meaning of X results in the type ∀ X, X → list X → list X. *)
Check cons : forall X : Type, X -> list X -> list X.

(* Having to supply a type argument for every single use of a list constructor would be rather burdensome; we will soon see ways of reducing this annotation burden. *)
Check (cons nat 2 (cons nat 1 (nil nat)))
      : list nat.

(* We can now go back and make polymorphic versions of all the list-processing functions that we wrote before. Here is repeat, for example: *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

(* As with nil and cons, we can use repeat by applying it first to a type and then to an element of this type (and a number): *)
Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

(* To use repeat to build other kinds of lists, we simply instantiate it with an appropriate type parameter: *)
Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.


(** Type Annotation Inference **)
(* Let's write the definition of repeat again, but this time we won't specify the types of any of the arguments. Will Coq still accept it? *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.
(* Indeed it will. Let's see what type Coq has assigned to repeat'... *)
Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.
(* It has exactly the same type as repeat. Coq was able to use type inference to deduce what the types of X, x, and count must be, based on how they are used. For example, since X is used as an argument to cons, it must be a Type, since cons expects a Type as its first argument; matching count with 0 and S means it must be a nat; and so on. *)
(* This powerful facility means we don't always have to write explicit type annotations everywhere, although explicit type annotations can still be quite useful as documentation and sanity checks, so we will continue to use them much of the time. *)

(** Type Argument Synthesis **)

(* To use a polymorphic function, we need to pass it one or more types in addition to its other arguments. For example, the recursive call in the body of the repeat function above must pass along the type X. But since the second argument to repeat is an element of X, it seems entirely obvious that the first argument can only be X -- why should we have to write it explicitly? *)
(* Fortunately, Coq permits us to avoid this kind of redundancy. In place of any type argument we can write a "hole" _, which can be read as "Please try to figure out for yourself what belongs here." More precisely, when Coq encounters a _, it will attempt to unify all locally available information -- the type of the function being applied, the types of the other arguments, and the type expected by the context in which the application appears -- to determine what concrete type should replace the _. *)

(* This may sound similar to type annotation inference -- and, indeed, the two procedures rely on the same underlying mechanisms. Instead of simply omitting the types of some arguments to a function, we can also replace the types with holes to tell Coq to attempt to infer the missing information. *)
Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(* In this instance, we don't save much by writing _ instead of X. But in many cases the difference in both keystrokes and readability is nontrivial. For example, suppose we want to write down a list containing the numbers 1, 2, and 3. Instead of this... *)
Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
(* ...we can use holes to write this: *)
Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(** Implicit Arguments **)
(* In fact, we can go further and even avoid writing _'s in most cases by telling Coq always to infer the type argument(s) of a given function.
The Arguments directive specifies the name of the function (or constructor) and then lists the (leading) argument names to be treated as implicit, each surrounded by curly braces. *)
Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

(* Now we don't have to supply any type arguments at all in the example: *)
Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(* Alternatively, we can declare an argument to be implicit when defining the function itself, by surrounding it in curly braces instead of parens. For example: *)
Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.
Compute repeat''' 3 3.

(* We will use the latter style whenever possible, but we will continue to use explicit Argument declarations for Inductive constructors. The reason for this is that marking the parameter of an inductive type as implicit causes it to become implicit for the type itself, not just for its constructors. For instance, consider the following alternative definition of the list type: *)
Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').
(* Because X is declared as implicit for the entire inductive definition including list' itself, we now have to write just list' whether we are talking about lists of numbers or booleans or anything else, rather than list' nat or list' bool or whatever; this is a step too far. *)
Compute cons' 2 (cons' 2 (cons' 3 nil')).
(* Let's finish by re-implementing a few other standard list functions on our new polymorphic lists... *)

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

(** Supplying Type Arguments Explicitly **)

(* One small problem with declaring arguments to be implicit is that, once in a while, Coq does not have enough local information to determine a type argument; in such cases, we need to tell Coq that we want to give the argument explicitly just this time. For example, suppose we write this: *)
Fail Definition mynil := nil.
(* (The Fail qualifier that appears before Definition can be used with any command, and is used to ensure that that command indeed fails when executed. If the command does fail, Coq prints the corresponding error message, but continues processing the rest of the file.) *)

(* Here, Coq gives us an error because it doesn't know what type argument to supply to nil. We can help it by providing an explicit type declaration (so that Coq has more information available when it gets to the "application" of nil): *)
Definition mynil : list nat := nil.

(* Alternatively, we can force the implicit arguments to be explicit by prefixing the function name with @. *)

(* Check @nil : forall X : Type, list X. *)
Definition mynil' := @nil nat.

(* Using argument synthesis and implicit arguments, we can define convenient notation for lists, as before. Since we have made the constructor type arguments implicit, Coq will know to automatically infer these when we use the notations. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* Now lists can be written just the way we'd hope: *)
Definition list123''' := [1; 2; 3].
