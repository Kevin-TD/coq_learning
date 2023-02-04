Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X}.

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

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
                     
(* Following the same pattern, the definition for pairs of numbers that we gave in the last chapter can be generalized to polymorphic pairs, often called products: *)
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y}.

(* As with lists, we make the type arguments implicit and define the familiar concrete notation. *)
Notation "( x , y )" := (pair x y).
(* We can also use the Notation mechanism to define the standard notation for product types (i.e., the types of pairs): *)
Notation "X * Y" := (prod X Y) : type_scope.
(* The annotation : type_scope tells Coq that this abbreviation should only be used when parsing types, not when parsing expressions. This avoids a clash with the multiplication symbol. *)

(* It is easy at first to get (x,y) and X×Y confused. Remember that (x,y) is a value built from two other values, while X×Y is a type built from two other types. If x has type X and y has type Y, then (x,y) has type X×Y. *)

(* The first and second projection functions now look pretty much as they would in any functional programming language. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.
Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(* The following function takes two lists and combines them into a list of pairs. In other functional languages, it is often called zip; we call it combine for consistency with Coq's standard library. *)
Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.
Compute (combine [1;2] [false;false]). (* [(1, false); (2, false)] *)
Check @combine. (* forall X Y : Type, list X -> list Y -> list (X * Y) *)