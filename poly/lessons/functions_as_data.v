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

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).
Arguments pair {X} {Y}.
Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.
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
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.


(* Like most modern programming languages -- especially other "functional" languages, including OCaml, Haskell, Racket, Scala, Clojure, etc. -- Coq treats functions as first-class citizens, allowing them to be passed as arguments to other functions, returned as results, stored in data structures, etc. *)

(** Higher-Order Function **)

(* Functions that manipulate other functions are often called higher-order functions. Here's a simple one: *)
Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

(* The argument f here is itself a function (from X to X); the body of doit3times applies f three times to some value n. *)
Check @doit3times : forall X : Type, (X -> X) -> X -> X.

(** Filter **)
(* Here is a more useful higher-order function, taking a list of Xs and a predicate on X (a function from X to bool) and "filtering" the list, returning a new list containing just those elements for which the predicate returns true. *)
Fixpoint filter {X:Type} (test: X -> bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

(* For example, if we apply filter to the predicate even and a list of numbers l, it returns a list containing just the even members of l. *)
Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(* We can use filter to give a concise version of countevennumbers *)
Definition countevenmembers' (l:list nat) : nat :=
  length (filter even l).

(** Anonymous Functions **)

(* It is arguably a little sad, in the example just above, to be forced to define the function length_is_1 and give it a name just to be able to pass it as an argument to filter, since we will probably never use it again. Moreover, this is not an isolated example: when using higher-order functions, we often want to pass as arguments "one-off" functions that we will never use again; having to give each of these functions a name would be tedious.
Fortunately, there is a better way. We can construct a function "on the fly" without declaring it at the top level or giving it a name. *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed. 
(* The expression (fun n ⇒ n × n) can be read as "the function that, given a number n, yields n × n." *)

(* Here is the filter example, rewritten to use an anonymous function. *)
Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(** Map **)

(* Another handy higher-order function is called map. *)

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

(* It takes a function f and a list l = [n1, n2, n3, ...] and returns the list [f n1, f n2, f n3,...] , where f has been applied to each element of l in turn.  *)


(* Lists are not the only inductive type for which map makes sense. Here is a map for the option type: *)
Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.


(** Fold **)
(* An even more powerful higher-order function is called fold. This function is the inspiration for the "reduce" operation that lies at the heart of Google's map/reduce distributed programming framework. *)

Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(* Intuitively, the behavior of the fold operation is to insert a given binary operator f between every pair of elements in a given list. For example, fold plus [1;2;3;4] intuitively means 1+2+3+4. To make this precise, we also need a "starting element" that serves as the initial second input to f. So, for example,
fold plus [1;2;3;4] 0 yields  1 + (2 + (3 + (4 + 0))).
*)

(** Functions That Construct Functions **)
(* Most of the higher-order functions we have talked about so far take functions as arguments. Let's look at some examples that involve returning functions as the results of other functions. To begin, here is a function that takes a value x (drawn from some type X) and returns a function from nat to X that yields x whenever it is called, ignoring its nat argument. *)

Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.    (* constant fun !! 😁 *)