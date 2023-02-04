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

Definition fst {X Y : Type} (p : X*Y) : X :=
    match p with
    | pair x y => x
    end.
    
Definition snd {X Y : Type} (p : X*Y) : Y :=
    match p with
    | pair x y => y
    end.

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
Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.
Fixpoint fold {X Y: Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.
Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
    match l with
    | [] => None
    | a :: l' => if n =? O then Some a else nth_error l' (pred n)
    end.



(* Many common functions on lists can be implemented in terms of fold. For example, here is an alternative definition of length: *)
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.


(* additional lemma *)
Lemma fold_length_n_l : forall X (l : list X), forall n : X, 
    fold_length(n :: l) = 1 + fold_length(l).
Proof.
    intros X l n. induction l as [| k l' IHl'].
    - reflexivity.
    - reflexivity.  (* incredibly aggressive reflexivity *)
    Qed.
    
(* exercise *)
Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
    intros X l. induction l as [| n l' IHl'].
    - reflexivity.  (* aggressive reflexivity *)
    - simpl. rewrite <- IHl'. rewrite -> fold_length_n_l. reflexivity.
    Qed.

(* exercise *)
Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold  (fun x l => (f x) :: l) l [].

Theorem fold_map_correct : forall X Y (l : list X), forall  f : X -> Y,
  fold_map f l = map f l.
Proof. 
  intros X Y l f. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. reflexivity.
  Qed.
  

(* Currying *)
(* The type X → Y → Z can be read as describing functions that take two arguments, one of type X and another of type Y, and return an output of type Z. Strictly speaking, this type is written X → (Y → Z) when fully parenthesized. That is, if we have f : X → Y → Z, and we give f an input of type X, it will give us as output a function of type Y → Z. If we then give that function an input of type Y, it will return an output of type Z. That is, every function in Coq takes only one input, but some functions return a function as output. This is precisely what enables partial application, as we saw above with plus3. *)

(* By contrast, functions of type X × Y → Z -- which when fully parenthesized is written (X × Y) → Z -- require their single input to be a pair. Both arguments must be given at once; there is no possibility of partial application.
It is possible to convert a function between these two types. Converting from X × Y → Z to X → Y → Z is called currying, in honor of the logician Haskell Curry. Converting from X → Y → Z to X × Y → Z is called uncurrying.
We can define currying as follows: *)

Definition curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z := 
  f (x, y).


(* As an exercise, define its inverse, prod_uncurry. Then prove the theorems below to show that the two are inverses. *)
Definition uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z :=
  f (fst p) (snd p).

Check @curry. 
Check @uncurry.

(* exercise *)
Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  curry (uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y. reflexivity. 
  Qed.

(* exercise *)
Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  uncurry (curry f) p = f p.
Proof.
  intros X Y Z f p. destruct p. reflexivity. 
  Qed.


Lemma nth_error_l_length_l : forall (X : Type), forall (l : list X), 
  nth_error l (length l) = None.
Proof. 
  intros X l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity. 
  Qed.

(* exercise *)
Theorem nth_error_l_n : forall (X : Type), forall (l : list X), forall (n : nat),
  length l = n -> nth_error l n = None.
Proof.
  intros X l n H. destruct l.
  - reflexivity.
  - rewrite <- H. simpl. rewrite -> nth_error_l_length_l. reflexivity. 
  Qed.