(* pair constructing *)

Inductive natprod : Type :=
  | pair (n1 n2 : nat).

(* getting first or second *)
Definition fst (p : natprod) : nat :=
    match p with
    | pair x y => x
    end.
Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

Compute fst(pair 1 2). (* 1 *)

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(* Note that pattern-matching on a pair (with parentheses: (x, y)) is not to be confused with the "multiple pattern" syntax (with no parentheses: x, y) that we have seen previously. The above examples illustrate pattern matching on a pair with elements x and y, whereas, for example, the definition of minus in Basics performs pattern matching on the values n and m: *)

Fixpoint minus (n m : nat) : nat :=
    match n, m with
        | O   , _    => O
        | S _ , O    => n
        | S n', S m' => minus n' m'
    end.

(* The distinction is minor, but it is worth knowing that they are not the same.  *)

(* Now let's try to prove a few simple facts about pairs.
If we state properties of pairs in a slightly peculiar way, we can sometimes complete their proofs with just reflexivity (and its built-in simplification): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof. 
    reflexivity. Qed.

(* But just reflexivity is not enough if we state the lemma in the most natural way: *)
Theorem surjective_pairing_stuck : forall (p : natprod),
    p = (fst p, snd p).
Proof.
    simpl. (* Doesn't reduce anything! *) Abort.

(* Instead, we need to expose the structure of p so that simpl can perform the pattern match in fst and snd. We can do this with destruct. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
    intros p. destruct p as [n m].
    simpl. reflexivity. Qed.

(* Notice that, unlike its behavior with nats, where it generates two subgoals, destruct generates just one subgoal here. That's because natprods can only be constructed in one way. *)