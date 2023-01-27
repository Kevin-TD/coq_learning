Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

(* As with numbers, simple facts about list-processing functions can sometimes be proved entirely by simplification. For example, just the simplification performed by reflexivity is enough for this theorem... *)

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.


(* Also, as with numbers, it is sometimes helpful to perform case analysis on the possible shapes (empty or non-empty) of an unknown list. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

(* Notice that the as annotation on the destruct tactic here introduces two names, n and l', corresponding to the fact that the cons constructor for lists takes two arguments (the head and tail of the list it is constructing). *)
(* Usually, though, interesting theorems about lists require induction for their proofs. We'll see how to do this next. *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity. 
  Qed. 


(* reversing a list *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.



(* For something a bit more challenging than the proofs we've seen so far, let's prove that reversing a list does not change its length. Our first attempt gets stuck in the successor case... *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

(* So let's take the equation relating ++ and length that would have enabled us to make progress at the point where we got stuck and state it as a separate lemma. *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

(* also be needing this *)
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof. Admitted.

(* Now we can complete the original proof. *)
Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite add_comm.
    reflexivity.
Qed.

(* Search *)
(* We've seen that proofs can make use of other theorems we've already proved, e.g., using rewrite. But in order to refer to a theorem, we need to know its name! Indeed, it is often hard even to remember what theorems have been proven, much less what they are called.
Coq's Search command is quite helpful with this. Let's say you've forgotten the name of a theorem about rev. The command Search rev will cause Coq to display a list of all theorems involving rev. *)
Search rev.

(* Or say you've forgotten the name of the theorem showing that plus is commutative. You can use a pattern to search for all theorems involving the equality of two additions *)
Search (_ + _ = _ + _).

(* You'll see a lot of results there, nearly all of them from the standard library. To restrict the results, you can search inside a particular module: *)
(* Search (_ + _ = _ + _) inside Induction. *)

(* You can also make the search more precise by using variables in the search pattern instead of wildcards: *)
Search (?x + ?y = ?y + ?x).