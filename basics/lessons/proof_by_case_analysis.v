(* Of course, not everything can be proved by simple calculation and rewriting *)

(*
Theorem plus_1_neq_0_firsttry : ∀ n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.
*) 

(* To make progress, we need to consider the possible forms of n separately. If n is O, then we can calculate the final result of (n + 1) =? 0 and check that it is, indeed, false. And if n = S n' for some n', then, although we don't know exactly what number n + 1 represents, we can calculate that, at least, it will begin with one S, and this is enough to calculate that, again, (n + 1) =? 0 will yield false. *)
(* The tactic that tells Coq to consider, separately, the cases where n = O and where n = S n' is called destruct. *)

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

Theorem plus_1_neq_0 : forall n : nat,
    (n + 1) =? 0 = false. 
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

(* The destruct generates two subgoals, which we must then prove, separately, in order to get Coq to accept the theorem. *)
(* The annotation "as [| n']" is called an intro pattern. It tells Coq what variable names to introduce in each subgoal. In general, what goes between the square brackets is a list of lists of names, separated by |. In this case, the first component is empty, since the O constructor is nullary (it doesn't have any arguments). The second component gives a single name, n', since S is a unary constructor. *)

(* In each subgoal, Coq remembers the assumption about n that is relevant for this subgoal -- either n = 0 or n = S n' for some n'. The eqn:E annotation tells destruct to give the name E to this equation. Leaving off the eqn:E annotation causes Coq to omit these assumptions in the subgoals. *)

(* The - signs on the second and third lines are called bullets, and they mark the parts of the proof that correspond to the two generated subgoals. The part of the proof script that comes after a bullet is the entire proof for the corresponding subgoal. In this example, each of the subgoals is easily proved by a single use of reflexivity, which itself performs some simplification -- e.g., the second one simplifies (S n' + 1) =? 0 to false by first rewriting (S n' + 1) to S (n' + 1), then unfolding eqb, and then simplifying the match. *)
(* Marking cases with bullets is optional: if bullets are not present, Coq simply asks you to prove each subgoal in sequence, one at a time. But it is a good idea to use bullets. For one thing, they make the structure of a proof apparent, improving readability. Also, bullets instruct Coq to ensure that a subgoal is complete before trying to verify the next one, preventing proofs for different subgoals from getting mixed up. These issues become especially important in large developments, where fragile proofs lead to long debugging sessions. *)

(* The destruct tactic can be used with any inductively defined datatype. For example, we use it next to prove that boolean negation is involutive -- i.e., that negation is its own inverse. *)

Theorem negb_involutive : forall b : bool, 
  negb (negb b) = b. 
Proof. 
  intros b. destruct b eqn:E. 
  - reflexivity. 
  - reflexivity. Qed. 

(* Note that the destruct here has no as clause because none of the subcases of the destruct need to bind any variables, so there is no need to specify any names. In fact, we can omit the as clause from any destruct and Coq will fill in variable names automatically. This is generally considered bad style, since Coq often makes confusing choices of names when left to its own devices. *)

(* It is sometimes useful to invoke destruct inside a subgoal, generating yet more proof obligations. In this case, we use different kinds of bullets to mark goals on different "levels." For example:
 *)

Theorem andb_commutative : forall b c, andb b c = andb c b. 
Proof. 
  intros b c. destruct b eqn:Eb. 
  - destruct c eqn:Ec. 
    + reflexivity.
    + reflexivity. 
  - destruct c eqn:Ec. 
    + reflexivity. 
    + reflexivity. Qed. 

(* asteriks can be used or any repetition of a bullet symbol (e.g., -- or [asterik][asterik][asterik] *)
(* We can also enclose sub-proofs in curly braces *)

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof.
  intros b c d. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
  - destruct c eqn:Ec.
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
    { destruct d eqn:Ed.
      - reflexivity.
      - reflexivity. }
Qed.

(* many proofs perform case analysis on a variable right after introducing it:  intros x y. destruct y as [|y] eqn:E.  *)
(* This pattern is so common that Coq provides a shorthand for it *)

Theorem plus_1_neq_0' : forall n : nat, 
  (n + 1) =? 0 = false. 
Proof. 
  intros [|n]. 
  - reflexivity. 
  - reflexivity. Qed. 

(* If there are no constructor arguments that need names, we can just write [] to get the case analysis. *)

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** Question: how does Coq's decreasing analysis make it so you have to right functions in weird ways? What would a solution to the 2 star decreasing exericse look like?  *)