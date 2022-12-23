(* let's turn to stating and proving properties of their behavior *)

(*  we've already started doing this: each Example in the previous sections makes a precise claim about the behavior of some function on some particular inputs. The proofs of these claims were always the same: use simpl to simplify both sides of the equation, then use reflexivity to check that both sides contain identical values. *)

(* The same sort of "proof by simplification" can be used to prove more interesting properties as well. For example, the fact that 0 is a "neutral element" for + on the left can be proved just by observing that 0 + n reduces to n no matter what n is -- a fact that can be read directly off the definition of plus. *)

Theorem plus_O_n : forall n : nat, 0 + n = n. 
Proof.
    intros n. simpl. reflexivity. Qed. 