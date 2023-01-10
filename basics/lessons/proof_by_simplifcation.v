(* let's turn to stating and proving properties of their behavior *)

(*  we've already started doing this: each Example in the previous sections makes a precise claim about the behavior of some function on some particular inputs. The proofs of these claims were always the same: use simpl to simplify both sides of the equation, then use reflexivity to check that both sides contain identical values. *)

(* The same sort of "proof by simplification" can be used to prove more interesting properties as well. For example, the fact that 0 is a "neutral element" for + on the left can be proved just by observing that 0 + n reduces to n no matter what n is -- a fact that can be read directly off the definition of plus. *)

Theorem plus_O_n : forall n : nat, 0 + n = n. 
Proof.
    intros n. simpl. reflexivity. Qed. 

(* This is a good place to mention that reflexivity is a bit more powerful than we have acknowledged. In the examples we have seen, the calls to simpl were actually not needed, because reflexivity can perform some simplification automatically when checking that two sides are equal; simpl was just added so that we could see the intermediate state -- after simplification but before finishing the proof. Here is a shorter proof of the theorem: *)

Theorem plus_O_n' : forall n : nat , 0 + n = n. 
Proof. 
    intros n. reflexivity. Qed.

(* Moreover, it will be useful to know that reflexivity does somewhat more simplification than simpl does -- for example, it tries "unfolding" defined terms, replacing them with their right-hand sides. The reason for this difference is that, if reflexivity succeeds, the whole goal is finished and we don't need to look at whatever expanded expressions reflexivity has created by all this simplification and unfolding; by contrast, simpl is used in situations where we may have to read and understand the new goal that it creates, so we would not want it blindly expanding definitions and leaving the goal in a messy state. *)
(* simpl is for readability purposes it seems *)

(* Theorem, Example, Lemma, Fact, and Remark are keywords that pretty much mean the same thing to Coq *)

(* Second, we've added the quantifier ∀ n:nat, so that our theorem talks about all natural numbers n. Informally, to prove theorems of this form, we generally start by saying "Suppose n is some number..." Formally, this is achieved in the proof by intros n, which moves n from the quantifier in the goal to a context of current assumptions. Note that we could have used another identifier instead of n in the intros clause, (though of course this might be confusing to human readers of the proof)*)

Theorem plus_O_n'' : forall n : nat, 0 + n = n. 
Proof. 
    intros m. reflexivity. Qed.

(* The keywords intros, simpl, and reflexivity are examples of tactics. A tactic is a command that is used between Proof and Qed to guide the process of checking some claim we are making. We will see several more tactics in the rest of this chapter and many more in future chapters. *)
(* Other similar theorems can be proved with the same pattern. *)
Theorem plus_1_1 : forall n : nat, 1 + n = S n. 
Proof. 
    intros n. reflexivity. Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
    intros n. reflexivity. Qed.

(*  You may want to add calls to simpl before reflexivity to see the simplifications that Coq performs on the terms before checking that they are equal.
 *)