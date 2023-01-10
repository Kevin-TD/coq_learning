Theorem plus_id_example : forall n m : nat,  
    n = m -> n + n = m + n. 
(* to prove this, we assume n = m, and we can replace n with m in the goal statement and obtain an equality with the same expression on both sides. The tactic that tells Coq to perform this replacement is called rewrite. *)
Proof. 
    (* move both quantifiers into context *)
    intros n m. 
    (* move the hypothesis (n = m)  into context *)
    intros H. 
    (* rewrite the goal using the hypothesis *)
    rewrite -> H. 
    (* tells Coq to rewrite the current goal (n + n = m + m) by replacing the left side of the equality hypothesis H with the right side. *)
    (* The arrow symbol in the rewrite has nothing to do with implication: it tells Coq to apply the rewrite from left to right. In fact, you can omit the arrow, and Coq will default to rewriting in this direction. To rewrite from right to left, you can use rewrite <- *)

    (* results in m + m = m + m *)
    (* use reflexivity to affirm that m + m is same as m + m *)

    reflexivity. Qed. 

Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
    Admitted.
 (* The Admitted command tells Coq that we want to skip trying to prove this theorem and just accept it as a given. This can be useful for developing longer proofs, since we can state subsidiary lemmas that we believe will be useful for making some larger argument, use Admitted to accept them on faith for the moment, and continue working on the main argument until we are sure it makes sense; then we can go back and fill in the proofs we skipped. Be careful, though: every time you say Admitted you are leaving a door open for total nonsense to enter Coq's nice, rigorous, formally checked world! *)

 (* The Check command can also be used to examine the statements of previously declared lemmas and theorems. The two examples below are lemmas about multiplication that are proved in the standard library.  *)

 Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)

Check mult_n_Sm.
(*  forall n m : nat, n * m + n = n * S m *)

(* We can use the rewrite tactic with a previously proved theorem instead of a hypothesis from the context. If the statement of the previously proved theorem involves quantified variables, as in the example below, Coq tries to instantiate them by matching with the current goal. *)

Theorem mult_n_0_m_0 : forall p q : nat, 
    (p * 0) + (q * 0) = 0. 

Proof. 
    intros p q. 
    rewrite <- mult_n_O.
    rewrite <- mult_n_O. 
    reflexivity. Qed. 
