(*  Induction - If P(n) is some proposition involving a natural number n and we want to show that P holds for all numbers n, we can reason like this:
show that P(O) holds;
show that, for any n', if P(n') holds, then so does P(S n');
conclude that P(n) holds for all n. *)


(* In Coq, the steps are the same: we begin with the goal of proving P(n) for all n and break it down (by applying the induction tactic) into two separate subgoals: one where we must show P(O) and another where we must show P(n') → P(S n'). Here's how this works for the theorem at hand: *)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. Qed.

(* IHn' reads "induction hypothesis for n'" *)

Theorem minus_n_n : forall n, 
  minus n n = 0. 
Proof. 
  intros n. induction n as [| n' IHn']. 
  - (* n = 0 *)
    simpl. reflexivity. 
  - (* n = S n'*)
    simpl. rewrite -> IHn'. reflexivity. Qed. 