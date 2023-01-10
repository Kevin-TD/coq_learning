(* In Coq, as in informal mathematics, large proofs are often broken into a sequence of theorems, with later proofs referring to earlier theorems. But sometimes a proof will involve some miscellaneous fact that is too trivial and of too little general interest to bother giving it its own top-level name. In such cases, it is convenient to be able to simply state and prove the needed "sub-theorem" right at the point where it is used. The assert tactic allows us to do this. *)

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
    Admitted.

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

  (* The assert tactic introduces two sub-goals. The first is the assertion itself; by prefixing it with H: we name the assertion H.  *)
  (* The second goal is the same as the one at the point where we invoke assert except that, in the context, we now have the assumption H that n + 0 + 0 = n. That is, assert generates one subgoal where we must prove the asserted fact and a second subgoal where we can use the asserted fact to make progress on whatever we were trying to prove in the first place. *)

(* As another example, suppose we want to prove that (n + m) + (p + q) = (m + n) + (p + q). The only difference between the two sides of the = is that the arguments m and n to the first inner + are swapped, so it seems we should be able to use the commutativity of addition (add_comm) to rewrite one into the other. However, the rewrite tactic is not very smart about where it applies the rewrite. There are three uses of + here, and it turns out that doing rewrite → add_comm will affect only the outer one *)
(* To use add_comm at the point where we need it, we can introduce a local lemma stating that n + m = m + n (for the particular m and n that we are talking about here), prove this lemma using add_comm, and then use it to do the desired rewrite. *)

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.