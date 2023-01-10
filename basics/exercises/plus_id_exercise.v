Theorem plus_id_exercise : forall n m o : nat, 
    n = m -> m = o -> n + m = m + o. 
Proof. 
    intros n m o. 
    intros H0 H1. 
    rewrite -> H0, H1.
    reflexivity. Qed. 