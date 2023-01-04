(* admittedly, i looked up the solution *)


Lemma andb_t_f : andb true false = false. 
Proof. reflexivity. Qed.

Lemma andb_f_t : andb false true = false. 
Proof. reflexivity. Qed.


Theorem andb_eq_orb : 
    forall (b c : bool), 
    (andb b c = orb b c) -> 
    b = c. 
Proof. 
    intros b c H. 
    - destruct b. 
     + destruct c. 
      -- reflexivity.
      -- rewrite <- andb_t_f. rewrite -> H. reflexivity.
     + destruct c. 
      -- rewrite <- andb_f_t. rewrite -> H. reflexivity.
      -- reflexivity.
Qed.


