(* Exercise: 1 star, standard (nandb) *) 

Inductive bool : Type :=
  | true 
  | false. 
Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.



Definition nandb (b1:bool) (b2:bool) : bool :=
  if (negb b1) then true
  else negb b2.


Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed. 

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed. 

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed. 

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed. 
