(* As a final illustration of how data structures can be defined in Coq, here is a simple partial map data type, analogous to the map or dictionary data structures found in most programming languages. *)
(* First, we define a new inductive datatype id to serve as the "keys" of our partial maps. *)
Inductive id : Type :=
  | Id (n : nat).

(* Internally, an id is just a number. Introducing a separate type by wrapping each nat with the tag Id makes definitions more readable and gives us flexibility to change representations later if we want to.
We'll also need an equality test for ids: *)

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
Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Lemma n_eq_n : forall n : nat, 
    n =? n = true.
Proof.
    intros n. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHn'. reflexivity.
    Qed.

(* EXERCISE *)
Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
    intros x. destruct x.
    simpl. rewrite -> n_eq_n. reflexivity.
    Qed.

(* Now we define the type of partial maps: *)
Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).


(* The update function overrides the entry for a given key in a partial map by shadowing it with a new one (or simply adds a new entry if the given key is not already present). *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(* Last, the find function searches a partial_map for a given key. It returns None if the key was not found and Some val if the key was associated with val. If the same key is mapped to multiple values, find will return the first one it encounters. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

(* EXERCISE *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
    intros d x v. destruct d.
    - destruct x.
     + simpl. rewrite -> n_eq_n. reflexivity.
    - destruct x.
     + simpl. rewrite -> n_eq_n. reflexivity.
    Qed.

(* EXERCISE *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
    intros d x y o H. destruct d.
    - simpl. rewrite -> H. reflexivity.
    - simpl. rewrite -> H. reflexivity.
    Qed.