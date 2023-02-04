Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).


Arguments nil {X}.
Arguments cons {X}.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(* Prior proven theorems/lemmas *)
Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
    intros A l m n. induction l as [| k l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHl'. reflexivity.
    Qed.
                     
(* additional lemmas *)
Lemma list_app_nil : forall X (l1 : list X),
    l1 ++ [] = l1.
Proof.
    intros X l1. induction l1 as [| n l1' IHl1'].
    - simpl. reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity.
    Qed.

(* exercise *)
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
    intros X l1 l2. induction l1 as [| n l1' IHl'].
    - simpl. rewrite -> list_app_nil. reflexivity.
    - simpl. rewrite -> IHl'. rewrite -> app_assoc. reflexivity.
    Qed.

(* exercise *)
Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
    intros X l. induction l as [| n l' IHl'].
    - simpl. reflexivity.
    - simpl. rewrite -> rev_app_distr. rewrite -> IHl'. simpl. reflexivity.
    Qed.