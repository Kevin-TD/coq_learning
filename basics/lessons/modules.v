Inductive rgb : Type :=
  | red
  | green
  | blue.


Module Playground.
  Definition b : rgb := blue.
End Playground.

Definition b : bool := true.
Check Playground.b : rgb.
Check b : bool.
