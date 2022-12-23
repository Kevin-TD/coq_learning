(* cmd + shift + i for interpret to point *)
Module TuplePlayground.
    Inductive bit : Type :=
        | B0
        | B1.
    Inductive nybble : Type :=
        | bits (b0 b1 b2 b3 : bit).
    Check (bits B1 B0 B1 B0) : nybble.

    (* The bits constructor acts as a wrapper for its contents. Unwrapping can be done by pattern-matching, as in the all_zero function which tests a nybble to see if all its bits are B0. We use underscore (_) as a wildcard pattern to avoid inventing variable names that will not be used. *)
    Definition all_zero (nb : nybble) : bool := 
        match nb with 
        | (bits B0 B0 B0 B0) => true 
        | (bits _ _ _ _) => false 
        end. 

    Compute (all_zero (bits B1 B0 B1 B0)). 
    Compute (all_zero (bits B0 B0 B0 B0)).


End TuplePlayground.  