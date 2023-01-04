Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Definition incr (m:bin) : bin 
    https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html#ad2ec4e405f68c46c0a176e3e94ae2e%3Csub%3E3%3C/sub%3E

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.