Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

(* The following exercises explore an alternative way of defining natural numbers using the Church numerals, which are named after their inventor, the mathematician Alonzo Church. We can represent a natural number n as a function that takes a function f as a parameter and returns f iterated n times. *)

Definition cnat := forall X : Type, (X -> X) -> X -> X.

(* Let's see how to write some numbers with this notation. Iterating a function once should be the same as just applying it. Thus: *)

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(* Similarly, two should apply f twice to its argument: *)
Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(* Defining zero is somewhat trickier: how can we "apply a function zero times"? The answer is actually simple: just return the argument untouched. *)
Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(* More generally, a number n can be written as fun X f x ⇒ f (f ... (f x) ...), with n occurrences of f. Let's informally notate that as fun X f x ⇒ f^n x, with the convention that f^0 x is just x. Note how the doit3times function we've defined previously is actually just the Church representation of 3. *)
Definition three : cnat := @doit3times.

(* So n X f x represents "do it n times", where n is a Church numerals and "it" means applying f starting with x. *)
(* Another way to think about the Church representation is that function f represents the successor operation on X, and value x represents the zero element of X. We could even rewrite with those names to make it clearer: *)
Definition zero' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => zero.

Definition one' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ zero.

Definition two' : cnat :=
  fun (X : Type) (succ : X -> X) (zero : X) => succ (succ zero).

(* If we passed in S as succ and O as zero, we'd even get the Peano naturals as a result: *)

Example zero_church_peano : zero nat S O = 0.
Proof. reflexivity. Qed.
Example one_church_peano : one nat S O = 1.
Proof. reflexivity. Qed.
Example two_church_peano : two nat S O = 2.
Proof. reflexivity. Qed.

(* But the intellectually exciting implication of the Church numerals is that we don't strictly need the natural numbers to be built-in to a functional programming language, or even to be definable with an inductive data type. It's possible to represent them purely (if not efficiently) with functions.
Of course, it's not enough to represent numerals; we need to be able to do arithmetic with them. Show that we can by completing the definitions of the following functions. Make sure that the corresponding unit tests pass by proving them with reflexivity. *)

(* Define a function that computes the successor of a Church numeral. Given a Church numeral n, its successor scc n should iterate its function argument once more than n. That is, given fun X f x ⇒ f^n x as input, scc should produce fun X f x ⇒ f^(n+1) x as output. In other words, do it n times, then do it once more. *)

(* exercise *)
Definition scc (n : cnat) : cnat :=
    fun (X : Type) (f : X -> X) (x : X) => f ((n X f) x).

Example scc_1 : scc zero = one.
Proof. reflexivity. Qed.

Example scc_2 : scc one = two.
Proof. reflexivity. Qed.

Example scc_3 : scc two = three.
Proof. reflexivity. Qed.
 
(* Define a function that computes the addition of two Church numerals. Given fun X f x ⇒ f^n x and fun X f x ⇒ f^m x as input, plus should produce fun X f x ⇒ f^(n + m) x as output. In other words, do it n times, then do it m more times. *)

(* thought i needed this but i do not but i am still keeping it as it might be useful later *)
Fixpoint repeat_apply {X:Type} (f : X -> X) (x:X) (n:nat) : X :=
  match n with
  | O => x
  | S n' => f (repeat_apply f x n')
  end.


(* exercise *)
Definition plus (n m : cnat) : cnat :=
    fun (X : Type) (f : X -> X) (x : X) => n X f (m X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.
Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.
Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
  Proof. reflexivity. Qed.

(* exercise *)
Definition mult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => m X (n X f) x.

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.
Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.
Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

(* exercise *)
Definition exp (n m : cnat) : cnat :=
  fun(X: Type) => m (X -> X) (n X).
(* i looked this one up since i couldn't quite figure it out & i did not have a lot of time to keep working on it but i do not quite understand what is going on here *)
  
Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.