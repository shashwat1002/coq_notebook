Theorem indentify_fn_applied_twice : 
forall (f : bool -> bool),
(forall (x : bool), f x = x) -> forall (b : bool), f ( f b ) = b.

Proof. 
    intros f.
    intros H.
    intros b.
    rewrite -> H.
    rewrite -> H.
    reflexivity.
Qed.

Theorem andb_eq_orb : 
forall (b c : bool),
( andb b c = orb b c) -> b = c.
Proof.
    intros b c.
    destruct b.
    - simpl. intros H1. rewrite <- H1. reflexivity.
    - simpl. intros H2. rewrite <- H2. reflexivity. 
Qed.



(* New definition of binary as per the excercise :*)

Inductive bin : Type :=
    | Z
    | B0 (n : bin)
    | B1 (n : bin).

Fixpoint incr (m : bin) : bin :=
    match m with
    | Z => B1 Z
    | B0 m' => B1 m'
    | B1 m' => B0 (incr m')
    end.


Fixpoint bin_to_nat (m:bin) : nat :=
    match m with
    | Z => O
    | B0 m' => mult 2 (bin_to_nat m')
    | B1 m' => S (mult 2 (bin_to_nat m'))
    end.

(* Unit tests begin here : *)

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. simpl. reflexivity. Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. simpl. reflexivity. Qed.





