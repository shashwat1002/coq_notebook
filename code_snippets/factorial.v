
Fixpoint factorial (n : nat) : nat :=
    match n with
    | O => S O
    | S O => S O
    | S n' => mult n (factorial n')
    end.

Example check_factorial_6 : factorial(6) = 720.
Proof. simpl. reflexivity. Qed.

Example check_factorial_10 : factorial(5) = mult 10 12.
Proof. simpl. reflexivity. Qed.
