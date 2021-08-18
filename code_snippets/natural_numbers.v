Module NaturalNumPlayground.

Inductive nat : Type :=
    | O
    | S (n : nat).


Check S ( S O) : nat.

Definition pred (n : nat) := 
    match n with
    | O => O
    | S n' => n'
    end.

Compute pred (S (S (S O))).


End NaturalNumPlayground.

Check (S (S (S O))).

Definition minustwo (n : nat) : nat := 
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.

Compute (minustwo 4).

Fixpoint iseven (n : nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S ( S n') => iseven (n')
    end.


Definition isodd (n : nat) : bool :=
    match n with
    | n => negb(iseven n) 
    end.

Example check_is_even : (iseven 16) = true.
Proof. simpl. reflexivity. Qed.

Example check_is_odd : (isodd 17) = true.
Proof. simpl. reflexivity. Qed.


Module NaturalPlayground2.

Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => (plus n' m)
    end.
 
    
End NaturalPlayground2.

