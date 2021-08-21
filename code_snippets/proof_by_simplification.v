Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => (plus n' m)
    end.
 
Theorem plus_0_: forall n : nat, (plus 0 n) = n.
Proof.
    intros n. simpl. reflexivity. Qed.

