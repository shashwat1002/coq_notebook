Fixpoint eqb (m n : nat)  : bool :=
    match m with
    | O => match n with
            | O => true
            | S n' => false
            end
    | S m' => match n with
                | O => false
                | S n' => eqb m' n'
                end
    end.


Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem  plus_1_neq_O: forall n : nat, plus n 1 =? O = false.
Proof.
    intros n. destruct n as [|  n'] eqn:E.
    - reflexivity.
    - reflexivity.

Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.

Proof.
    intros b c.
    destruct b eqn:E.
    - simpl. intros H. rewrite <- H. reflexivity.
    - simpl. intros H2. discriminate.
Qed. 

