

Theorem plus_id_example : forall n m : nat, n = m -> n + n = m + m.

Proof.
    (* move both quantifiers into the context *)
    intros m n.
    (* move the hypothesis into context *)
    (* Hypothesis H here is m = n*)
    intros H.

    rewrite <- H.
    reflexivity.
Qed.

Theorem plus_id_exercise : forall n m : nat, 
    n = m -> m = O -> n + m = m + O.

Proof.
    intros n m.
    (* introduce m n  in the current context*)
    intros H.
    (* introduce hypothesis H: n=m *)
    intros H2.
    (* introduce hypothesis H2: m = O*)
    
    rewrite -> H.
    (* rewrite claim using H and from left to right, i.e. claim becomes m + m = m + O *)
    rewrite <- H2.
    (* rewrite claim using H2 from right to left, i.e. replace O with m *)

    reflexivity.
    (* simple reflexitivity comparison *)
Qed.

Check mult.
Check mult_n_O.
Check mult_n_Sm.

Theorem  mult_n_1: forall p : nat, mult p 1 = p.
Proof.
    intros p.
    rewrite <- mult_n_Sm.
    rewrite <- mult_n_O.
    simpl.
    reflexivity.



Qed.

