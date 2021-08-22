# Proof by simplificatioin 

so you use `simpl.` to simplify both sides

and then `reflexivity` to compare two identical values

now, refer back to the definition of plus 

```coq
Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => (plus n' m)
    end.
 
```

now, we can directly see something interesting here

`0 + m` will easily give us `0` (because of the first case of the function)



so the proof of that fact will be something like 

```coq
Theorem plus_0_: forall n : nat, (plus 0 n) = n.
Proof.
    intros n. simpl. reflexivity. Qed.

```



Note: if you did this 

```coq
Theorem  plus_n_0 : forall n : nat, (plus n 0) = n.
Proof.
    intros n. simpl. reflexivity. Qed.
```

we'll have a problem because `simpl.` will just return the input with no modification, i.e. `plus n 0` and you're gon



__What is `intros` you ask?__

`intros` keyword is used to introduce `forall` type variables into context

in this case that is `n`. To introduce it into the context of the proof we use `intros`



# Proof by rewriting



consider

```coq
Theorem plus_id_example : forall n m : nat, n = m -> n + n = m + m.

Proof.
    (* move both quantifiers into the context *)
    intros m n.
    (* move the hypothesis into context *)
    (* Hypothesis H here is m = n *)
    intros H.

    rewrite -> H.
    (* rewritten to n + n = n + n *)
    reflexivity.
Qed.
```



Note, the `->` in the `rewrite` has nothing to do with implication, it tells coq to rewrite from left to right. To rewrite from right to left, you use the `<-`

```coq
    rewrite <- H.
    (* rewritten to m + m = m + m *)
    reflexivity.
```



Note: you can present multiple statements implication like this 



```coq
Theorem plus_id_exercise : ∀ n m o : nat,
  n = m → m = o → n + m = m + o.
```

so this can be read as 
$$
n = m \and \ m = 0 \Rightarrow n + m = m + 0
$$
this is because of a functional programming concept called currying 



so the last statement is the actual claim, the first two are the hypothesees



The proof of the above statement is:

```coq
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
```





Note: `Admitted` can be used to consider a theorem without actually proving it 

Note: We can use the `Check` command to examing the statements of previously declared theorems or lemmas.

Take the example of these theorems that have been proven in the standard library.

```coq
Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)
Check mult_n_Sm.
(* ===> forall n m : nat, n * m + n = n * S m *)
```







Note that you can use the `rewrite ` tactic to use a previously proven theorem (instead of a hypothesis from the current context)





Now, we wanna prove this 

```coq
Theorem  mult_n_1: forall p : nat, mult p 1 = p.
```



using the above theorems 

```coq
Proof.
    intros p.
    (* goal is p * 1 = 0 *)
    rewrite <- mult_n_Sm.
    (* rewrite the left side and replace p * 1 with p * 0 + p *)
    rewrite <- mult_n_O.
    (* rewrite left side again to 0 + p *)
    simpl.
    (* left side becomes p *)
    reflexivity.
    (* dun. over. *)
Qed.
```



# Proof by Case Analysis

Sometimes we wanna prove shit case by case 

and rewrite those cases one by one

before the example, assume these things are in the file:

```coq
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

```



Now, consider we wanna prove this theorem 

```coq
Theorem  plus_1_neq_O: forall n : nat, plus n 1 =? O = false.

```

```coq
Proof.
	intros n.
	simpl. (* does nothing of value *)
Abort.
```



What can we do about this? 

we can break it into cases and prove those cases individually 

```coq
Theorem  plus_1_neq_O: forall n : nat, plus n 1 =? O = false.
Proof.
    intros n. destruct n as [|  n'] eqn:E.
    - reflexivity.
    - reflexivity.

Qed.

```



the `as [| n']` is like a list of lists that breaks it into two cases

the first element is empty because the `O` constructor doesn't need an argument 

the `-` leads to bulleted points, so that we can prove one by one 



the `destruct` tactic can be used with any inductively defined datatype



Definition of destruct as per  <https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.destruct>

### `destruct`

"This tactic applies to any goal. The argument [`term`](https://coq.inria.fr/refman/language/core/basic.html#grammar-token-term) must be of inductive or co-inductive type and the tactic generates subgoals, one for each possible form of [`term`](https://coq.inria.fr/refman/language/core/basic.html#grammar-token-term), i.e. one for each constructor of the inductive or co-inductive type. Unlike [`induction`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.induction), no induction hypothesis is generated by [`destruct`](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacn.destruct)."



Now consider this theorem

```coq
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.

```



```coq
Proof.
    intros b c.
    destruct b eqn:E.
    - simpl. intros H. rewrite <- H. reflexivity.
    - simpl. intros H2. discriminate.
Qed. 
```



Think of this proof like a truth table. 

First we break the `b` into two cases and then then examine the hypothesis 

in the first case we see `and true c = true` and in the second we see `and false c = true` 

when we do the rewrites, in the second case we'll get something like `true = false` and we can use the keyword `discriminate` to tell `coq` that the hypothesis itself doesn't work so there is only one plausible case and the other is a contradiction.



