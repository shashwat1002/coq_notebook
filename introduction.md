# Data and functions

- _coq_ by itself doesn't provide much functionality on datatypes.
- It provides a mechanism to define datatypes from scratch.
- The coq distribution comes with numbers / booleans etc. But these are just part of the standard library and have been written using said mechanism.



## Days of the week

Using a simple example to illustrate the definition mechanism

We are definining a _type_ and it'll be called _day_

```coq
Inductive day: Type :=
	| monday
	| tuesday
	| wednesday
	| thursday
	| friday
	| saturday
	| sunday.
```



lol, actual fullstops are used to terminate

Note: I don't yet know what `Inductive` implies yet but I hypothesize that it's basicaly telling the compiler that the possible values of the _type_ `day` make a set that is well-ordered 

(hypothesis failed :) )



Now we can make a function



```coq
Definition next_weekday (d:dat) : day :=
	match d with
	 | monday => tuesday
	 | tuesday => wednesday
	 | wednesday => thursday
	 | thursday => friday
	 | friday => monday
	 | saturday => monday
	 | sunday => monday
	end.
```

 

imagine having two-day weekend, can't be me.

Note: in above examples, the types have been explicitly declared and that is not necessary in coq (not always anyway)

to evaluate these functions we us the `Compute`

```coq
Compute (next_weekday friday).
(* ==> monday: day *)
```



also consider 

```coq
Compute (next_weekday (next_weekday friday)).
```

gives the second weekday after friday 



Now, we can record what our expectations 

```coq
Example test_next_weekday:
	(next_weekday(next_weekday saturday)) = tuesday.
```



This basically makes the assertion that the second weekday after saturday is tuesday. 



Also we named the assertion `test_next_weekday` so that we can refer to it later.



We can ask coq to actually verify this assertion like so 

```coq
Proof. simpl. reflexivity. Qed.
```

The above statement implies that the assertion can be verified by saying that both sides of the equality evaluate to the same thing.



The `Proof` keyword makes coq enter the proof mode. 

`simpl` in this case simplifies the left side to `tuesday` 

`reflexivity.`  just verifies the trivial equality `tuesday = tuesday`



Note: suppose we put two assertions before the `Proof. simpl. reflexivity. Qed.` This is called a nested proof and isn't allowed by default.



also if the assertion fails coq will give a message like `Unable to unify "tuesday" with "wednesday".`

## Booleans

This is a standard type `bool` but we're gonna define it ourselves with members true and false



```coq
Inductive bool: Type :=
    | true
    | false.
    
```

Note: I haven't a clue what `Inductive` implies here



Anyway, using the function definition syntax we saw earlier, we can define a few functions



```coq
Definition negb (b: bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Definition andb (b1: bool) (b2: bool): bool :=
    match b1 with
    | true => b2
    | false => false

Definition orb (b1: bool) (b2: bool) : bool := 
    match b1 with
    | true => true
    | false => b2
    end.

```



These are interesting ways to define and / or, ngl 

and now suppose we checked `or` on a case by case basis



```coq
Example test_orb1: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.


```



# Notation

Also we can define nice symbols to represent functions

```coq
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.

Proof. simpl. reflexivity. Qed.

```



# Types

`Check` command prints the type an expressions computes to 



```coq
Check true.
(*===> true: bool)
```



if we follow the check expression with a colon and another expression, coq will compare the types and verify if they're thesame 

```coq
Check true
: bool.

```

Note: even functions have a type, they're _function types_ and are represented using arrows

```
Check negb
	: bool -> bool.
```





# The `Inductive` definition

Finally we get to address the `Inductive` definition.

If you'll note, the types so far have all been like `enums` or `enumerated types` 

- so they're like a finite set of elements, called _constructors_



The `Inductive` definition does two things

- we get a set of new _constructors_ eg: red, true, etc.
- It groups said constructors into a name like `bool` or `color`



# New types from old

We also note that _constructors can in turn take arguments like here

```coq
Inductive rgb: Type :=
	| red
	| green
	| blue.
Inductive color: Type :=
	| black
	| white
	| primary (p: rgb)
	

```

note the `primary` it takes an argument of type `rgb`



so when we say `primary red` it is said that the `primary` constructor has been applied to argument `red`

so 
$$
\text{red} \in rgb \\
\text{primary red} \in color
$$


So now we define other functions



```coq
Definition monochrome (c: color) : bool := 
    match c with
    | black => true
    | white => true
    | primary p => false
    end.
```



and now 

```coq
Compute monochrome black.
Compute monochrome (primary red).
```



both give us true 

also in the second case if we did `Compute monochrome primary red` it would be an error because red is supposed to be an argument to `primary`



# Modules

Coq provides a _mdule_ system for making large shit 

The syntax ends up looking a lot like python



```coq
Module Playground.
	Definition b: rgb := blue.
End Playground
```

Now, that particular `b` will be referred to using `Playground.b` 



# Tuples

A single constructor with multiple parameters can be used to create a tuple type

Consider a bit string of 3 members

(will also define bool)



```
Inductive bit : Type :=
    | B0
    | B1.

Inductive three_tuple : Type :=
    | bits (b0 b1 b2 : bit).

Check (bits B0 B1 B0)
    : three_tuple.

```

Also I think this is equivalent to 



```coq
Inductive bit : Type :=
    | B0
    | B1.

Inductive three_tuple : Type :=
    | bits (b0 : bit) (b1 : bit) (b2 : bit).

Check (bits B0 B1 B0)
    : three_tuple.
    
```



the latter suntax is what'll allow me to make mixed tuples



# Numbers



we'll endeavour to define natural numbers ourselves.

We want the definition to be such that it makes proofs simpler.

So we kinda define it recursively

```coq
Inductive nat : Type :=
	| O
	| S (n : nat).
```



So what does this look like with context to numbers we know and love?

- 1 is represented by S O
- 2 is represented by S (S O)
- 3 is represented by s ( S ( S O))

think of S as "successor" so S of something means _successor of something_



We need to understand that _O and S are symbols in the sand_ (Thank you, professor Aftab Hussein). We have just defined a representation 



## Functions on this definition

```coq
Definition pred (n : nat) : nat :=
	match n with
		| O => O
		| S n' => n'
	end.

```

the second branch is basicallt saying that if you have S (..) then return the stuff in the parenthesis

Note it's not `0`, it's `O` just a representation 





Because Natural numbers are so uniquitous, coq provides a definition for them and a nice way of printing them 



consider this

```coq
Check (S (S (S O))).
```



the output of `coq` will mention `nat` and `3` 

consider an arbitrary function

```coq
Definition minustwo (n : nat) : nat := 
    match n with
    | O => O
    | S O => O
    | S (S n') => n'
    end.
```



note that 

`Check S` will yield `nat -> nat`

and so will `Check minustwo` and `Check pred`

but there is a fundamental difference between them and S

both `minustwo` and `pred` are computationally defined, that is `pred (S O)` can be _simplified_ to `O` . No such behavior can be associated to simplification of `S` and an argument



# Recursive function

```coq
Fixpoint iseven (n : nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S ( S n') => iseven (n')
    end.
```



This is basically using a recursive function based on the claim that `n` is an even number if and only if `n-2` is also even with the base cases of `1` ans `0`







You use the `Fixpoint` keyword instead of `Definition`

You can use this definition to define other functions, like say for instance we wanna detect odd numbers, we can define such a function as a negation. 



```coq
Definition isodd (n : nat) : bool :=
    match n with
    | n => negb(iseven n) 
    end.
```









Now consider the examples

```coq
Example check_is_even : (iseven 16) = true.
Proof. simpl. reflexivity. Qed.

Example check_is_odd : (isodd 17) = true.
Proof. simpl. reflexivity. Qed.
```

pass

but

```coq
Example check_is_od : (iseven 17) = true.
Proof. simpl. reflexivity. Qed.
```



fails

## `plus`

We define plus again

```coq
Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => (plus n' m)
    end.
```



## `eqb`

```coq
Fixpoint eqb (n m : nat) : bool :=
	match n with 
		| O => match m with
				| 0 => true
				| s m' => false
				end
		| S n' => match m with
					| 0 => false
					| S m' => eqb n' m'
					end
	end.

```



lol, the complexity is `O(min(m, n))`

## `leb`

```coq
Fixpoint leb (a b: nat ) : bool :=
    match a with
    | O => true
    | S a' => match b with
                | O => false
                | S b' => leb a' b'
                end
    end.

```

