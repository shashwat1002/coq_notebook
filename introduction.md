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

