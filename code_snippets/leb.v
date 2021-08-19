Fixpoint leb (a b: nat ) : bool :=
    match a with
    | O => true
    | S a' => match b with
                | O => false
                | S b' => leb a' b'
                end
    end.


Fixpoint ltb (a b : nat) : bool := 
    match b with
    | O => false
    | S b' => leb a b'
    end.
