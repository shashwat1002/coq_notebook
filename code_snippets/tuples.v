Module TuplePlayground.

Inductive bit : Type :=
    | B0
    | B1.

Inductive three_tuple : Type :=
    | bits (b0 b1 b2 : bit).

Check (bits B0 B1 B0)
    : three_tuple.


End TuplePlayground.

Module TuplePlayground2.

Inductive bit : Type :=
    | B0
    | B1.

Inductive three_tuple : Type :=
    | bits (b0 : bit) (b1 : bit) (b2 : bit).

Check (bits B0 B1 B0)
    : three_tuple.
    
End TuplePlayground2.


