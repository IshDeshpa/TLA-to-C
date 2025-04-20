---- MODULE Test ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N
VARIABLES x, y

ASSUME N ∈ Nat /\ N > 0

(*-----------------------------------------------------------------*)
(* A bounded quantifier example: for all i in 1..N, i ≤ N       *)
AllWithinN ==
  \A i ∈ 1..N : i ≤ N

(*-----------------------------------------------------------------*)
(* A plain record literal                                        *)
MyRec ==
  [ foo  |-> x,
    bar  |-> y ]

(* A “set of records” (Cartesian product)                       *)
MyRecSet ==
  [ foo : {0,1},
    bar : {10,20} ]

(* Record‑field selection                                       *)
FooVal == MyRec.foo
BarVal == MyRec.bar

====


