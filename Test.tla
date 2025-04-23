---- MODULE Test ----
EXTENDS Naturals

CONSTANT N
ASSUME N = 10

VARIABLE dummy, x, n

Double[x ∈ 1..N]   == 2 * x
Increment[n ∈ 1..N] == n + 1

TestInc == Increment[3]

Init  == dummy = 0

Next  == dummy' = dummy
Spec  == Init ∧ [][Next]_dummy
====  

