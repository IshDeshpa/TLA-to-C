----------------------------- MODULE SimpleCounter -----------------------------
EXTENDS Naturals, TLC

(****************************************************************************
--algorithm counter
variables x = 0;

begin
  IncrementLoop:
    while x < 5 do
      x := x + 1;
    end while;
end algorithm;
****************************************************************************)

=============================================================================

\* Invariants
Invariant1 == x >= 0                 \* x is always non-negative
Invariant2 == x <= 5                 \* x never goes above 5
Invariant3 == x \in Nat              \* x is always a natural number

\* The full specification
Init == x = 0
Next == 
  \/ /\ x < 5
     /\ x' = x + 1
  \/ /\ ~(x < 5)
     /\ UNCHANGED x

Spec == Init /\ [][Next]_<<x>>

\* Property to be checked by TLC
Inv == Invariant1 /\ Invariant2 /\ Invariant3
=============================================================================
