----------------------------- MODULE ComplexTypes -----------------------------
EXTENDS Naturals, Sequences

\* Define a set of numbers
SetNums == {4, 5, 6}

\* Define a sequence containing numbers from the set
SeqNums == <<1, 2, 3>>

\* Define a record (structure) with several fields:
\*   - id: a numeric identifier
\*   - description: a string describing the record
\*   - dataSet: a field that holds the set of numbers
RecordExample == [ id          |-> 1,
                   description |-> "TLA+ Example",
                   dataSet     |-> SetNums ]

\* Define a function that maps each element in SetNums to its square
SquareFunction == [ x \in SetNums |-> x * x ]

\* Define a boolean value to help illustrate booleans in tree-sitter.
BooleanValue == TRUE

=============================================================================

