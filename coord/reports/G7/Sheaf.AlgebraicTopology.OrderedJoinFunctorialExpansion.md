## What changed

Proved `AlgebraicTopology.OrderedJoin.functorialExpansion` in
`Sheaf.AlgebraicTopology.OrderedJoinFunctorialExpansion`, preserving the existing
public declarations and the recipe definition. All helpers are proved and private.
Naturality is checked on the free integer generators. Mapping commutes with face
insertion and replacement, and `symbolTerm` handles invalid degrees explicitly.
The prefix recurrence is proved from the actual `List.range` fold, preserving
rightmost-first composition. Induction gives missing-color vanishing and the
signed powerset expansion; Mathlib's powerset-insert sum partitions the two
branches. Conversion from the powerset sum back to the specified list retains
its unreduced indexing, and the cardinality of the initial interval gives `2^i`.

The node's proof step 5 and proof-origin note record the equivalent induction on
ascending prefix length. Other node fields, the statement, definitions, and unit
route are unchanged. Added private proof imports supply powerset sums, finite
interval cardinalities.

## Proved and sorry left

Closed the one original hole:
`AlgebraicTopology.OrderedJoin.functorialExpansion`
(node `lem-sfb-ordered-join-functorial-expansion`). Added zero holes and split off
zero statements. No `sorry` remains in the delivered module.

Validation: the complete module compiled cleanly through `lcompile.py` in
5.0 seconds. `#print axioms AlgebraicTopology.OrderedJoin.functorialExpansion`
reported exactly `propext`, `Classical.choice`, and `Quot.sound`. The proof does
not inherit the parent theorem's hole. All delivered Lean lines are at most
100 characters.

## No longer needed

No existing import, node, or module is pruned. The sole declared proof dependency,
`def-weil-pbc-free-module`, is realized by the existing Finsupp free-module API.
The proof uses the constructions from `OrderedJoinPartialContraction`, never its
unfinished `partialContraction` theorem. The sibling single-color and telescope
theorems are not needed for this calculation and were not imported. Searches
with LeanFinder, Loogle, the logged grep service, and local source inspection
found scalar commutative-ring product identities, which do not directly supply
these ordered linear-operator identities.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was required. The ascending-prefix
induction is equivalent to the descending-endpoint induction in the original
plan. Both explicitly preserve the prescribed composition order. The degree
argument uses the existing cardinality-sensitive `symbolTerm`; no restriction
to nonnegative degrees or injective vertex maps is introduced.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
