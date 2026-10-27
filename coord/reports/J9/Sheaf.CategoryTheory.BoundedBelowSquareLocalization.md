## What changed

Proved `CategoryTheory.existsUnique_boundedBelowSquareLocalization` in
`Sheaf.CategoryTheory.BoundedBelowSquareLocalization`, preserving its statement.
The proof composes the exact-functor comparisons on the unbounded homotopy category,
restricts the conjugated termwise transformation to the bounded-below homotopy category,
and descends by Mathlib's fully faithful precomposition with `DerivedCategory.Plus.Qh`.
The preimage equation gives the component formula; cancellation gives the commuting square;
localization extensionality proves uniqueness. Updated the item's node proof to this route.
No other existing module or node was changed.

Validation: the final module compiled cleanly through `lcompile.py` in 3.7 seconds.
The original theorem statement was also compared verbatim and is unchanged.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.existsUnique_boundedBelowSquareLocalization`
(node `lem-trf-bounded-below-square-localization`): 1 of 1 original sorries.
Added 0 holes and 0 split-off statements. No sorry remains in the delivery.

## No longer needed

Removed the private import
`Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`:
the proof uses the homotopy localization instance in `DerivedCategory.Plus`
directly, so it does not need the cochain quotient's composite localization instance.
The separate passage to bounded-below cochain complexes and back is unnecessary.
All three existing proof-dependency nodes remain relevant: exact-functor comparisons,
bounded-below homotopy localization (the input already recorded in the cochain-localization
node's Mathlib match), and localization's universal property.
No project module or entire dependency node is withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original plan's detour through cochain
localization can be omitted because Mathlib already proves the needed homotopy
localization directly without enough injectives. The construction does not import
`BoundedBelowDerivedMateModel` (which would take a longer route through bounded-below
exact functors); it retains exactly the unbounded comparisons prescribed in this statement.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
