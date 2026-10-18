## What changed

Proved both declarations in `lean/Sheaf/Paper/ProperUnboundedWindow.lean`.
Added proof-only imports of `Sheaf.Paper.ProperIndConstructibleUnbounded` and
`Sheaf.Paper.ProperUnboundedWindowIso`. A proved private helper converts the
finite-natural-lower-bound dimension hypothesis to the extended-dimension bound
required by the former. This handles negative d and bottom dimensions explicitly.
The existing derived pushforward alias reduces to the same total derived functor.
The proof selects preservation and both bounds from the arbitrary-complex theorem,
then selects final-endpoint membership and the two specified canonical IsIso
assertions from the window theorem. Both coefficient cases follow this argument.
Updated the item's proof, proof_deps and proof_origin to describe these selections.
No existing signature, public import or definition changed.

Both proofs compile together through lcompile.py (6.6 seconds, no errors or warnings).
The initial combined constructor caused excessive elaboration; applying the theorem
in stages and checking each conjunct separately compiles within the normal limits.
No definition repair or increased limit was needed.

## Proved and sorry left

Closed 2 of 2 holes:
- `AlgebraicGeometry.ProEtale.properUnboundedWindow`.
- `AlgebraicGeometry.ProEtale.properUnboundedWindow_padicAlgCl`.

Both belong to `sk-lem-proper-unbounded-window`. Zero holes remain in the item;
zero holes were added and zero statements were split off. These proofs use the
existing stated dependencies, which still carry their own proof obligations.
`dimensionBound_of_nat_tests` is also completely proved.

## No longer needed

No existing imports were removed. No new import is unused.
The following are no longer direct proof dependencies of this module:
`det-ambient-ind-derived-sums` / `Sheaf.Paper.AmbientIndDerivedSums`,
`def-kun-truncations` / `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`, and
`det-proper-unbounded-window-bounded-below` /
`Sheaf.Paper.ProperIndConstructibleBoundedBelow`.
Their work is already encapsulated by the stronger declared conclusions of
`det-proper-unbounded-window-arbitrary` and `det-proper-unbounded-window-iso`.
They remain transitive dependencies of those modules, so this delivery prunes
no module from the targets' import closure and preserves the unit route.

## Where the brief, the DAG or earlier work was wrong

The DAG's five-step prose unnecessarily repeated conclusions already included in
the arbitrary-complex and window-isomorphism declarations. Their full signatures
allow direct conjunction assembly. The two dependencies encode the same integer
fibre bound differently; the conversion is proved, including the empty-fibre and
negative-d cases. No mathematical statement correction was required.
Searches with msearch.py (leanfinder, loogle, grep) and rg found the existing
project detail declarations as the shortest route. The useful Mathlib order lemma
was `ENat.WithBot.add_one_le_iff`; no replacement geometric theorem was found.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
