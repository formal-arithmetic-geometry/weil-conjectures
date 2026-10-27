## What changed

In `Sheaf.AlgebraicGeometry.ProEtaleClopenUnboundedDerivedLocalization`, proved the three
preliminary exactness/additivity theorems. Restriction preserves finite limits after forgetting
to presheaves and preserves colimits by the explicit module pushforward adjunction. Insertion
is additive by faithful tuple restriction and the diagonal identity/off-diagonal zero formulas.
The existing module-gluing exactness detector then proves insertion exactness.

Added proved private helpers `faithful_of_unit` and `additive_of_coordinates`. The latter
keeps the coordinate additivity argument abstract rather than repeatedly elaborating concrete
sheaf morphisms. Added proof-only imports
`Mathlib.Algebra.Homology.ShortComplex.ExactFunctor` and
`Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`. Moved the existing irreducibility
attributes immediately before the insertion proof; their declarations and final attributes
are unchanged. Kept `SheafOfModules.pushforward` locally irreducible after the restriction
proof to avoid repeated unfolding in the remaining statements and insertion proofs. This
reduced the full-file compile from 54.7 seconds (and a delivery timeout) to 36.0 seconds.
Updated DAG step 1 and proof origin to describe these proofs.

## Proved and sorry left

Closed three of the four original holes, with no new holes:

- `AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.restriction_exact`.
- `AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.insertion_additive`.
- `AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.insertion_exact`.

One original hole remains unchanged:
`AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.clopen_unbounded_derived_localization`,
node `lem-pur-clopen-unbounded-derived-localization`. Its complete localization and
normalization statement and proof plan are preserved. No split statements were added.
This is a partial delivery of the multi-hole module, not a proof of the main theorem.

## No longer needed

Removed unused proof imports `Mathlib.CategoryTheory.Localization.Pi` and
`Mathlib.CategoryTheory.Localization.Predicate`. The unproved main theorem still needs its
recorded localization dependencies; no DAG node or module is withdrawn or claimed pruned.
All public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. Step 1 can use the module-gluing theorem's already
proved exactness detector, instead of separately reconstructing coordinate kernel/cokernel
universal properties. Its diagonal/off-diagonal insertion formulas also suffice for
additivity. No hypotheses, universes, definitions, public signatures, or unit routes changed.

Change record: `coord/changes/proetale-clopen-localization-proof-transparency.md`.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
