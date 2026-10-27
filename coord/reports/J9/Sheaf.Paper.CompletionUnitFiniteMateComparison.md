## What changed

Proved `WeilConjectures.CompletionUnit.finiteComparison_of_unit` in
`Sheaf.Paper.CompletionUnitFiniteMateComparison`, preserving its signature and the
original public import. Added a private proof import of
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` for the
canonical exact-functor comparison equations. Updated the item's own DAG proof
and proof-origin record to describe the Lean argument.

The proof first computes eta followed by a finite total-limit projection. Its
K-injective normalization extends to every tower by naturality along a
K-injective resolution and cancellation after exact evaluation. Canonical
localization-factor equations transport this to sequence restriction. The
ordinary model's degreewise projection and tensor-unit formulas then give the
ordinary finite scalar unit. Finally the finite derived adjunction's normalized
K-flat unit and injectivity of its Hom equivalence identify the evaluated
comparison. All auxiliary lemmas are private and completely proved.

Remote compilation accepted the complete proof in 55.8 seconds. Development
profiling options were removed before delivery. Static comparison confirmed the
public theorem signature is unchanged and every Lean line is at most 100 columns.

Only the item module and its own node are changed. No shared definition,
statement, instance, public import, target, or consumer is changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.CompletionUnit.finiteComparison_of_unit`, node
`lem-trf-completion-unit-finite-mate-comparison`.

Holes closed: 1. Holes added: 0. Holes remaining in the item: 0.
No statements were split off, and no theorem bodies elsewhere were changed.
This proves the assigned statement from the existing library declarations;
it does not claim that all transitive dependencies are free of `sorry`.

## No longer needed

None. No original import was removed, no module was withdrawn, and no declared
DAG dependency was bypassed. The existing ordinary model, coefficient calculus,
actual tower projections, K-injective resolutions, and normalized finite scalar
adjunction are all used. The blueprint unit and its realized steps are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect proof step was found. The given three-step plan
can be formalized without another decomposition. The final equality uses finite
adjunction mates, not faithfulness of derived evaluation. The argument treats all
integer cochain degrees and every natural-number level uniformly, including
level zero (positive exponent one), zero complexes, and empty schemes. The
flat-term hypothesis is preserved in the theorem's signature; the calculation
itself only needs the supplied K-flat condition.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
