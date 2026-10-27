## What changed

Filled `finiteOrdinary_properties` and `restrictionSquare_existsUnique` in
`Sheaf.Paper.PurRepresentingPairFiniteScalar`. The first compares the ordinary coordinate
functor with restriction along the constant sheafification unit and the existing quotient-ring
equivalence. The second constructs the unique identity-on-sections comparison using
naturality of that unit. All theorem statements remain unchanged. Object and counit construction bodies remain
unchanged. The `finiteReductionChart` comparison proves its index simplification directly by reflexivity
after unfolding the projection. The chart is declared before the Brown-coordinate definitions, matching its imported-only
dependencies and avoiding later local reducibility settings. The `object` and `counit`
definitions now give explicit result types, equal to their previously inferred types, and
are locally irreducible only for elaboration of `RationalPair`, then return to normal
reducibility. From `coordinateOrdinaryComparison` onward, elaboration respects the existing
transparency boundaries; the full-module diagnostic compile succeeded in 41.9 seconds.
The change record is
`coord/changes/pur-finite-scalar-explicit-counit-type.md`. Updated the node with the auxiliary proof step and its existing-node dependencies.
Added proved private helpers and a private import of
`Sheaf.CategoryTheory.ConstantRingModuleSheaves`.

## Proved and sorry left

Closed two of the original four holes:

- `WeilConjectures.PurRepresentingPairFiniteScalar.finiteOrdinary_properties`.
- `WeilConjectures.PurRepresentingPairFiniteScalar.restrictionSquare_existsUnique`.

Two holes remain, both attached to
`lem-pur-reconstructed-pair-finite-scalar-extension`:

- `WeilConjectures.PurRepresentingPairFiniteScalar.coordinateEvaluation_existsUnique`.
- `WeilConjectures.PurRepresentingPairFiniteScalar.reconstructed_pair_finite_scalar_extension`.

No holes were added and no statements were split off. The full scalar-extension theorem
remains unfinished; this delivery closes its two ordinary-coordinate prerequisites.

## No longer needed

Removed private imports `Sheaf.Paper.PurIntegralReductionUniformTor`,
`Sheaf.Paper.FiniteFreeConstructibleScalarTransport`,
`Sheaf.CategoryTheory.SystemScalarCoherence`,
`Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus`,
`Sheaf.Paper.BrownTowerFiniteSiteComparison`, and `Sheaf.Paper.ScalarCompletionAssociator`.
They are unused by the completed auxiliary proofs. No DAG dependency or module is withdrawn;
the unfinished main argument retains its planned dependencies and its unit route.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. Existing inferred counit types and the coefficient chart
required elaboration repairs to meet the single-file compile limit; those repairs are
recorded in the change record above. The module's ordinary-coordinate proof sketches apply
as stated. The constant commutative-ring sheafification and ring-valued sheafification must
be related through `constantCommuteCompose`; treating them as definitionally identical would
miss a necessary scalar-action comparison.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
