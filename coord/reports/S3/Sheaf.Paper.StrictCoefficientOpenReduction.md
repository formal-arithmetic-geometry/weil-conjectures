## What changed

Proved `WeilConjectures.strictCoefficientOpenReduction` in
`Sheaf.Paper.StrictCoefficientOpenReduction`, preserving its complete statement and the
existing definition of `strictCoefficientOpenEvaluation` verbatim. The only other delivered
file is its own node, `lem-strict-coefficient-open-reduction`, whose proof, proof dependencies
and proof origin now describe the implemented route.

The proof uses five existing modules as private proof imports:
`IntegralReductionPullbackModel`, `IntegralSystemOperationModels`,
`IntegralOpenReductionIso`, `IntegralOpenFiniteEvaluation` and
`IntegralNativeOpenComparison`, all under `Sheaf.SixFunctors`.

For the canonical reduction calculi, invert the existing natural transformation
`model.openReduction` using `integralOpenReductionIso`, then compose with
`integralNativeOpenIso`. The latter compares complete strict-system functors, rather
than attempting to lift a collection of finite maps. The theorems
`integralNativeOpenComparison` and `integralOpenFiniteEvaluation`, followed by cancellation
of the evaluated isomorphism, give its finite-coordinate formula.

For arbitrary supplied SX and SY, compare reductions by uniqueness of left adjoints to
the same fixed total limit. A private proved lemma transposes `unit_projection` under
the finite scalar adjunction to show that these comparisons preserve
`reductionEvaluation`. Conjugating the constructed natural transformation and using
naturality gives the formula for SX and SY. Finally expand `openFiniteReduction`, move
inverse `finiteOpenIso` across the finite image by naturality, and cancel the two finite
open presentation factors. This is exactly the displayed ringed-coordinate equation.

All new helpers are private and fully defined or proved. There are no changes to shared
definitions, public signatures, public imports, consumer modules or adopted source modules.
No data definition chooses an arbitrary witness of an unproved existence theorem. The
existential operation/model witnesses are used within a theorem proof to construct the
existential comparison required by that theorem.

The proof is uniform for every ambient derived input and every natural n. It uses no
completeness, constructibility, quasi-compactness, nonzero input or nonempty scheme
hypothesis. Thus the empty open, zero input, identity open and exponent-one case n=0
are included by the same naturality and inverse identities.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.strictCoefficientOpenReduction`
(node `lem-strict-coefficient-open-reduction`).

Added 0 holes. Split off 0 statements. There are no remaining direct `sorry` occurrences
in the item or any new helper. The final single-file compile through `lcompile.py` passed without warnings in 36.6 seconds,
below the 60-second limit. Existing dependencies retain their own proof status;
this delivery proves the item from those already stated declarations.

## No longer needed

No existing import was removed, and no module is withdrawn. Each of the five added proof
imports provides a declaration used by the proof. Both original public imports remain.

The item's proof no longer directly uses these former planned dependencies:

- `lem-pc-kflat-resolution`, module
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`;
- `lem-pur-left-derived-from-kflat-class`, module
  `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`;
- `lem-weil-pbc-ring-sheaf-change-adjunction`, module
  `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`.

Their work is already packaged in the existing open-mate, finite-evaluation and native
presentation results. No claim is made that these modules become globally unreachable;
they may remain transitive dependencies of the results used here. No UNIT statement or
realized UNIT proof step is bypassed. The unit record `sk-def-sf-operations` has no
realized steps for this helper node.

## Where the brief, the DAG or earlier work was wrong

The former plan repeated a K-flat construction already available through the existing
whole-system open reduction isomorphism and its normalized evaluations. The shorter route
closes the item without introducing a fifth decomposition.

The current server queue row was checked: this is a proof item with one hole, not a
zero-hole rework. The historical rework row refers to a quarantined dependency involving
`FiniteRealizationScalarMate`; both the restored source and its preserved archive were
read. The current item is present, no build-error file is present, and no withdrawal or
empty replacement is made. Its Lean attachment and statement dependencies are preserved.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
