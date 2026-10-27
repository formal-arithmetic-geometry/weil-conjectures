## What changed

Filled the five theorem proofs in `Sheaf.Paper.PointExactDerivedModel`, preserving
all existing public signatures and data. Exactness uses the existing exact pullback
and point-section instances, and quasi-isomorphism preservation for exact functors.
Composition uses the published module-comparison localization theorem, the exact
composition factorization formula, and the natural-isomorphism factorization formula.
Constructibility uses the isomorphism-pullback theorem and the canonical comparison
between tensor and transported pullback models. Evaluation restriction is definitional.
Composition and descent use proved private abstract lemmas, avoiding expansion of
ringed-site data during factor cancellation.

## Proved and sorry left

Closed all five original holes: `WeilConjectures.PointExactDerivedModel.exactness`,
`WeilConjectures.PointExactDerivedModel.composition`,
`WeilConjectures.PointExactDerivedModel.preserves_constructible`,
`WeilConjectures.PointExactDerivedModel.evaluation_restriction`, and
`WeilConjectures.PointExactDerivedModel.descent`, all attached to
`lem-trf-point-exact-derived-model`. No split-off statements or textual sorry remain. Holes closed: 5. Holes added: 0.
The module compiled cleanly through lcompile.py (15.5 seconds, exit code 0); the
final delivery rechecks the module and axioms after removing an unused private helper. The proof covers n=1 by the
successor reindexing, r=0 and m=0 by the positive-power conventions, arbitrary
unbounded K, and arbitrary alpha (including zero and noninvertible alpha).

## No longer needed

Removed redundant explicit proof imports:
`Sheaf.AlgebraicGeometry.ProEtaleConstantExact`,
`Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`,
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, and
`Sheaf.Paper.PointSectionsFiniteness` are redundant explicit proof imports.
The existing public imports remain unchanged because they provide the public interface.
Added private proof imports for module-comparison localization, the normalized
pullback-model bridge, the Frobenius point isomorphism, bounded-constructible
isomorphism closure, and the source exact-functor API. The direct
`lem-sfb-exact-derived-composition` node is retained for its formula; the proof
uses the source API `mapDerivedCategoryCompIso_fac` implementing that same formula,
rather than its existence-and-uniqueness wrapper module. The proof does not need the combined point realization
`lem-trf-point-exact-realization`: its exactness and evaluation clauses are already
instances and definitional equalities; constructibility is obtained directly from the
isomorphism theorem. It does not need the full pasting-syntax theorem
`lem-trf-exact-evaluation-transformation-descent`: Mathlib localization directly
provides the particular existence and uniqueness assertion stated here. The constant
coefficient composition identity and K-flat resolution argument are already subsumed
by `lem-pod-constant-comparison-module-localization`. The obsolete direct tool-use approvals
`lem-weil-pbc-exact-functor-derived-functor` and `lem-pc-kflat-resolution` are removed:
no Kan-extension property or resolution is constructed in this proof. The already
normalized comparison theorem retains its own dependencies. No declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned realization uses transported pullback, while this module uses tensor
pullback. They are canonically naturally isomorphic, rather than definitionally equal;
constructibility transfers through `openSquareDerivedPullbackModel` and isomorphism
closure. Positive coefficient levels are changed from n to j+1 using n >= 1.
The full-subcategory restriction of evaluation is definitionally the recorded fibre.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
