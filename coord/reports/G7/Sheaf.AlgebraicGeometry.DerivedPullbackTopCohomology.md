## What changed

Filled `AlgebraicGeometry.derivedPullback_topCohomology` in
`Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology`, preserving every existing
signature and construction. All supporting lemmas are proved private helpers.
The proof uses bounded-above flat replacements and the selected counit's existing
K-flat invertibility theorem. Right exactness computes the top homology of the
counit on a strictly bounded representative. The truncation triangle then proves
invertibility of the specified top comparison on every upper-bounded object.
The Hom-set bijection proves projection naturality and its universal factorization;
these give naturality and composition of the top comparison.

For composition, the section-normalized tensor adjunction is identified with the
adjunction selected by the existing tensor-pullback theorem. Its composition map
is therefore the same mate used by the pinned derived composition. The selected
counit's composition equation and the termwise single comparison give the result
directly in every integer degree. No shift or inverse derived single comparison
is needed. Updated the existing DAG node to record this route.

## Proved and sorry left

Original holes: 1, in `AlgebraicGeometry.derivedPullback_topCohomology`
(node `lem-weil-pbc-derived-pullback-top-cohomology`).
The packet contains a complete proof of that declaration and zero textual
`sorry`s. No holes are added and none are split off. The full module compiled on the server in 57.6 seconds, with no warnings.
Axiom validation is checked by the delivery preflight. The local declaration comparison
confirms all five signatures and all four definition bodies are unchanged.

## No longer needed

Removed proof imports:

- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`: the proof needs the
  adopted source theorem returning `IsKFlatTensor`, which computes derived pullback;
  import `WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat` instead.
- `Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition`.
- `Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose`.

The proof does not use these originally declared proof dependencies:

- `lem-pc-canonical-single-pullback-composition`;
- `lem-pc-canonical-single-pullback-comparison` as an invertibility theorem;
- `lem-pc-canonical-single-adjunction-transpose`;
- `lem-pc-pinned-pullback-counit-shifts`;
- `lem-pc-pinned-pullback-composition-shifts`.

The corresponding five obsolete entries were removed from `tool_uses`.

Composition is proved in degree n from
`lem-pc-perfect-hom-cochain-counit`. The public imports defining the existing
canonical additive structure and pinned composition name remain, including their
transitive dependencies. Thus the source comparison module and the pinned shift
modules remain imported; this delivery does not claim they leave the targets'
import closure. No module or declaration is withdrawn. The blueprint unit's
statement and realized steps are unchanged.

These project modules leave this module's import closure (this does not assert
that they leave the whole targets' closure):

- `Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatStalkCriterion`
- `Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose`
- `Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison`
- `Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition`
- `Sheaf.Paper.DerivedHomMayerVietoris`
- `WeilConjectures.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison`
- `WeilConjectures.AlgebraicGeometry.Picard.HomotopySinglePullbackComposition`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `WeilConjectures.Mathlib.Algebra.Homology.Embedding.Extend`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Resolution`

## Where the brief, the DAG or earlier work was wrong

The original plan's passage through ordinary pullback comparisons and shifts is
unnecessary: the fixed-counit composition equation already works on every
homotopy single complex in degree n. The existing degree-comparison proof in
`WeilConjectures.AlgebraicGeometry.ModulePullbackComparisonDegreeAutomorphism`
provides the right-exact flat-resolution argument; its helpers are private, so
this packet proves the needed specialization for the selected counit locally.
The Sheaf K-flatness theorem gives the acyclic-tensor formulation; the adopted
source version gives the `IsKFlatTensor` predicate required by derived pullback.
No statement or definition repair was necessary. The argument also covers zero top
cohomology, negative degrees, and complexes unbounded below. On a nonflat map it
uses only the top cohomology isomorphism; it never assumes the derived single
comparison itself is invertible.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
