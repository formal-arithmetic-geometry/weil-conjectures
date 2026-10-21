## What changed

Filled the six proof bodies in Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary.
All fourteen original public signatures were compared verbatim with the source and match;
the existing real-data definitions are unchanged. Private proved
helpers establish the derived-unit shift compatibility, the triangle comparison for a
sequence with injective first terms, and the canonical open-section comparison.

The section row is the actual kernel and restriction row. The sheaf support row is
short exact by supportInjectiveConeDistinguished; its degreewise splittings identify
its derived image triangle with the evaluated quotient triangle. Universal kernels
supply the inclusion-normalized first-term comparison. The normalized derived boundary
comes from exists_injectiveBoundary and injectiveBoundary_exact, and Mathlib's δ_apply
gives the positive differential-of-a-lift formula in every integer degree.

The local proof-context additions are documented in
coord/changes/K9-proetale-support-global-boundary-proof-context.md; the required
consumer check reports zero current Lean importers, with the DAG parents retained.

Updated the existing DAG proof steps to record the split-sequence argument. No other
module is adapted, and no public helper or new node is added. Local irreducibility
attributes and proved component equations in the triangle proof keep the derived,
quotient, sheaf-operation and comparison constructions abstract, as in the existing
localization proof.

## Proved and sorry left

Closed these six original holes, all in namespace AlgebraicGeometry.ProEtale and node
lem-pur-proetale-support-global-boundary:

- supportGlobalOpenSectionIso_naturality
- supportGlobalRestriction_zero
- supportGlobalModels_kInjective
- supportGlobalTriangleComparison
- supportGlobalComparisonNatural
- supportGlobalBoundaryNormalization

Holes added: zero. Holes left in the delivered module: zero. This is a proof, not a
decomposition. Dependency theorems retain their existing proof status.

## No longer needed

Removed the proof-only imports Sheaf.CategoryTheory.RingedSiteInjectiveMonoRestriction
and Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed. Their corresponding direct proof
dependencies lem-pur-ringed-site-injective-mono-restriction and
lem-weil-pbc-proetale-ringed-open-closed are removed from this node's proof steps and top-level tool_uses approvals.
Restriction surjectivity is proved directly using free module presheaves and exact
sheafification. Open inverse-image injectivity uses the published weakly-etale theorem.
These modules may still be needed elsewhere; no module is withdrawn.

The direct dependencies lem-weil-pbc-complex-ses-long-exact-naturality and
lem-weil-pbc-kinjective-hom-derived are also unnecessary. Monic/epic cancellation proves
the two chain-level comparison squares, and the normalized-boundary interface already
supplies a natural transformation on the derived category.

Removed redundant direct proof imports (still publicly available through retained modules):

- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
- WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift
- Mathlib.Algebra.Category.ModuleCat.Adjunctions
- Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
- Sheaf.AlgebraicGeometry.PurSupportExact
- Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
- Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
- Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
- Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
- Mathlib.Algebra.Homology.HomologySequenceLemmas
- Mathlib.Algebra.Homology.DerivedCategory.KInjective

The intermediate claim that the cone itself must be termwise injective is unnecessary:
degreewise splittings, the proved split-sequence boundary theorem, and shift-compatible
derived units compare the third arrows directly. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The listed lemmas exist and the original public statements are retained. The generic
long exact support theorem is stated only for its specified finite quotient coefficient
rings, so it cannot directly produce the arbitrary finite-ring boundary requested here.
Its published generic normalized-boundary interface does, and gives exactly the same
unit-normalized snake boundary without strengthening a hypothesis.

No statement is disputed. The constructions also apply to the zero ring, the empty
open or closed member of the pair, zero complexes, and arbitrary negative degrees.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
