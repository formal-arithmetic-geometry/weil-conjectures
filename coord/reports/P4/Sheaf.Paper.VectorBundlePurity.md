## What changed

`Sheaf.Paper.VectorBundlePurity` now proves the arithmetic characteristic-invertibility
claim and assembles the normalized purity family with its three independent compatibility
laws. Its public theorem signature, conclusion definition and public imports are unchanged.
Four new statement modules separate normalized-family existence, base change, ordered direct
sums and scalar reduction. The parent specializes their finite-ring statements to the
specified coefficient quotient and its reduction maps.

The proof DAG follows these four source portions. No adopted source-library file changes,
no existing declaration is removed, and no definition acquires postponed data.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.vectorBundlePurity`; its module has zero holes.
The private lemma `coefficientChar_isUnit` is proved: the coefficient characteristic divides
a power of the coefficient prime, and that prime is invertible on the base. The final
assembly and coefficient-quotient specializations are complete Lean proofs.

Added four holes, each exactly the body of a named public theorem:

- `WeilConjectures.PurityFiniteSetting.vectorBundleNormalized`
  (`lem-pur-normalized-vector-purity-bundle`).
- `WeilConjectures.PurityFiniteSetting.vectorIntegrationCounit_baseChange`
  (`lem-pur-normalized-vector-purity-base-change`).
- `WeilConjectures.PurityFiniteSetting.vectorIntegrationCounit_directSum`
  (`lem-pur-normalized-vector-purity-direct-sum`).
- `WeilConjectures.PurityFiniteSetting.vectorIntegrationCounit_scalarReduction`
  (`lem-pur-normalized-vector-purity-scalar-reduction`).

This is a decomposition: one original hole closed, four subordinate holes added. The first
contains no compatibility law, and each other theorem contains only one compatibility law
for an already normalized family. None restates the whole parent. There are no holes in
private lemmas, definitions, or retained partial proofs. All five modules compiled together
before final import cleanup; the final packet is checked by the delivery tool.

## No longer needed

Removed these private imports from the parent:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.ScalarExtensionUnitTriangles`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance`
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`
- `Sheaf.AlgebraicGeometry.CompactProjectionExchange`
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction`
- `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`
- `Sheaf.AlgebraicGeometry.ProjectiveLineTrace`
- `Sheaf.AlgebraicGeometry.ShriekTensorComposition`
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.VectorBundleIntegration`
- `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`
- `Sheaf.Paper.DegreeZeroDerivedMapGluing`
- `Sheaf.Paper.EtaleCompactScalarCoherence`
- `Sheaf.Paper.PurityFiniteSetting`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.VectorPurityNormalization`
- `Sheaf.Paper.VectorPurityScalarSingle`
- `Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension`
- `Sheaf.Targets.VectorBundlePurity`

The parent no longer directly applies `thm-amb-vector-bundle-purity`,
`lem-pur-integration-transpose-base-change`, `lem-pur-integration-transpose-composition`,
`lem-pur-integration-transpose-scalar-mate`, or
`lem-pur-finite-tate-scalar-source-normalization`. The new normalized-family node uses
`lem-amb-vector-integration-mate`; the compatibility nodes retain geometric trace, Tate
pullback, compact projection and scalar coherence dependencies as recorded in their DAG.
The existing normalization definition remains a statement dependency. These are changes to
the parent's direct route, not claims that all these modules leave the targets' closure.
No module is withdrawn and no global pruning is claimed. The unit's `realized` statement
and step lists are empty; the source route remains integration, transposition and the three
compatibilities.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies present maps in different coordinates. The integration-mate theorem
orders the coefficient second, while this item's family orders it first. Base change in
the public predicate includes arbitrary Cartesian bundle presentations; the geometric trace
lemma uses canonical pullbacks. Direct sums use literal module biproducts and arbitrary
actual compactification triangles. Scalar reduction specifies ordered shifted Tate powers
and includes the coefficient-unit object. These identifications require proof; they are
recorded in the new source lemmas rather than asserted to hold definitionally.

The new statements retain rank zero, empty base, the zero coefficient ring, N=1, identity
base change and nonflat finite scalar reduction. Their source arguments specialize to unit
or unique maps in the degenerate geometric cases. No statement is disputed or weakened.

## New nodes

`lem-pur-normalized-vector-purity-bundle`, in
`Sheaf.Paper.NormalizedVectorPurityBundle`, isolates the normalized invertible family and its
restricted functor conclusion, before any of the three compatibility laws.

`lem-pur-normalized-vector-purity-base-change`, in
`Sheaf.Paper.NormalizedVectorPurityBaseChange`, isolates the canonical exceptional exchange
equation and its invertibility for an independently normalized family.

`lem-pur-normalized-vector-purity-direct-sum`, in
`Sheaf.Paper.NormalizedVectorPurityDirectSum`, isolates the ordered two-factor formula for
every actual compactification triangle.

`lem-pur-normalized-vector-purity-scalar-reduction`, in
`Sheaf.Paper.NormalizedVectorPurityScalarReduction`, isolates scalar source compatibility,
the exceptional scalar mate, invertibility and the coefficient-unit component. It applies
to finite coefficient maps; the parent specializes it to the specified quotient map.

Each node cites the current blueprint's vector-bundle purity proof and contains the
corresponding proof in words, search records and Lean attachment. No change record is
needed because existing definitions, signatures and public imports are unchanged.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
