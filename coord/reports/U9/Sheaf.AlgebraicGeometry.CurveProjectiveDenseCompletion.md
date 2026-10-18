## What changed

Proved `AlgebraicGeometry.exists_projective_dense_completion_of_dim_le_one` with its
original signature. The completion is the constructed scheme-theoretic image of the
projective-space immersion supplied by `DimOneQuasiProjective`; no witness is chosen
from a postponed existence theorem. Reused the already proved
`AlgebraicGeometry.topologicalKrullDim_le_of_dense` for the dimension bound, and the
source specialization-chain inequality and closed zero-dimensional finiteness theorem
for the boundary. The argument handles empty, nonreduced, reducible and mixed-dimensional
schemes. Injectivity on sections and preservation of reducedness use the existing
scheme-theoretic dominance API.

Updated the theorem docstring and its DAG proof to the implemented route. Added one
DAG attachment for the existing dense-open dimension theorem, without a new Lean module
or a proof hole. All added imports are proof-only; public imports, declarations,
visibility, target statements and definitions are unchanged. No other module is adapted.

Validation: the final sandbox module compiled cleanly through `lcompile.py` in 4.2 s.
The original file also compiled before editing. The initial proof needed two notation
repairs (the opensRange coercion and parentheses around a complement subtype), now fixed.
The required delivery dry run performs the final declaration and axiom probe.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.exists_projective_dense_completion_of_dim_le_one`
(node `lem-weil-pbc-curve-projective-dense-completion`).

Holes added: 0. Holes remaining in the item: 0. Split-offs: 0.
The new node attaches `AlgebraicGeometry.topologicalKrullDim_le_of_dense`, which already
has a complete proof in `WeilConjectures.AlgebraicGeometry.DenseCompactification`.
Existing dependency theorems are used as stated; their proofs are not changed.

## No longer needed

The direct proof dependency `lem-sc-closed-irreducible-dimension-trdeg` and its module
`Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg` are unnecessary for this proof:
the existing dense-open dimension comparison replaces the two residue-field
transcendence-degree calculations. Removed its obsolete top-level tool approval from
the item node. This changes no blueprint unit statement or realized step.

Removed direct proof imports:

- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`

Except for `ClosedIrreducibleDimensionTrdeg`, the removed explicit imports remain
available through the retained imports: they are redundant imports, not withdrawn
mathematical dependencies. `DenseCompactification`, the scheme-theoretic image
complements, and the topology Krull-dimension complements are imported for their
proved APIs. No unused proof-dependency import remains.

For completeness, the following 107 library modules leave this item's import
closure compared with the original module. This is local pruning; other target paths
may still use them, so no global pruning count is claimed here:

- `Mathlib.Algebra.Module.ULift`
- `Mathlib.Algebra.Regular.SMul`
- `Mathlib.AlgebraicGeometry.LimitsOver`
- `Mathlib.AlgebraicGeometry.Morphisms.FlatMono`
- `Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective`
- `Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Mathlib.CategoryTheory.Elements`
- `Mathlib.CategoryTheory.Limits.FinallySmall`
- `Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory`
- `Mathlib.CategoryTheory.Sites.LocalSite`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Category`
- `Mathlib.CategoryTheory.Sites.Point.Comap`
- `Mathlib.CategoryTheory.Sites.Point.Conservative`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Data.Set.Image`
- `Mathlib.FieldTheory.PrimitiveElement`
- `Mathlib.Order.ConditionallyCompleteLattice.Basic`
- `Mathlib.Order.KrullDimension`
- `Mathlib.Order.Preorder.Chain`
- `Mathlib.Order.RelSeries`
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`
- `Mathlib.RingTheory.Artinian.Module`
- `Mathlib.RingTheory.Depth.Rees`
- `Mathlib.RingTheory.Etale.Descent`
- `Mathlib.RingTheory.Finiteness.ModuleFinitePresentation`
- `Mathlib.RingTheory.Flat.Rank`
- `Mathlib.RingTheory.Ideal.AssociatedPrime.Basic`
- `Mathlib.RingTheory.Ideal.AssociatedPrime.Localization`
- `Mathlib.RingTheory.KrullDimension.Module`
- `Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs`
- `Mathlib.RingTheory.Polynomial.IntegralNormalization`
- `Mathlib.RingTheory.Regular.IsSMulRegular`
- `Mathlib.RingTheory.RingHom.PurelyInseparable`
- `Mathlib.RingTheory.Smooth.NoetherianDescent`
- `Mathlib.Topology.Defs.Basic`
- `Mathlib.Topology.Homeomorph.Lemmas`
- `Mathlib.Topology.Irreducible`
- `Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso`
- `Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg`
- `Sheaf.RingTheory.AssociatedPrimeMinimalOfDepth`
- `Sheaf.RingTheory.CmModuleGoodElementNonzerodivisor`
- `Sheaf.RingTheory.CmModuleGoodElementSetup`
- `Sheaf.RingTheory.Depth`
- `Sheaf.RingTheory.DepthLeDimAssociatedPrime`
- `Sheaf.RingTheory.DepthLeSupportDimension`
- `Sheaf.RingTheory.DepthOverQuotientRing`
- `Sheaf.RingTheory.DepthQuotSMulTop`
- `Sheaf.RingTheory.DepthQuotientNonzerodivisor`
- `Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRing`
- `Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRingChains`
- `Sheaf.RingTheory.FiniteTypeDomainDimensionLocalRingLocalization`
- `Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg`
- `Sheaf.RingTheory.GoodElementCuttingParameter`
- `Sheaf.RingTheory.IsRegularOfDimensionDrop`
- `Sheaf.RingTheory.IsRegularSystemOfParameters`
- `Sheaf.RingTheory.IsSMulRegularOfGoodSequence`
- `Sheaf.RingTheory.MaximalChainLengthOfDepth`
- `Sheaf.RingTheory.MaximalChainLengthOfDepthPositive`
- `Sheaf.RingTheory.NonzerodivisorIfMaximalNotAssociated`
- `Sheaf.RingTheory.PolynomialRingMaximalChainHeightDifference`
- `Sheaf.RingTheory.PolynomialRingMaximalLocalizationDimension`
- `Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Coprod`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Cover`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Descent`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.EssSurj`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.FullyFaithful`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Outer`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Reduction`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Section`
- `WeilConjectures.CategoryTheory.ConcreteCategory.FinitelyGenerated`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`
- `WeilConjectures.Mathlib.CategoryTheory.Elements`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.FinallySmall`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.HasLimits`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Category`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Conservative`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `WeilConjectures.Mathlib.Data.Set.Image`
- `WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint`
- `WeilConjectures.Mathlib.RingTheory.Etale.PropertyC`
- `WeilConjectures.Mathlib.RingTheory.Etale.ResidueField`
- `WeilConjectures.Mathlib.RingTheory.Etale.ResidueFieldBaseChange`
- `WeilConjectures.Mathlib.RingTheory.Flat.DescentAlgebra`
- `WeilConjectures.Mathlib.RingTheory.RingHom.PurelyInseparable`
- `WeilConjectures.Mathlib.Topology.Constructible`
- `WeilConjectures.RingTheory.AssociatedPrimePowerQuotient`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
- `WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.UpperLowerStar.Defs`
- `WeilConjectures.Topology.Stratification`

## Where the brief, the DAG or earlier work was wrong

The statement and the planned geometric construction are correct. The DAG's generic
residue-field comparison was unnecessary because a complete general dense-open dimension
comparison already exists in the source library. Its boundary argument can be expressed
directly with the already proved specialization-chain inequality, then the existing
zero-dimensional closed-subset finiteness theorem. No statement repair, disputed statement,
new definition, forced adaptation, or change record is needed.

## New nodes

`lem-weil-pbc-dense-open-dimension-comparison` attaches the existing proved theorem
`AlgebraicGeometry.topologicalKrullDim_le_of_dense`. Its statement includes all locally
finite type and quasi-compact hypotheses and allows the empty scheme. It records the
component-generic-point and reduced-component argument already in that theorem's proof,
its literature sources, and the three actual Mathlib search kinds. A blueprint search
for `dense open dimension` returned no matching node; a search of DAG Lean attachments
also found no existing attachment for this declaration. No new theorem is postponed,
and there are no change-record paths.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
