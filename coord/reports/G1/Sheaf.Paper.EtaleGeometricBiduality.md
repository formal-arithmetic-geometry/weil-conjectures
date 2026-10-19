## What changed

Proved WeilConjectures.finite_stage_etale_geometric_biduality in the assigned module.
The existing source VerdierBiduality theorems already supply the geometric induction and
preservation. Private proved bridges identify the constructibility and Tor predicates and
verify that the coefficient exponent is invertible. Generic categorical assembly constructs
the restricted anti-equivalence and its inclusion comparison. Ambient exactness is obtained
from the existing identity-scalar-extension internal-Hom comparison.

Repaired FiniteEtaleGeometricBiduality to name the canonical source evaluation transpose
and factor repeated categorical clauses through GeometricBidualityConclusion. The precise
old and new definitions, proof of their mathematical agreement, all consumers, and the
scope of statement review are in
coord/changes/G1-etale-geometric-biduality-canonical-presentation.md.

Verification: item compiled without warnings or errors in 9.0 s; the original direct
consumer Sheaf.Paper.FiniteStageVerdierBiduality compiled unchanged in 7.6 s. The latter
was only copied temporarily for checking and is not part of this delivery. All original
public imports and the theorem signature are retained. No other group's module is edited.

## Proved and sorry left

Closed 1 original hole: WeilConjectures.finite_stage_etale_geometric_biduality
(node thm-weil-etale-geometric-biduality). All its private helpers are proved.
Remaining sorry in the item: none (0). Holes added: none (0). Split-off holes: none (0).
This is a proof using existing declarations, not a decomposition. The new DAG attachment
records existing source proofs; it adds no Lean declaration or hole. The ambient pairing
and internal-Hom comparison are existing stated dependencies and retain their own items.

## No longer needed

The direct geometric reconstruction is unnecessary because the source library already
implements it, with the same canonical transformation. No unit statement or realized unit
proof step is bypassed: the unit has empty realized.statement/steps, and the source proof
performs the geometric dimension induction and prior preservation. Its two public source
results are explicitly attached by the new node. Nodes listed here are no longer direct
proof dependencies of this item; this does not claim they are unused elsewhere or absent
from the source theorem's own proof.

Removed proof imports (110; all public imports are retained):

- Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
- Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
- Mathlib.Algebra.Homology.DerivedCategory.TStructure
- Mathlib.Algebra.Homology.ShortComplex.ShortExact
- Mathlib.AlgebraicGeometry.Fiber
- Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
- Mathlib.AlgebraicGeometry.Morphisms.Immersion
- Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
- Mathlib.AlgebraicGeometry.Noetherian
- Mathlib.AlgebraicGeometry.OpenImmersion
- Mathlib.AlgebraicGeometry.Properties
- Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
- Mathlib.CategoryTheory.Sites.Point.Basic
- Mathlib.CategoryTheory.Sites.Point.Skyscraper
- Mathlib.Topology.Constructible
- Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.Algebra.Homology.KFlatTelescopeClosure
- Sheaf.AlgebraicGeometry.AbelianSheavesGModules
- Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction
- Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
- Sheaf.AlgebraicGeometry.ClosedPointField
- Sheaf.AlgebraicGeometry.CompactifiableOverField
- Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSupport
- Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullback
- Sheaf.AlgebraicGeometry.CoordinateGenericDimension
- Sheaf.AlgebraicGeometry.DerivedCategories
- Sheaf.AlgebraicGeometry.DimensionExtension
- Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
- Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
- Sheaf.AlgebraicGeometry.EtaleClosedCoprojection
- Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
- Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing
- Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
- Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed
- Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
- Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
- Sheaf.AlgebraicGeometry.EtaleLocalDualInterval
- Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
- Sheaf.AlgebraicGeometry.EtaleTwistedBidualTransport
- Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
- Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
- Sheaf.AlgebraicGeometry.OpenClosedRecollement
- Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
- Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest
- Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor
- Sheaf.AlgebraicGeometry.SmoothTensorDuality
- Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition
- Sheaf.CategoryTheory.DerivedCategory.NoetherianFlatComplexPerfect
- Sheaf.CategoryTheory.ExactCoupleConvergence
- Sheaf.CategoryTheory.Filtration
- Sheaf.CategoryTheory.RingedDerivedRestriction
- Sheaf.CategoryTheory.RingedSiteModules
- Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
- Sheaf.CategoryTheory.TruncationCouple
- Sheaf.CategoryTheory.TruncationHypercohomology
- Sheaf.Paper.CoefficientFrobenius
- Sheaf.Paper.DeltaProperPushforward
- Sheaf.Paper.DeltaRestriction
- Sheaf.Paper.DirectImageTorAmplitude
- Sheaf.Paper.FiniteDirectImageComposition
- Sheaf.Paper.KFlatRingedToposPullback
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.Paper.RingedTopoiDerivedTensorPullback
- Sheaf.Paper.SfHomTriangulated
- Sheaf.Paper.StratumAmbientHom
- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
- WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure
- WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
- WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
- WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
- WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology
- WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
- WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
- WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
- WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
- WeilConjectures.CategoryTheory.Sites.PullbackFlat
- WeilConjectures.CategoryTheory.TruncationHypercohomology
- WeilConjectures.Compactification.Defs
- WeilConjectures.Compactification.NagataCompactification
- WeilConjectures.ConstructibleSheaf.KernelCokernel
- WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo
- WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
- WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
- WeilConjectures.Mathlib.CategoryTheory.EssentialImage
- WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
- WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
- WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
- WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
- WeilConjectures.Mathlib.CategoryTheory.Whiskering
- WeilConjectures.Mathlib.Topology.KrullDimension
- WeilConjectures.SixFunctors.Etale.Derived.Coefficients
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
- WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
- WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
- WeilConjectures.SixFunctors.Etale.Derived.Tensor
- WeilConjectures.SixFunctors.Etale.Derived.TensorHom
- WeilConjectures.SixFunctors.Etale.Derived.Triangulated
- WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
- WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

Pruned direct proof nodes and their declared modules (retained statement dependencies
are excluded from this list):

| node | module or leaf |
|---|---|
| cor-amb-affine-space-adjunction | Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction |
| def-nagata-compactification | WeilConjectures.Compactification.Defs |
| def-nagata-scheme-theoretic-closure | Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme |
| def-sbc-standard-tstructure-derived-category | Mathlib: DerivedCategory.TStructure.t |
| def-weil-constructible-subset | Mathlib: Topology.IsConstructible |
| def-weil-pbc-direct-image | WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs |
| def-weil-pbc-extension-by-zero | WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs |
| def-weil-sheaf-of-modules-category | Sheaf.CategoryTheory.RingedSiteModules |
| lem-asd-etale-finite-twist-pullback | Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback |
| lem-cbc-open-closed-recollement | Sheaf.AlgebraicGeometry.OpenClosedRecollement |
| lem-exc-abelian-sheaves-gmodules | Sheaf.AlgebraicGeometry.AbelianSheavesGModules |
| lem-exc-closed-ambient | Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint |
| lem-fin-coordinate-generic-dimension | Sheaf.AlgebraicGeometry.CoordinateGenericDimension |
| lem-kun-closed-point-field | Sheaf.AlgebraicGeometry.ClosedPointField |
| lem-kun-derived-tensor-triangulated | WeilConjectures.SixFunctors.Etale.Derived.Triangulated |
| lem-kun-dimension-extension | Sheaf.AlgebraicGeometry.DimensionExtension |
| lem-kun-dimension-finite-type | WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType |
| lem-pc-kflat-closure | Sheaf.Algebra.Homology.KFlatTelescopeClosure |
| lem-pc-noetherian-flat-complex-perfect | Sheaf.CategoryTheory.DerivedCategory.NoetherianFlatComplexPerfect |
| lem-pod-etale-stalk-tensor-scalar | Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar |
| lem-pur-etale-open-derived-tensor | WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection |
| lem-sc-scheme-sober | Mathlib: AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat, AlgebraicGeometry T0Space instance, IsGenericPoint.eq |
| lem-sf-derived-homology-long-exact | Mathlib: DerivedCategory.HomologySequence.exact₂ |
| lem-sf-etale-direct-image-vanishing | Sheaf.AlgebraicGeometry.EtaleDirectImageVanishing |
| lem-sf-etale-flat-model | WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel |
| lem-sf-etale-generic-exchange-algclosed | Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed |
| lem-sf-etale-local-dual-interval | Sheaf.AlgebraicGeometry.EtaleLocalDualInterval |
| lem-sf-etale-smooth-stratified-ctf | Sheaf.AlgebraicGeometry.SmoothStratificationFiniteTor |
| lem-sf-etale-twisted-bidual-transport | Sheaf.AlgebraicGeometry.EtaleTwistedBidualTransport |
| lem-sf-hom-triangulated | Sheaf.Paper.SfHomTriangulated |
| lem-sf-unbounded-compact-support-proper-composition | Sheaf.AlgebraicGeometry.UnboundedCompactSupportProperComposition |
| lem-weil-coefficient-frobenius | Sheaf.Paper.CoefficientFrobenius |
| lem-weil-delta-proper-pushforward | Sheaf.Paper.DeltaProperPushforward |
| lem-weil-delta-restriction | Sheaf.Paper.DeltaRestriction |
| lem-weil-derived-direct-image-composition | Sheaf.Paper.FiniteDirectImageComposition |
| lem-weil-pbc-constructible-etale-set-pullback | Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullback |
| lem-weil-pbc-constructible-module-support-constructible | Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSupport |
| lem-weil-pbc-derived-direct-image-triangulated | WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus |
| lem-weil-pbc-extension-by-zero-exact | WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs |
| lem-weil-pbc-extension-by-zero-stalks | WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison |
| lem-weil-pbc-finite-type-over-noetherian | Mathlib: AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian; AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace; AlgebraicGeometry.IsNoetherian (class); instance IsNoetherian (Spec R) for IsNoetherianRing R |
| lem-weil-pbc-inverse-image-stalk-germ | WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm |
| lem-weil-pbc-noetherian-finitely-many-components | Mathlib: AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian |
| lem-weil-pbc-ringed-pullback-preserves-kflat | Sheaf.Paper.KFlatRingedToposPullback |
| lem-weil-pbc-ringed-topoi-derived-tensor-pullback | Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses |
| lem-weil-pbc-small-module-diagrams-grothendieck | Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck |
| lem-weil-pbc-zero-dimensional-cohomology | WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology |
| lem-weil-stratum-ambient-hom | Sheaf.Paper.StratumAmbientHom |
| lemma-nagata-immersion-open-in-scheme-image | Mathlib.AlgebraicGeometry.Morphisms.Immersion |
| lemma-weil-pbc-geometric-stalk-conservative | WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint |
| prop-weil-pbc-geometric-stalks-exact | Mathlib: CategoryTheory.GrothendieckTopology.Point.instPreservesFiniteLimitsSheafSheafFiberOfLocallySmallOfHasFiniteLimitsOfAB5OfSize; CategoryTheory.GrothendieckTopology.Point (instance (Φ.sheafFiber).IsLeftAdjoint); CategoryTheory.ShortComplex.ShortExact.map_of_exact |
| prop-weil-pbc-inverse-image-modules-exact | WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact |
| sk-lem-coprojection | Sheaf.AlgebraicGeometry.EtaleClosedCoprojection |
| thm-amb-etale-exceptional-adjoint | WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint |
| thm-asd-smooth-tensor | Sheaf.AlgebraicGeometry.SmoothTensorDuality |
| thm-constructible-serre | WeilConjectures.ConstructibleSheaf.KernelCokernel |
| thm-nagata-compactification | WeilConjectures.Compactification.NagataCompactification |
| thm-sf-direct-image-tor-amplitude | Sheaf.Paper.DirectImageTorAmplitude |
| thm-sp-truncation-e2 | WeilConjectures.CategoryTheory.TruncationHypercohomology |

All prior tool_uses approvals absent from the new proof_deps are removed, in their
original order; these are precisely the obsolete direct tools in the table above.
The new proof imports EtaleHomThickLocus instead of SfHomTriangulated: the latter is in
the SheafOfModules encoding, whereas the item uses Sheaf (ModuleCat A).

## Where the brief, the DAG or earlier work was wrong

The earlier attempted compatibility bridge was not a missing geometric theorem: it was
an expensive comparison of two presentations of the same canonical map. No new unproved
compatibility module is delivered. The earlier sandbox helper was never in the shared
library and has been removed from the deliverable sources. The source library already
proves the geometric assertions; the original DAG planned to rebuild them independently.
The statement of the node is unchanged; only its implementation presentation is repaired.
The old proof docstring is replaced with the route actually used.

The retained sandbox contains searches from earlier resumed attempts, while the current
.budget.start is 2026-10-19 17:07:48 UTC. This reference-clock refresh occurred before this
resumed turn; the retained .brief2, .brief3, .brief4 and .brief5 files identify the earlier
brief versions but carry no provider attempt identifiers. No budget or launcher file was
edited, and useful proof work continued without waiting for a time gate.

## New nodes

lem-sf-finite-ring-geometric-duality attaches the two already proved declarations
AlgebraicGeometry.Etale.isIso_verdierDualDoubleDual_app and
AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual from the source module
WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality. It records the broader finite-ring
geometric isomorphism and preservation used before categorical assembly, not the item's
full exact anti-equivalence conclusion. No new Lean module or sorry is introduced. The
whole-blueprint biduality search found the specialized item, its parent, and the global
preservation node; none states this general finite-ring source result with its existing
source attachment. Mathlib searches found no geometric duality theorem.

Change record: coord/changes/G1-etale-geometric-biduality-canonical-presentation.md.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
