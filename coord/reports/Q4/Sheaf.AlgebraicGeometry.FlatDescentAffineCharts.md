## What changed

Proved AlgebraicGeometry.exists_flat_descent_affine_charts with its original signature.
A private finite_affine_triples lemma chooses nested affine neighbourhoods and extracts a
finite subcover using Mathlib compactness. For each triple the proved chart comparison
constructs the actual section rings, their algebra maps, and finite-presentation certificate.
The already proved exists_affineOpen_directedRingSystem supplies the compatible ring
system and its colimit presentation. A proved general open-triple tensor comparison
identifies the restricted stage and limit arrows with the tensor-product spectrum arrows.
Flat.SpecMap_iff, arrow-isomorphism invariance, restriction, and iff_exists_resLE finish
the two implications, including the empty-source case without a separate assumption.

Moved FlatDescentChart and its three predicate definitions verbatim into a publicly
re-exported FlatDescentChart module to avoid an import cycle. The change record is
coord/changes/flat-descent-chart-relocation.md. No existing module other than this item
is edited. The original DescendFlatFinitePresentation caller is compiled against the
new overlay. Added the fully proved modules FlatDescentChartComparison and
AffineTripleTensorBaseChange. The latter imports all of AffineBasePieceTensorBaseChangeInstance for proof use and
applies its existing private tensor_pullback_arrow theorem; no duplicate is declared;
the open-source comparison is new and permits U₀ strictly smaller than f₀⁻¹(V₀).

## Proved and sorry left

Closed the only original hole:
AlgebraicGeometry.exists_flat_descent_affine_charts
(node lem-weil-pbc-flat-descent-affine-charts).

Also fully proved AlgebraicGeometry.exists_flat_descent_chart_comparison
(node lem-weil-pbc-flat-descent-chart-comparison),
AlgebraicGeometry.affine_triple_tensor_base_change
(node lem-weil-pbc-affine-triple-tensor-base-change), and the private
finite_affine_triples helper. The tensor_pullback_arrow helper is reused from the library.

Original holes closed: 1. New holes added: 0. No sorry remains in any delivered module.
This is a complete proof, not a decomposition into unproved statements.
#print axioms AlgebraicGeometry.exists_flat_descent_affine_charts reports exactly
[propext, Classical.choice, Quot.sound]. All four files compile without warnings
through lcompile.py. The dry run also runs its declaration-wide axiom probe.

Resumed-worker validation (2026-10-13): reread all four delivered modules, the
original theorem and chart definitions, the existing directed-ring-system proof,
the node routes, and the unit realized list. Recompiled the entire sandbox through
lcompile.py --all: all four files compiled cleanly. The delivery dry run printed OK;
its only pending requirement is the independent second reading. Nothing was pushed.

## No longer needed

Deleted the duplicate private tensor_pullback_arrow declaration from
AffineTripleTensorBaseChange and reused the existing theorem by a proof-only import all.
Its host module remains needed; no duplicate tensor proof or new node is required.

Removed the proof import Sheaf.AlgebraicGeometry.LimitAffineTransition. The supplied
cone is already limiting, so the coordinate-ring comparison uses the proved
AffineOpenDirectedRingSystem instead of constructing a new limit by relative spectra.
The node lem-weil-pbc-limit-affine-transition is no longer a direct proof dependency;
its existence branch is not used by either new lemma. The new nodes retain the
open-fibre-product and affine-spectrum route of the original argument. The ring
colimit, finite-presentation, and tensor-product public imports moved to the chart-data
module; redundant copies were removed from the item. No blueprint unit statement
or realized step is bypassed.

The following modules leave this item’s import closure on the current delivery base.
This is local pruning; no global pruning count is asserted.

- `Mathlib.Algebra.Category.Grp.AB`: (no module record in the DAG)
- `Mathlib.Algebra.Category.Grp.Abelian`: (no module record in the DAG)
- `Mathlib.Algebra.Category.Grp.Colimits`: (no module record in the DAG)
- `Mathlib.Algebra.Category.Grp.FilteredColimits`: `lem-weil-pbc-abelian-groups-forget-filtered-colimits`
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.FilteredColimits`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`: `def-weil-presheaf-modules-sheafification`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Projective`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`: `def-weil-pbc-module-finite-type-presentation`, `def-weil-pbc-generating-sections`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`: (no module record in the DAG)
- `Mathlib.Algebra.Category.ModuleCat.Stalk`: `lem-pc-filtered-colimit-varying-ring-modules`
- `Mathlib.Algebra.Category.ModuleCat.Ulift`: (no module record in the DAG)
- `Mathlib.Algebra.Category.Ring.Constructions`: (no module record in the DAG)
- `Mathlib.Algebra.Category.Ring.FilteredColimits`: (no module record in the DAG)
- `Mathlib.Algebra.Category.Ring.Limits`: (no module record in the DAG)
- `Mathlib.Algebra.Exact.Basic`: (no module record in the DAG)
- `Mathlib.Algebra.Group.Int.Defs`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.Additive`: `def-weil-pbc-chain-complex-tensor-module`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.DerivedCategory.Plus`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`: `lem-weil-pbc-complex-ses-triangle`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.Double`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.ExactSequence`: `def-weil-pbc-exact-sequence`
- `Mathlib.Algebra.Homology.HomologicalComplexAbelian`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.HomotopyCategory`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.HomotopyCategory.Plus`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.HomotopyCategory.Shift`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.Localization`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.QuasiIso`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.Refinements`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.SingleHomology`: (no module record in the DAG)
- `Mathlib.Algebra.Homology.SpectralObject.Basic`: (no module record in the DAG)
- `Mathlib.Algebra.Module.FinitePresentation`: (no module record in the DAG)
- `Mathlib.Algebra.Module.LocalizedModule.Exact`: (no module record in the DAG)
- `Mathlib.Algebra.Module.TransferInstance`: (no module record in the DAG)
- `Mathlib.AlgebraicGeometry.AffineScheme`: (no module record in the DAG)
- `Mathlib.AlgebraicGeometry.Modules.Presheaf`: (no module record in the DAG)
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `lem-weil-pbc-module-restriction-open-immersion-colimits`, `def-weil-sheaf-of-modules-category`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `lem-weil-pbc-spec-module-tilde-sections`, `lem-weil-pbc-affine-tilde-gamma-adjunction`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: (no module record in the DAG)
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `lemma-nagata-open-immersion-qc-over-separated-target`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `lem-weil-pbc-closed-immersion-from-composite`
- `Mathlib.AlgebraicGeometry.Noetherian`: `pqf-def-locnoeth`
- `Mathlib.AlgebraicGeometry.PullbackCarrier`: (no module record in the DAG)
- `Mathlib.AlgebraicGeometry.RelativeGluing`: (no module record in the DAG)
- `Mathlib.AlgebraicGeometry.Restrict`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Abelian.ShortExact`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Adjunction.Additive`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Adjunction.Limits`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Adjunction.Unique`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Comma.Over.Basic`: (no module record in the DAG)
- `Mathlib.CategoryTheory.ConcreteCategory.EpiMono`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Filtered.Basic`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`: `lem-category-theory-concrete-iscolimit-exists-rep`
- `Mathlib.CategoryTheory.Limits.Constructions.Over.Connected`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.ExactFunctor`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.Final`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.FullSubcategory`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.IsConnected`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.Lattice`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.Preserves.Basic`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Limits.Shapes.Kernels`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Localization.Adjunction`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Localization.LocalizerMorphism`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Localization.Monoidal.Braided`: (no module record in the DAG)
- `Mathlib.CategoryTheory.ObjectProperty.ContainsZero`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Shift.CommShift`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.Abelian`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.Continuous`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.Descent.DescentData`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.Equivalence`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.LeftExact`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.Limits`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.LocallySurjective`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.Over`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.PreservesSheafification`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.Pullback`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.SheafHom`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Sites.Sheafification`: `def-weil-pbc-sheafification`
- `Mathlib.CategoryTheory.Sites.Subsheaf`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Subobject.Basic`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Triangulated.HomologicalFunctor`: `lem-sp-long-exact-of-triangle`
- `Mathlib.CategoryTheory.Triangulated.SpectralObject`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Triangulated.Subcategory`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT`: (no module record in the DAG)
- `Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE`: (no module record in the DAG)
- `Mathlib.Geometry.RingedSpace.Basic`: (no module record in the DAG)
- `Mathlib.LinearAlgebra.Matrix.Rank`: (no module record in the DAG)
- `Mathlib.LinearAlgebra.Span.Basic`: (no module record in the DAG)
- `Mathlib.LinearAlgebra.TensorProduct.Basic`: (no module record in the DAG)
- `Mathlib.LinearAlgebra.TensorProduct.Map`: (no module record in the DAG)
- `Mathlib.RingTheory.Finiteness.Projective`: (no module record in the DAG)
- `Mathlib.RingTheory.Flat.EquationalCriterion`: (no module record in the DAG)
- `Mathlib.RingTheory.Flat.Localization`: (no module record in the DAG)
- `Mathlib.RingTheory.Flat.Stability`: (no module record in the DAG)
- `Mathlib.RingTheory.Ideal.Quotient.Operations`: (no module record in the DAG)
- `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`: (no module record in the DAG)
- `Mathlib.RingTheory.LocalProperties.FinitePresentation`: (no module record in the DAG)
- `Mathlib.RingTheory.Localization.BaseChange`: (no module record in the DAG)
- `Mathlib.RingTheory.Localization.Finiteness`: (no module record in the DAG)
- `Mathlib.RingTheory.Polynomial.Basic`: (no module record in the DAG)
- `Mathlib.RingTheory.Spectrum.Prime.FreeLocus`: (no module record in the DAG)
- `Mathlib.RingTheory.TensorProduct.Basic`: (no module record in the DAG)
- `Mathlib.RingTheory.TensorProduct.DirectLimitFG`: (no module record in the DAG)
- `Mathlib.Tactic.IrreducibleDef`: (no module record in the DAG)
- `Mathlib.Topology.Category.TopCat.Opens`: (no module record in the DAG)
- `Mathlib.Topology.Sheaves.Abelian`: (no module record in the DAG)
- `Mathlib.Topology.Sheaves.Functors`: `def-weil-pbc-topological-inverse-image`
- `Mathlib.Topology.Sheaves.LocallySurjective`: (no module record in the DAG)
- `Mathlib.Topology.Sheaves.Presheaf`: (no module record in the DAG)
- `Mathlib.Topology.Sheaves.Sheaf`: (no module record in the DAG)
- `Mathlib.Topology.Sheaves.SheafCondition.Sites`: (no module record in the DAG)
- `Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing`: (no module record in the DAG)
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullback`: `lem-pc-presheaf-module-inverse-image-adjunction`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackComparison`: `lem-pc-topological-module-pullback-comparison`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackRepresentatives`: `lem-pc-topological-pullback-common-representatives`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction`: `lem-pc-module-change-of-rings-adjunction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`: `def-pur-sheaf-tensor-product`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback`: `lem-pc-module-inverse-image-adjunction`
- `Sheaf.Algebra.Homology.OpenCoverAdjunctionTriangle`: `lem-sc-open-cover-adjunction-triangle`
- `Sheaf.Algebra.Homology.OpenCoverMateComplexShortExact`: `lem-sc-open-cover-mate-complex-short-exact`
- `Sheaf.Algebra.Homology.OpenCoverMateModuleShortExact`: `lem-sc-open-cover-mate-module-short-exact`
- `Sheaf.Algebra.Homology.OpenCoverMateModuleShortExactCore`: `lem-sc-open-cover-mate-module-counit-compatibility`, `lem-sc-open-cover-mate-module-short-exact-core`
- `Sheaf.Algebra.Homology.OpenDerivedMatePresentation`: `lem-sc-localization-nested-adjunction-mate`
- `Sheaf.Algebra.Homology.OpenExtensionCounitStalk`: `lem-sc-open-extension-counit-stalk`
- `Sheaf.Algebra.Homology.OpenHomTriangleRealization`: `lem-sc-open-hom-triangle-realization`
- `Sheaf.AlgebraicGeometry.AffineAlgebraLocalMaps`: `lem-weil-pbc-affine-algebra-local-maps`
- `Sheaf.AlgebraicGeometry.AffineMorphismRelativeSpec`: `lem-weil-pbc-affine-morphism-relative-spec`
- `Sheaf.AlgebraicGeometry.AffineOverLimitInclusion`: `lem-weil-pbc-affine-over-limit-inclusion`
- `Sheaf.AlgebraicGeometry.AffineStructureAlgebraFullyFaithful`: `lem-weil-pbc-affine-structure-algebra-fully-faithful`
- `Sheaf.AlgebraicGeometry.Coherent`: `pqf-def-coherent`
- `Sheaf.AlgebraicGeometry.CommAlgebraSheaf`: `def-weil-pbc-comm-algebra-sheaf`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`: `lem-weil-pbc-limit-affine-transition-core`, `lem-weil-pbc-limit-affine-transition`, `lem-weil-pbc-limit-affine-transition-affine-comparison`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineChartUnit`: `lem-weil-pbc-module-pullback-affine-chart-unit`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`: `lem-weil-pbc-module-pullback-affine-sections`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSectionsBijective`: `lem-weil-pbc-module-pullback-affine-sections-bijective`
- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`: `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange`: `lem-weil-pbc-quasi-coherent-affine-section-base-change`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebra`: `def-weil-pbc-quasi-coherent-algebra`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraAffineInclusion`: `lem-weil-pbc-quasi-coherent-algebra-affine-inclusion`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraColimit`: `lem-weil-pbc-quasi-coherent-algebra-colimit`
- `Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections`: `lem-weil-pbc-quasi-coherent-module-colimit-affine-sections`
- `Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitEvaluation`: `lem-weil-pbc-quasi-coherent-module-colimit-evaluation`
- `Sheaf.AlgebraicGeometry.QuasicoherentPushforwardQcqs`: `pqf-lem-pushforward-qcoh`
- `Sheaf.AlgebraicGeometry.QuasicoherentSectionPowerExtension`: `pqf-lem-qcoh-qcqs-section-power-extension`
- `Sheaf.AlgebraicGeometry.QuasicoherentSectionPowerTorsion`: `pqf-lem-qcoh-compact-section-power-torsion`
- `Sheaf.AlgebraicGeometry.RelativeSpecMorphismChart`: `lem-weil-pbc-relative-spec-morphism-chart`
- `Sheaf.AlgebraicGeometry.RelativeSpectrumAffineRealization`: `lem-weil-pbc-relative-spectrum-affine-realization`
- `Sheaf.AlgebraicGeometry.RelativeSpectrumStructureAlgebra`: `lem-weil-pbc-relative-spectrum-structure-algebra`
- `Sheaf.AlgebraicGeometry.TensorPullback`: `lem-pc-module-pullback-identity-composition`, `def-pc-module-pullback`
- `Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`: `lem-pc-module-pullback-adjunction`
- `Sheaf.CategoryTheory.CommAlgebraSheafModule`: `def-weil-pbc-ringed-space-algebra-module`
- `Sheaf.CategoryTheory.ExtensionByZeroPresheaf`: `def-weil-extension-by-zero-presheaf`
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`: `lem-pur-site-restriction-module-adjunction-exact`
- `Sheaf.CategoryTheory.PresheafChangeOfRingsAdjunction`: `lem-pc-presheaf-change-of-rings-adjunction`
- `Sheaf.CategoryTheory.SheafAlgebrasDirectedColimit`: `lem-weil-pbc-sheaf-algebras-directed-colimit`
- `Sheaf.CategoryTheory.SheafAlgebrasDirectedColimitAlgebraCore`: `stage3-sheaf-algebras-directed-colimit-algebra-core`
- `Sheaf.CategoryTheory.SheafAlgebrasDirectedColimitModuleCore`: `stage3-sheaf-algebras-directed-colimit-module-core`
- `Sheaf.CategoryTheory.SiteExtensionByZeroExact`: `lem-weil-pbc-site-extension-by-zero-exact`
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf`: `def-weil-pbc-site-extension-by-zero-presheaf`
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheafAdjoint`: `lem-weil-pbc-site-extension-by-zero-presheaf-adjoint`
- `Sheaf.Paper.DerivedHomMayerVietoris`: `lem-sc-derived-hom-mayer-vietoris`
- `Sheaf.Paper.SiteRestrictionExact`: `lem-weil-pbc-site-restriction-exact`
- `Sheaf.Topology.InverseImageModule`: `def-pc-topological-inverse-image-module`
- `Sheaf.Topology.InverseImageOperationExt`: `lem-pc-inverse-image-operation-ext`
- `Sheaf.Topology.InverseImagePresheafModule`: `lem-pc-inverse-image-presheaf-module`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom`: (no module record in the DAG)
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: `def-pur-sheaf-hom`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`: `lem-weil-pbc-module-tensor-symmetric-monoidal`
- `WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator`: `def-sc-local-free-generator`
- `WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine`: `lem-pc-finite-flat-affine-sections-projective`, `lem-pc-affine-sections-finite-locally-free-criterion`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde`: `lem-weil-pbc-pushforward-spec-global-sections`
- `WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit`: (no module record in the DAG)
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel`: `lem-weil-pbc-quasi-coherent-module-cokernel-closure`
- `WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`: `lem-pc-quasicoherent-module-coproducts`, `lem-pqf-kernel-finite-presentation-noetherian`, `pqf-lem-qcoh-principal-open-criterion`, `lem-weil-pbc-quasi-coherent-module-coproduct-closure`, `lem-weil-pbc-quasicoherent-epi-affine-cover`, `lem-weil-pbc-quasi-coherent-module-kernel`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`: `lem-weil-pbc-termwise-adjunction-homotopy`
- `WeilConjectures.FromJoel.Algebra.Homology.Double`: (no module record in the DAG)
- `WeilConjectures.FromJoel.Algebra.Homology.DoubleHomology`: (no module record in the DAG)
- `WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso`: (no module record in the DAG)
- `WeilConjectures.FromJoel.CategoryTheory.Limits.ExactFunctor`: (no module record in the DAG)
- `WeilConjectures.FromJoel.CategoryTheory.Localization.LocalizerMorphism`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Projective`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`: `def-sc-finite-locally-free-sheaf`, `def-amb-finite-locally-free-module`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: `lem-weil-pbc-exact-functor-bounded-below`, `def-weil-pbc-derived-inverse-image`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Homology.ExactSequence`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Shift`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Homology.SingleHomology`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Algebra.Module.LocalizedModule.Exact`: (no module record in the DAG)
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`: `lem-weil-pbc-module-restriction-iso-stalk-bijective`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`: `lem-weil-pbc-module-pullback-quasi-coherent`, `lem-weil-pbc-affine-module-basic-open-localization`
- `WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly`: (no module record in the DAG)
- `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Kernels`: (no module record in the DAG)
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: (no module record in the DAG)
- `WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift`: (no module record in the DAG)
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous`: (no module record in the DAG)
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafHom`: (no module record in the DAG)
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject`: (no module record in the DAG)
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.ETrunc`: (no module record in the DAG)
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject`: (no module record in the DAG)
- `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic`: (no module record in the DAG)
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.FreeLocus`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Topology.Category.TopCat.Opens`: (no module record in the DAG)
- `WeilConjectures.Mathlib.Topology.Sheaves.Presheaf`: (no module record in the DAG)

Second-reader dependency accounting: the complete list of original direct proof dependencies
removed from the item node is:

- `lem-weil-pbc-morphism-into-affine-scheme`
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`
- `pqf-def-affine-morphism`
- `def-weil-pbc-category-colimit`
- `lem-weil-pbc-limit-affine-transition`
- `lem-weil-pbc-spec-colimit-limit`
- `def-pc-fibre-product`
- `lem-weil-pbc-open-fibre-product`
- `lem-weil-pbc-fibre-product-affine-spectra`
- `def-pc-scheme`
- `def-weil-pbc-flat-ring-map`

Except for the unnecessary limit-existence construction, these ingredients remain used
inside the proved chart-comparison lemmas or in the unchanged chart definitions. Their
removal from the item node is delegation to those actual proofs, not a claim that their
mathematics or modules disappear from the targets. The local closure list above is
separate from global pruning; no global module-pruning count is asserted here.

## Where the brief, the DAG or earlier work was wrong

The local Stacks source files are absent on this machine. The resumed worker read
[Tag 04AI](https://stacks.math.columbia.edu/tag/04AI),
[Tag 01JR](https://stacks.math.columbia.edu/tag/01JR), and
[Tag 01I4](https://stacks.math.columbia.edu/tag/01I4) directly on the Stacks site:
the finite affine reduction, open pullback intersection, and tensor-spectrum
identification agree with the delivered proofs. No additional source is needed.

The node's mathematical argument is sound, but its existence-of-limit dependency is
unnecessary for a theorem whose hypotheses already provide a limiting cone. Mathlib
and the proved AffineOpenDirectedRingSystem supply the comparison directly. The
existing affine base-piece tensor presentation is not an exact substitute: it assumes
affineness of the entire stage map and uses the full inverse image of a target open,
whereas a locally finitely presented map need not be affine and our chosen source
open can be strictly smaller. The new geometric lemma handles exactly that difference.

The nearest blueprint ancestor is retained from the item's recorded provenance,
lemma-weil-pbc-h1-constructible-representation. Searches over the whole blueprint for
'affine triple', 'tensor product flat', and 'tensor spectra' find no matching blueprint
statement. The broader 'affine open' search was also read and has no matching result.
LeanSearch was unavailable (HTTP 500), recorded as unavailable, not as no match.
LeanFinder, Loogle and grep found the Mathlib restriction, flatness, and tensor-spectrum
ingredients. The library search additionally found the proved coordinate-ring system
and the existing private tensor transport theorem now imported and applied directly.

Edge cases checked: I may be a preorder with a single stage; i₀ ensures the required
upper tail is nonempty. Empty U₀ and W₀ have zero section rings and the pullback/tensor
identities remain valid. If X₀ is empty, the finite subcover is empty and the source-local
flatness criterion has no points to check. No nonempty-open or nonzero-ring hypothesis
was added. No quasi-separatedness is used in the local construction. All original
compactness and quasi-separatedness hypotheses are retained unchanged.

## New nodes

lem-weil-pbc-affine-triple-tensor-base-change records a fully proved comparison for one
open triple after an arbitrary base change. It has no directed-system, finite-presentation,
or flatness assumption or conclusion. Its proof constructs the inverse-image opens,
restricts the pullback squares, and verifies the tensor-map arrow by its two projections.

lem-weil-pbc-flat-descent-chart-comparison records the fully proved construction of one
finite-presentation chart with its stage and limit arrow comparisons. It uses the existing
proved coordinate-ring-system theorem and the preceding proved open-triple comparison.
It needs no compactness and proves no flatness assertion. The original chart-definition
node changes only its Lean module/file location; the original theorem node changes only
its proof, proof_deps and proof_origin. The definition relocation is documented in
coord/changes/flat-descent-chart-relocation.md.

Repair of return X-7a120 (2026-10-13): the previous review accepted a duplicate private
helper, which the landing checker correctly refused. Deleted the entire duplicate
tensor_pullback_arrow proof and imported the existing module with proof-only import all;
Lean resolves the original private theorem without any visibility or signature change.
Updated the geometric node proof and dependencies to record the reused ingredient.
All four repaired modules compile cleanly. The earlier independent reading below
describes the pre-repair delivery; its claim that copying the helper was correct is
superseded by this repair. A new second reading is left to the dispatcher.

## Earlier second reading (a previous round; superseded)

Independent second reader, 2026-10-13. Read all four delivered Lean modules and all four
node files, the original module, the change record, the proved directed-ring-system
construction, the existing affine-base-piece comparison, and sk-thm-p1.realized.
Read the source proofs at [04AI](https://stacks.math.columbia.edu/tag/04AI),
[01JR](https://stacks.math.columbia.edu/tag/01JR), and
[01I4](https://stacks.math.columbia.edu/tag/01I4).

1. Interface preservation: PASS. The diff changes the original theorem only in its proof;
   a byte comparison of its entire signature succeeds, including all compactness,
   quasi-separatedness, universe, directedness, and finite-presentation assumptions.
   The chart structure and all three predicate definitions, including docstrings and
   bodies, are byte-identical after relocation. The public re-export and recorded move
   preserve their names and visibility. Compiled the unchanged original
   DescendFlatFinitePresentation caller against the delivered overlay: no errors or warnings.

2. Proof and axioms: PASS. Independently recompiled all four modules with lcompile.py
   --all, without errors or warnings. Searched all delivered Lean for sorry and forbidden
   declarations/options: none. An independent scratch probe prints exactly propext,
   Classical.choice and Quot.sound for exists_flat_descent_affine_charts,
   exists_flat_descent_chart_comparison, affine_triple_tensor_base_change, and the
   three relocated predicates. Thus no imported sorry is hidden in the proved theorem.
   The chart is constructed from actual section rings and their algebra maps; the
   existential ring-system theorem used for local choices is itself fully proved.

3. New statements and search: PASS. There are no split-off holes. The two new public
   theorems are fully proved strict pieces of the argument: the geometric one has no
   directed system, finite presentation, or flatness; the chart construction has no
   finite cover or flatness. Matched each containment, spectrum compatibility equation,
   stage source-open equality and limit clause between Lean and the node statements.
   In the geometric proof hUW uses Over.w; hVT/hUT remove the extra intersection from
   isPullback_resLE; hfst/hsnd verify both projections of the arrow comparison.
   The tensor helper checks both tensor inclusions, rather than merely object isomorphisms.
   In the chart proof the composite aC=f.appTop.hom.comp aB makes the algebra equation
   reflexive; finitePresentation_appLE supplies exactly its certificate; hB and hC give
   the required compatible models before the stage and limit applications.
   Tested the argument on a singleton index, empty opens/zero section rings, empty X0,
   and U0 strictly contained in f0 inverse-image V0. No step needs a nonzero ring,
   nonempty source, quasi-separated affine intersection, or an affine whole stage map.
   Fresh LeanFinder search for restriction of a base-changed morphism to affine
   neighbourhoods found tensor-spectrum projection ingredients, no matching theorem.
   Loogle search for pullbackSpecIso found its projection lemmas. A qualified-identifier
   Loogle attempt did not recognize isPullback_resLE; direct rg and reading Restrict.lean
   found it. Searched lean/Sheaf/AlgebraicGeometry and Mathlib for affine_triple,
   finite_affine, arrowResLEAppIso, tensor_pullback_arrow and isPullback_resLE.
   The existing AffineBasePieceTensorBaseChangeInstance comparison uses the full
   inverse-image source open, so it cannot replace the independently chosen source
   open here. Its private tensor helper is correctly reused as a proof pattern.

4. Route and pruning: PASS after report clarification. finite_affine_triples builds the
   finite source cover directly from affine neighbourhoods and compactness. The top
   proof restricts flatness at the limit, transports along the arrow isomorphism, and
   applies Flat.SpecMap_iff. Conversely it chooses a covering initial source open at
   the first projection of each stage point, uses hUj to retain that point, then applies
   iff_exists_resLE. This is precisely the finite affine reduction of 04AI; it does not
   invoke eventual flatness. The two proof-only Sheaf imports are plain import, and
   public imports support signatures or the unchanged public definitions. The supplied
   limit is used through the proved AffineOpenDirectedRingSystem, so LimitAffineTransition
   need not be imported. No sk-thm-p1 realized statement or step is removed or bypassed.
   Expanded No longer needed to account explicitly for every removed original direct
   proof dependency and distinguish indirect use, local closure pruning, and global pruning.

5. DAG agreement: PASS. The existing theorem node changes exactly proof, proof_deps,
   proof_origin; the chart-definition node changes only its Lean location. Checked each
   new node's source, searches, creation, provenance, chapter/unit, Lean signature and
   proof-dependency union. The top node records the compact finite cover, chart comparison,
   and local affine flatness steps. The comparison node records the directed ring system,
   section-ring construction, and open-triple base change; the geometric node records
   restriction of pullback squares and tensor-spectrum projection identities. These are
   the actual Lean proofs. No target or mathematical statement changes.

Changes by the second reader: expanded dependency/pruning accounting and added this
independent review with fresh search, caller compilation and axiom evidence. No Lean
proof, definition, signature, import, or node needed repair. Original holes closed: 1;
new holes added: 0; remaining holes in delivered modules: 0.

## Second reading by Q4

1. Interface preservation: PASS. Compared `FlatDescentAffineCharts.lean` with the
repository version: the theorem signature is unchanged byte for byte. The moved
`FlatDescentChart` structure and its `baseFlat`, `stageFlat`, and `limitFlat`
definitions are verbatim, with the relocation recorded in
`coord/changes/flat-descent-chart-relocation.md`. The three added theorem signatures
match their DAG `lean.statement` fields. No caller-facing declaration was weakened or
given an extra hypothesis.

2. Proof and axioms: PASS. Compiled all four delivered modules with
`lcompile.py --all`; the result is clean. Searched the delivered Lean and DAG files
for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, and
`debug.skipKernelTC`; no such declaration occurs in Lean. A fresh probe prints only
`propext`, `Classical.choice`, and `Quot.sound` for the three public theorems and the
three chart predicates. No definition contains postponed data.

3. New statements: PASS. `affine_triple_tensor_base_change` is a strict geometric
open-triple comparison with no directed-system, finite-presentation, or flatness
claim. `exists_flat_descent_chart_comparison` adds the actual section-ring chart and
its stage/limit arrow comparisons, without a finite cover or flatness assertion.
Both are fully proved, have source/docstring explanations and matching DAG nodes, and
are absent from the repository/library under other names. The proofs handle empty
opens and a singleton preorder; the source open may be strictly smaller than the full
inverse image.

4. Route and pruning: PASS. The proof uses the finite affine compactness reduction,
the existing directed-ring-system construction, the new open-triple comparison, and
the existing tensor transport helper. Proof-only imports are plain `import`; removed
imports and dependencies are listed under `## No longer needed`. The unit route and
its realized nodes remain intact. No duplicate tensor helper remains.

5. DAG agreement: PASS. Read all four node files and checked each proof step,
`proof_deps`, `proof_origin`, Lean module/declaration, and the relocation change record
against the source. They agree with the compiled proofs. No holes were added; the
original affine-chart hole and both intermediate holes are closed. Changes made by
this reading: appended this review only; no Lean proof, definition, signature, import,
or node required repair.
