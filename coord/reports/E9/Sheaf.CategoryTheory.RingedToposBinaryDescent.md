## What changed

Replaced the proof of `CategoryTheory.ringedTopos_binary_descent` by a complete Lean
combination of the fibre construction, local restriction isomorphisms, overlap equation,
local cohomological bounds, and the independent natural lower-shriek triangle. Its
statement and universes are unchanged.

Moved the six existing helper definitions unchanged into
`Sheaf.CategoryTheory.RingedToposBinaryDescentDefs`, publicly reexported by the original
module. The extracted file preserves all nine original public imports. This avoids
cycles between the theorem and the geometric lemmas. The change record is
`coord/changes/ringed-topos-binary-descent-models.md`; all six downstream name searches
list only the item, with zero downstream importers. No existing external consumer or
adopted source declaration is changed.

Added the following source lemmas and proved their Lean bodies:

- `SheafOfModules.siteModuleExtensionByZero_exact`: the actual direct-sum presheaf,
  followed by sheafification, is additive, exact, and left adjoint to restriction,
  allowing the ring universe to differ from the object and Hom universes of the site.
  Its private Hom-equivalence helpers adapt the existing direct-sum proof to this
  interface; no object is chosen from an unproved existence theorem.
- `SheafOfModules.overFunctor_preservesKInjectiveComplexes_ofUniverses`: apply the
  existing exact-left-adjoint criterion to this concrete extension.
- `SheafOfModules.overMap_preservesKInjectiveComplexes_ofUniverses`: relocalization
  preserves K-injectives, by restriction to the iterated slice and its additive
  equivalence with the single slice.
- `SheafOfModules.sliceSheafificationComparisonIndependent_isIso`: generalizes
  the existing unit/local-bijectivity proof of module sheafification comparison to
  separate object and Hom universes for both sites and an independent ring universe.
  Its three data definitions construct the restriction functors and canonical map.
- `CategoryTheory.ringedTopos_ordinaryCross_restriction`: the ordinary overlap map
  becomes invertible on the other slice, for any pullback presentation of U×V.
  The inverse on slice objects is constructed explicitly using X→U and the V-coordinate.
- `CategoryTheory.ringedTopos_directImage_restriction`: proves the two derived counit
  assertions from the existing Grothendieck-abelian theorem, exact restriction, and
  derived full faithfulness; combines them with the remaining derived cross comparison.
- `CategoryTheory.ringedTopos_fibre_restriction`: the projection of a distinguished
  fibre of (a,b) is invertible when b is invertible, by coyoneda exactness and a graph
  section. Applies this on both opens, without a cover or a cohomological long exact
  sequence.

The two remaining geometric results are separate source lemmas for Tags 08DG and
08BU. Each has its own new module, full proof in words, exact Lean statement, searches,
and node. Their statements are proper parts of the original argument: neither gives
a glued object, overlap compatibility, or the cohomological interval conclusion.
The original module proves these conclusions itself.

Compiled the packet in import order through lcompile.py. Axiom probes for the
ordinary cross comparison, concrete exact extension, both K-injective theorems, and
the generalized module sheafification comparison
show only propext, Classical.choice and Quot.sound. The main theorem still uses
sorryAx through the two source lemmas explicitly listed below.
A profiler check of the independent-universe extension proof identified expensive
backward definitional-equality checks; explicit transparency settings make that file
compile within the per-file limit. After a preflight probe timeout, changed the
concrete extension from an abbrev to a definition, so its composite is not expanded
automatically by every consumer. A profiler run with all nine declaration axiom
checks completed in 18 seconds, with only the three allowed axioms. No definition,
statement, or file was split to avoid the limit.

## Proved and sorry left

Original module: one hole, `CategoryTheory.ringedTopos_binary_descent`.
Its proof body is now complete, conditional on the source lemmas below. This is a
decomposition of the original hole, not a claim to an axiom-free proof of binary descent.
One upper hole closed; two lower holes added. There is no `sorry` in the item module,
any definition, or any private helper.

The delivery's only remaining holes are:

- `CategoryTheory.ringedTopos_crossDirectImage_restriction`, node
  `lem-sp-ringed-topos-cross-direct-image-restriction`: passing the proved ordinary
  slice comparison to unbounded derived categories, and identifying it with the
  specified arbitrary restriction models and adjunction mates.
- `CategoryTheory.ringedTopos_binary_descent_triangle`, node
  `lem-sp-ringed-topos-lower-shriek-triangle`: the module Mayer–Vietoris sequence,
  its natural connecting transformation through localization, and transport to
  the specified left adjunctions.

The seven new theorem bodies listed above compile; the ordinary cross comparison,
independent-universe exact extension, and both K-injective corollaries have no new geometric
hypothesis or remaining proof obligation. The direct-image and fibre theorems depend
on the cross-restriction hole, so they are proved reductions, not independent closures
of its mathematics.

## No longer needed

Removed these direct proof imports from the item:

- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Mathlib.CategoryTheory.Sites.CoverLifting`
- `Mathlib.CategoryTheory.Sites.Limits`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.SheafSubcategoryComparison`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact`

The proof uses the site already present in the Lean statement, whose objects include
U,V,W. It therefore avoids the new represented-subterminal-site construction and
`lem-weil-pbc-sheaf-subcategory-comparison` / `lem-weil-pbc-site-sheaf-sets-limits-sectionwise`.
It uses the explicit Mathlib slice adjunction, avoiding the general algebraic inverse
image and `lem-weil-pbc-ringed-topoi-module-adjunction` machinery. Derived full faithfulness
uses the adopted exact-left-adjoint constructor directly; the general K-flat derived
adjunction construction `lem-pc-derived-adjoint-functors` is not used. The fibre proof
uses coyoneda exactness, so `lem-sf-derived-homology-long-exact` is not needed.

The old universe-specialized localized-system exactness and K-injective-resolution
interfaces are not used: the existing independent-universe exact restriction and
Grothendieck-abelian theorem apply directly, while the new concrete extension covers
the remaining independent-ring-universe gap. Extension by zero, slice/module
sheafification, K-injectives, and the SES triangle are still needed by the stated
remaining geometric arguments; they are retained in the appropriate new nodes.

The public imports are preserved transitively through the definitions module.
The following source/Sheaf modules leave this item's import closure when comparing
the repository version with the sandbox overlay. This is a local import comparison,
not a claim that all these modules leave the targets' global closure; other consumers
may retain them. No file or adopted-source declaration is withdrawn.

<details>
<summary>Complete list of modules no longer imported through this item</summary>

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses`
- `Sheaf.Algebra.Homology.AcyclicKFlatTensor`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsAcyclicKFlat`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatClosure`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatResolution`
- `Sheaf.Algebra.Homology.KFlatResolutionGeneral`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`
- `Sheaf.Algebra.Homology.RingedToposAcyclicKFlatPullback`
- `Sheaf.Algebra.Homology.RingedToposAdaptedFlatResolution`
- `Sheaf.Algebra.Homology.RingedToposPullbackFilteredColimits`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Homology.SliceModuleSheafification`
- `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.CoproductCopiesMorphismsClopen`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTowerLimit`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteTowerRepresentation`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleDirectImageLeftExact`
- `Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`
- `Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction`
- `Sheaf.CategoryTheory.AdjunctionRingOperations`
- `Sheaf.CategoryTheory.AlgebraicInverseImage`
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfTransport`
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`
- `Sheaf.CategoryTheory.DerivedAdjunctionHomDiagram`
- `Sheaf.CategoryTheory.DerivedAdjunctionSourceColimit`
- `Sheaf.CategoryTheory.DerivedAdjunctionTargetColimit`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd`
- `Sheaf.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors`
- `Sheaf.CategoryTheory.FiniteTypeRestrictionExact`
- `Sheaf.CategoryTheory.GeometricModuleConstruction`
- `Sheaf.CategoryTheory.GeometricModuleTransport`
- `Sheaf.CategoryTheory.GeometricRingTransport`
- `Sheaf.CategoryTheory.IndexedCoveringClass`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.CategoryTheory.ModulePullbackTensorIsoE`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.CategoryTheory.RingedToposMorphism`
- `Sheaf.CategoryTheory.RingedToposRingData`
- `Sheaf.CategoryTheory.SheafSubcategoryComparison`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.CategoryTheory.SitePullbackAbelianUnderlying`
- `Sheaf.CategoryTheory.Sites.InverseImageLocalFamilies`
- `Sheaf.CategoryTheory.Sites.LocalizedCommRingPullbackComparison`
- `Sheaf.CategoryTheory.Sites.LocalizedModulePullbackComparison`
- `Sheaf.CategoryTheory.Sites.LocalizedSetPullbackComparison`
- `Sheaf.CategoryTheory.Sites.LocalizedSheavesOverRepresentable`
- `Sheaf.CategoryTheory.Sites.SliceSheafInverseImageEquivalence`
- `Sheaf.CategoryTheory.SmallSetOfCoveringFamilies`
- `Sheaf.Paper.DerivedAdjunctionShift`
- `Sheaf.Paper.DerivedPullbackRepresentativeComputation`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Paper.LocalizeRingedSiteMorphism`
- `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`
- `Sheaf.Paper.ProEtaleLocallyConstantSheaf`
- `Sheaf.Paper.ProfiniteTestObjectFunctor`
- `Sheaf.Paper.ProjectionFormulaArrows`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.ResolvingRepresentativeWhiskering`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.RingedProjectionRestriction`
- `Sheaf.Paper.RingedSquareTensorCompatibility`
- `Sheaf.Paper.RingedTensorSquarePresentation`
- `Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackUnitExistence`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackUnitUnique`
- `Sheaf.Paper.RingedTopoiDerivedPullback`
- `Sheaf.Paper.RingedTopoiInverseImagePairing`
- `Sheaf.Paper.RingedTopoiInverseImageTensorComparison`
- `Sheaf.Paper.RingedTopoiInverseImageTensorPairingIsIso`
- `Sheaf.Paper.RingedTopoiScalarTensorComparison`
- `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`
- `Sheaf.Paper.RingedTopoiTensorComparisonData`
- `Sheaf.Paper.RingedTopoiTensorSections`
- `Sheaf.Paper.SliceSiteLocalization`
- `Sheaf.Paper.TensorPullbackRepresentativeDescent`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafifyBilinearExtExistence`
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafifyBilinearExtUniqueness`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `WeilConjectures.Algebra.Homology.BoundedAboveFlatTensorAcyclic`
- `WeilConjectures.Algebra.Homology.BoundedAboveFlatTensorAcyclicDegree`
- `WeilConjectures.Algebra.Homology.BoundedFlatReplacement`
- `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorAcyclic`
- `WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison`
- `WeilConjectures.Algebra.Homology.CyclePullbackCore`
- `WeilConjectures.Algebra.Homology.CyclePullbackLaws`
- `WeilConjectures.Algebra.Homology.CyclePullbackLifting`
- `WeilConjectures.Algebra.Homology.CyclePullbackResolution`
- `WeilConjectures.Algebra.Homology.CyclePullbackTower`
- `WeilConjectures.Algebra.Homology.CyclePullbackTowerComparison`
- `WeilConjectures.Algebra.Homology.FilteredColimitsTensor`
- `WeilConjectures.Algebra.Homology.FilteredColimitsTensorTotal`
- `WeilConjectures.Algebra.Homology.FlatAugmentationEpicification`
- `WeilConjectures.Algebra.Homology.FlatCoverFunctor`
- `WeilConjectures.Algebra.Homology.FlatTruncationSuccessor`
- `WeilConjectures.Algebra.Homology.FlatTruncationTelescopeComparison`
- `WeilConjectures.Algebra.Homology.FlatTruncationTower`
- `WeilConjectures.Algebra.Homology.KFlat`
- `WeilConjectures.Algebra.Homology.KFlatTensorConeTwoOutOfThree`
- `WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`
- `WeilConjectures.Algebra.Homology.RelativeFlatExtension`
- `WeilConjectures.Algebra.Homology.TelescopeColimit`
- `WeilConjectures.Algebra.Homology.TelescopeShiftMono`
- `WeilConjectures.Algebra.Homology.TruncationTelescope`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `WeilConjectures.AlgebraicGeometry.LocallyClosedStratification`
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra`
- `WeilConjectures.AlgebraicGeometry.SiteRestrictionExact`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Coprod`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Cover`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Descent`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.EssSurj`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.FullyFaithful`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Gluing`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Outer`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Reduction`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Section`
- `WeilConjectures.CategoryTheory.Adjunction.ProjectionMap`
- `WeilConjectures.CategoryTheory.ConcreteCategory.FinitelyGenerated`
- `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`
- `WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit`
- `WeilConjectures.CategoryTheory.DerivedCategory.Constructible`
- `WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal`
- `WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro`
- `WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantProCriterion`
- `WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantProHomColimit`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedExactOfLocalization`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory`
- `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge`
- `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift`
- `WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`
- `WeilConjectures.CategoryTheory.DerivedFunctorShift`
- `WeilConjectures.CategoryTheory.DerivedFunctorThirdValue`
- `WeilConjectures.CategoryTheory.DerivedFunctorTriangleRetractionHomColimit`
- `WeilConjectures.CategoryTheory.DerivedFunctorTriangles`
- `WeilConjectures.CategoryTheory.DerivedFunctorValueTriangle`
- `WeilConjectures.CategoryTheory.DerivedFunctorValueTriangleCompatibility`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients`
- `WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`
- `WeilConjectures.CategoryTheory.LeftDerivedExactWhenDefined`
- `WeilConjectures.CategoryTheory.LeftDerivedKanSourceTriangles`
- `WeilConjectures.CategoryTheory.LeftDerivedKanTriangleValueComparison`
- `WeilConjectures.CategoryTheory.LeftDerivedValueMorphism`
- `WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact`
- `WeilConjectures.CategoryTheory.ModuleObjects.Abelian`
- `WeilConjectures.CategoryTheory.ModuleObjects.Bimod`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`
- `WeilConjectures.CategoryTheory.ModuleObjects.Preadditive`
- `WeilConjectures.CategoryTheory.Monoidal.Dualizable`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex`
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`
- `WeilConjectures.CategoryTheory.Monoidal.Mod.Limits`
- `WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift`
- `WeilConjectures.CategoryTheory.RingObjects.Ab`
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`
- `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions`
- `WeilConjectures.CategoryTheory.SheafAbelianObjectsBijective`
- `WeilConjectures.CategoryTheory.SheafAbelianObjectsInjective`
- `WeilConjectures.CategoryTheory.SheafAbelianObjectsSurjective`
- `WeilConjectures.CategoryTheory.SheafRingObjectReconstruction`
- `WeilConjectures.CategoryTheory.SheafRingObjectsBijective`
- `WeilConjectures.CategoryTheory.SheafRingObjectsInjective`
- `WeilConjectures.CategoryTheory.SheafRingObjectsSurjective`
- `WeilConjectures.CategoryTheory.SheavesAbelianForward`
- `WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian`
- `WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore`
- `WeilConjectures.CategoryTheory.SiteExtensionByZeroExact`
- `WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf`
- `WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheafAdjoint`
- `WeilConjectures.CategoryTheory.Sites.LocallyBijectiveFiniteLimit`
- `WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact`
- `WeilConjectures.CategoryTheory.ThirdValueConstruction`
- `WeilConjectures.CategoryTheory.TriangleCommonRefinement`
- `WeilConjectures.CategoryTheory.TriangleMorphismCategory`
- `WeilConjectures.CategoryTheory.Triangulated.DenominatorTriangleCompletion`
- `WeilConjectures.CategoryTheory.TriangulatedHomColimitComparison`
- `WeilConjectures.Compactification.Defs`
- `WeilConjectures.ConstructibleSheaf.Biproduct`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.ConstructibleSheaf.GenericConstancy`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `WeilConjectures.ConstructibleSheaf.OpenClosed`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.ConstructibleSheaf.Refinement`
- `WeilConjectures.ConstructibleSheaf.UniversalHomeomorphism`
- `WeilConjectures.Mathlib.Algebra.Algebra.Hom`
- `WeilConjectures.Mathlib.Algebra.Algebra.Pi`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB`
- `WeilConjectures.Mathlib.Algebra.Category.Ring.Limits`
- `WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `WeilConjectures.Mathlib.Algebra.Homology.Embedding.Extend`
- `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`
- `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`
- `WeilConjectures.Mathlib.AlgebraicGeometry.AffineOpenAlgebra`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Fiber`
- `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Limits`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.LocalIso`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian`
- `WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.Injective.Resolution`
- `WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived`
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`
- `WeilConjectures.Mathlib.CategoryTheory.Elements`
- `WeilConjectures.Mathlib.CategoryTheory.Equivalence`
- `WeilConjectures.Mathlib.CategoryTheory.Limits.FinallySmall`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mon`
- `WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Over`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Category`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Conservative`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.Mathlib.Data.Set.Image`
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`
- `WeilConjectures.Mathlib.RingTheory.Etale.FiberDegree`
- `WeilConjectures.Mathlib.RingTheory.Etale.Field`
- `WeilConjectures.Mathlib.RingTheory.Etale.GeometricPoint`
- `WeilConjectures.Mathlib.RingTheory.Etale.PropertyC`
- `WeilConjectures.Mathlib.RingTheory.Etale.QuasiFinite`
- `WeilConjectures.Mathlib.RingTheory.Etale.ResidueField`
- `WeilConjectures.Mathlib.RingTheory.Etale.ResidueFieldBaseChange`
- `WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale`
- `WeilConjectures.Mathlib.RingTheory.Etale.Weakly`
- `WeilConjectures.Mathlib.RingTheory.Flat.DescentAlgebra`
- `WeilConjectures.Mathlib.RingTheory.Flat.LocallyFree`
- `WeilConjectures.Mathlib.RingTheory.Henselian`
- `WeilConjectures.Mathlib.RingTheory.Idempotents`
- `WeilConjectures.Mathlib.RingTheory.Localization.Ideal`
- `WeilConjectures.Mathlib.RingTheory.RingHom.PurelyInseparable`
- `WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology`
- `WeilConjectures.Mathlib.RingTheory.Unramified.LocalStructure`
- `WeilConjectures.Mathlib.Topology.Category.TopCat.Limits.Pullbacks`
- `WeilConjectures.Mathlib.Topology.Connected.Clopen`
- `WeilConjectures.Mathlib.Topology.Connected.TotallyDisconnected`
- `WeilConjectures.Mathlib.Topology.Constructible`
- `WeilConjectures.Mathlib.Topology.Inseparable`
- `WeilConjectures.Mathlib.Topology.KrullDimension`
- `WeilConjectures.Mathlib.Topology.Maps.Basic`
- `WeilConjectures.Mathlib.Topology.NoetherianSpace`
- `WeilConjectures.Mathlib.Topology.QuasiSeparated`
- `WeilConjectures.Mathlib.Topology.Separation.Hausdorff`
- `WeilConjectures.Mathlib.Topology.Sets.Opens`
- `WeilConjectures.Mathlib.Topology.Sober`
- `WeilConjectures.Mathlib.Topology.Spectral.Basic`
- `WeilConjectures.Mathlib.Topology.Spectral.Prespectral`
- `WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.Defs`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Complement`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`
- `WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.OpenClosed.ClosedImmersion`
- `WeilConjectures.SixFunctors.OpenClosed.Complex`
- `WeilConjectures.SixFunctors.OpenClosed.Stalk`
- `WeilConjectures.SixFunctors.OpenClosed.Vanishing`
- `WeilConjectures.SixFunctors.ProEtale.Comparison.Defs`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal`
- `WeilConjectures.SixFunctors.UpperLowerStar.Defs`
- `WeilConjectures.Topology.SpectralSpace.ConnectedComponent`
- `WeilConjectures.Topology.SpectralSpace.Profinite`
- `WeilConjectures.Topology.SpectralSpace.Pullback`
- `WeilConjectures.Topology.Stratification`
- `WeilConjectures.Topology.StratificationDense`

</details>

## Where the brief, the DAG or earlier work was wrong

The represented-site replacement in Step 1 is unnecessary for the actual Lean
statement: U,V and their terminal pullback already are objects of the supplied site.
The proposed cohomology-long-exact argument in Step 7 can be replaced by the shorter
abstract triangulated graph/coyoneda argument.

The recorded localized-system exactness and localized K-injective lemmas require the
ring to live in max(site-object,site-Hom,ring) itself; the item instead takes
`R : Sheaf J CommRingCat.{r}` with independent r. Their signatures cannot simply be
instantiated at the item's universes. The new exact extension and restriction
K-injective lemmas preserve the item's universes and prove the needed statements.
The existing `isGrothendieckAbelianOfUniverses` suffices for K-injective resolutions
in the derived counit proof. The existing `SliceModuleSheafification` comparison
also fixes site and coefficient universes together. Its naturality argument is now
generalized and proved in `SiteModuleSliceSheafification`, which the remaining
lower-shriek source lemma imports.

The source tags are for ringed spaces or the specified site context. We use their
explicit arguments for subterminal slice sites; we do not apply a ringed-space
statement to an arbitrary ringed site. No target statement or mathematical definition
has been weakened. The unit's charts-and-gluing route and both clauses are retained.

## New nodes

`def-sp-ringed-topos-binary-descent-models`: Termwise slice restriction models and normalized adjunction map. Lean attachment: `Sheaf.CategoryTheory.RingedToposBinaryDescentDefs`, `CategoryTheory.moduleOverComplex`.

`lem-sp-module-extension-zero-independent-ring`: Exact module extension by zero with an independent ring universe. Lean attachment: `Sheaf.CategoryTheory.SiteModuleExtensionByZeroExact`, `SheafOfModules.siteModuleExtensionByZero_exact`.

`lem-sp-module-slice-sheafification-independent-ring`: Module sheafification commutes with restriction at independent universes. Lean attachment: `Sheaf.CategoryTheory.SiteModuleSliceSheafification`, `SheafOfModules.sliceSheafificationComparisonIndependent_isIso`.

`lem-sp-ringed-topos-cross-direct-image-restriction`: Cross-restriction of the derived direct-image overlap maps. Lean attachment: `Sheaf.CategoryTheory.RingedToposCrossDirectImageRestriction`, `CategoryTheory.ringedTopos_crossDirectImage_restriction`.

`lem-sp-ringed-topos-direct-image-restriction`: Fully faithful derived open direct images and cross-restriction. Lean attachment: `Sheaf.CategoryTheory.RingedToposDirectImageRestriction`, `CategoryTheory.ringedTopos_directImage_restriction`.

`lem-sp-ringed-topos-fibre-restriction`: Isomorphisms from the direct-image fibre on both opens. Lean attachment: `Sheaf.CategoryTheory.RingedToposFibreRestriction`, `CategoryTheory.ringedTopos_fibre_restriction`.

`lem-sp-ringed-topos-lower-shriek-triangle`: Natural lower-shriek triangle for a binary subterminal cover. Lean attachment: `Sheaf.CategoryTheory.RingedToposBinaryDescentTriangle`, `CategoryTheory.ringedTopos_binary_descent_triangle`.

`lem-sp-ringed-topos-ordinary-cross-restriction`: Ordinary direct-image cross-restriction for subterminals. Lean attachment: `Sheaf.CategoryTheory.RingedToposOrdinaryCrossRestriction`, `CategoryTheory.ringedTopos_ordinaryCross_restriction`.

`lem-sp-site-relocalization-kinjective-independent-ring`: Relocalization preserves K-injectives at independent ring universes. Lean attachment: `Sheaf.CategoryTheory.SiteRelocalizationKInjective`, `SheafOfModules.overMap_preservesKInjectiveComplexes_ofUniverses`.

`lem-sp-site-restriction-kinjective-independent-ring`: Slice restriction preserves K-injectives at independent ring universes. Lean attachment: `Sheaf.CategoryTheory.SiteRestrictionKInjective`, `SheafOfModules.overFunctor_preservesKInjectiveComplexes_ofUniverses`.

Change record: `coord/changes/ringed-topos-binary-descent-models.md`.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
