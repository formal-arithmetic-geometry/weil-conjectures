## What changed

Replaced the sole `sorry` in
`Sheaf.Algebra.Homology.BaseDerivedExtensionResolution`, declaration
`ModuleCat.exists_baseDerivedExtension_resolution`, by a compiling proof.
The declaration's signature, universes, visibility and public imports are unchanged.

The proof uses the existing larger-universe filtered free resolution, identifies
its source as K-projective using the new filtered-free criterion, and takes the
homotopy images of K-projective complexes as the resolving class. Mathlib's
`CochainComplex.IsKProjective.quasiIso_iff` and
`HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences` turn every
quasi-isomorphism between these models into a homotopy-category isomorphism.
Ordinary scalar extension therefore inverts them regardless of flatness.
`Functor.leftDerived_from_resolvingClass` supplies the universal counit and
triangulated structure; its computation clause supplies the last resolution clause.

Added proof imports of `Mathlib.Algebra.Homology.DerivedCategory.KProjective`,
`Sheaf.Algebra.Homology.LargeFilteredFreeResolution`, and
`Sheaf.Algebra.Homology.FilteredFreeKProjective`. Retained the resolving-class
proof import. Updated the item's node proof, proof dependencies and proof origin.
The new module has one public theorem with its source and full argument in its docstring.
No existing interfaces or definitions changed, so no change record or forced adaptation is needed.

Both delivered modules compile through `lcompile.py --all`, without warnings.
The Lean proof was checked at unequal universes by the original polymorphic signature;
no carrier or ring universe was specialized. The new lemma's zero-ring, zero-complex,
empty-free-basis and unbounded cases were checked against its filtration argument.

## Proved and sorry left

Closed: `ModuleCat.exists_baseDerivedExtension_resolution`
(node `lem-pc-base-derived-extension-resolution`). There is no `sorry` in the item's module.

Added and left: `CochainComplex.isKProjective_of_filtered_free`
(node `lem-pc-filtered-free-kprojective`), in the new module
`Sheaf.Algebra.Homology.FilteredFreeKProjective`. Its proof is exactly `:= by sorry`.
This is a decomposition: one upper hole closed, one strictly smaller hole added,
net zero before import-closure pruning. The new statement concerns only the
K-projectivity of an already supplied filtered complex; it asserts neither
existence of resolutions nor a derived functor, counit, universal property,
triangulated structure or counit invertibility. The combining proof is real Lean.

Existing imported lemmas are used as stated; their downstream holes are not claimed
as closed by this delivery. In particular the larger-universe resolution construction
and the resolving-class construction retain their own source-backed proof dependencies.

## No longer needed

Removed proof imports:

- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`
  (`lem-pc-derived-tensor-second-factor-functor`).
- `Sheaf.Algebra.Homology.KFlatResolution` (`lem-pc-kflat-resolution`).

The proof no longer needs mixed total tensor, fixed-second-factor derived tensor,
K-flat tensor quasi-isomorphism comparison, ringed-site K-flat resolutions, or
transport of the derived universal pair along lifted-ring equivalences.
The larger-universe filtered free resolution already performs the scalar transport
needed for the resolution objects.

The complete difference between the original item's import closure and the delivered
item's import closure (project roots only; Mathlib excluded) is the following 222 modules.
These leave this item's closure, not necessarily the entire targets' closure:
other target paths may still need them. Node IDs are given whenever the DAG records
that module. No unit statement or realized unit proof step was bypassed; the item's
unit `sk-thm-picard-duality` has no realized nodes attached to this resolution route.

| Module no longer imported transitively by this item | Recorded node(s) |
|---|---|
| `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension` | `lem-pc-sites-module-sheafification-bilinear-extension` |
| `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionExistence` | `lem-pc-sites-module-sheafification-bilinear-extension-existence` |
| `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtensionUniqueness` | `lem-pc-sites-module-sheafification-bilinear-extension-uniqueness` |
| `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat` | `lem-pc-sites-modules-sheafification-flat` |
| `Sheaf.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor` | `lem-pc-sites-module-sheafification-tensor` |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat` | `def-pc-flat-sheaf-modules` |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct` | `lem-pc-sites-modules-coproduct-flat` |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal` | `lem-pc-sites-sheaf-tensor-bilinear-universal` |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` | `lem-pc-sheaf-modules-tensor-closed` |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct` | `def-pur-sheaf-tensor-product` |
| `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat` | `lem-pc-bounded-above-flat-kflat-site` |
| `Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclic` | `lem-pc-bounded-above-flat-tensor-acyclic` |
| `Sheaf.Algebra.Homology.BoundedAboveFlatTensorAcyclicDegree` | `lem-pc-bounded-above-flat-tensor-acyclic-degree` |
| `Sheaf.Algebra.Homology.BoundedFlatReplacement` | `lem-pc-kflat-bounded-flat-replacement` |
| `Sheaf.Algebra.Homology.CyclePullbackCore` | `lem-pc-functorial-cycle-pullback-core-stage3` |
| `Sheaf.Algebra.Homology.CyclePullbackLifting` | `lem-pc-functorial-cycle-pullback-lifting-stage3` |
| `Sheaf.Algebra.Homology.CyclePullbackResolution` | `lem-pc-functorial-cycle-pullback-construction` |
| `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor` | `lem-pc-derived-tensor-second-factor-functor` |
| `Sheaf.Algebra.Homology.DoubleComplexSingleRowTotalIso` | `lem-sp-double-complex-single-row-total-iso` |
| `Sheaf.Algebra.Homology.DoubleComplexVerticalSpectralObject` | `lem-sp-double-complex-vertical-spectral-object` |
| `Sheaf.Algebra.Homology.DoubleComplexVerticalTowerComparison` | `lem-sp-double-complex-vertical-tower-comparison` |
| `Sheaf.Algebra.Homology.DoubleComplexVerticalTowerComparisonFinite` | `lem-sp-double-complex-vertical-tower-comparison-finite` |
| `Sheaf.Algebra.Homology.DoubleComplexVerticalTowerComparisonTop` | `lem-sp-double-complex-vertical-tower-comparison-top` |
| `Sheaf.Algebra.Homology.DoubleComplexVerticalTowerMaps` | `lem-sp-double-complex-vertical-tower-maps` |
| `Sheaf.Algebra.Homology.DoubleComplexVerticalWindow` | `def-sp-double-complex-vertical-window` |
| `Sheaf.Algebra.Homology.DoubleComplexVerticalWindowHomology` | `lem-sp-double-complex-vertical-window-homology` |
| `Sheaf.Algebra.Homology.FilteredColimitsTensor` | `lem-pc-module-filtered-colimits-tensor` |
| `Sheaf.Algebra.Homology.FilteredColimitsTensorTotal` | `lem-pc-module-filtered-colimits-tensor-preserves` |
| `Sheaf.Algebra.Homology.FlatAugmentationEpicification` | `lem-pc-flat-augmentation-epicification` |
| `Sheaf.Algebra.Homology.FlatCoverFunctor` | `lem-pc-sites-modules-functorial-flat-cover` |
| `Sheaf.Algebra.Homology.FlatTruncationSuccessor` | `lem-pc-flat-truncation-successor` |
| `Sheaf.Algebra.Homology.FlatTruncationTelescopeComparison` | `lem-pc-flat-truncation-telescope-comparison` |
| `Sheaf.Algebra.Homology.FlatTruncationTower` | `lem-pc-flat-truncation-tower` |
| `Sheaf.Algebra.Homology.KFlat` | `def-pc-kflat-complex` |
| `Sheaf.Algebra.Homology.KFlatClosure` | `lem-pc-kflat-cone-direct-sum` |
| `Sheaf.Algebra.Homology.KFlatResolution` | `lem-pc-kflat-resolution` |
| `Sheaf.Algebra.Homology.KFlatTelescopeClosure` | `lem-pc-kflat-closure` |
| `Sheaf.Algebra.Homology.KFlatTensorConeTwoOutOfThree` | `lem-pc-kflat-tensor-cone-two-out-of-three` |
| `Sheaf.Algebra.Homology.MixedTensorKFlatQuasiIso` | `lem-pc-mixed-tensor-kflat-quasi-iso` |
| `Sheaf.Algebra.Homology.MixedTensorPointwiseLeftDerived` | `lem-pc-mixed-tensor-pointwise-left-derived` |
| `Sheaf.Algebra.Homology.MixedTensorRestrictionComparison` | `lem-pc-mixed-tensor-restriction-comparison` |
| `Sheaf.Algebra.Homology.MixedTotalTensor` | `def-pc-mixed-total-tensor` |
| `Sheaf.Algebra.Homology.RelativeFlatExtension` | `lem-pc-relative-flat-extension` |
| `Sheaf.Algebra.Homology.TelescopeColimit` | `lem-pc-complex-hocolim-colimit` |
| `Sheaf.Algebra.Homology.TelescopeShiftMono` | `lem-pc-telescope-shift-mono` |
| `Sheaf.Algebra.Homology.TruncationTelescope` | `lem-pc-kflat-hocolim-truncations` |
| `Sheaf.Algebra.Homology.VerticalWindowComponentIso` | `lem-sp-vertical-window-component-iso` |
| `Sheaf.Algebra.Homology.VerticalWindowComponentNaturality` | `lem-sp-vertical-window-component-naturality` |
| `Sheaf.Algebra.Homology.VerticalWindowDegreeIso` | `lem-sp-vertical-window-degree-iso` |
| `Sheaf.Algebra.Homology.VerticalWindowSingleIso` | `lem-sp-vertical-window-single-iso` |
| `Sheaf.CategoryTheory.ExtensionByZeroPresheaf` | `def-weil-extension-by-zero-presheaf` |
| `Sheaf.CategoryTheory.RingedSiteGrothendieckAbelian` | `lem-pur-ringed-site-grothendieck-abelian` |
| `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions` | `prop-pur-kinjective-resolutions-exist` |
| `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom` | none recorded |
| `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom` | `def-pur-sheaf-hom` |
| `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal` | `lem-weil-pbc-module-tensor-symmetric-monoidal` |
| `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed` | none recorded |
| `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree` | none recorded |
| `WeilConjectures.Algebra.Homology.HomotopyCategory.DerivabilityStructure` | none recorded |
| `WeilConjectures.CategoryTheory.Abelian.Flat.Basic` | `lem-weil-pbc-flat-coproduct` |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.AcyclicSwallowing` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.CardinalGenerated` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.CardinalGeneratedCover` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Coefficients` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.GeneratingMonoQuasiIsos` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution` | `lem-weil-pbc-kinjective-functorial-existence` |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective` | `lem-pur-kinjective-degreewise-existence` |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution` | `lem-weil-pbc-sheaf-flat-separator` |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeCardinal` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeEnlargement` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeGeneratingSet` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.SerpeSmallObject` | none recorded |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf` | `lem-weil-pbc-sheaf-tensor-closed` |
| `WeilConjectures.CategoryTheory.GrothendieckAbelian.Subcomplex` | none recorded |
| `WeilConjectures.CategoryTheory.Sites.TransfinitePlus` | none recorded |
| `WeilConjectures.CategoryTheory.Sites.TransfinitePlusSheaf` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns` | `lem-pc-bounded-above-double-complex-total-comparison` |
| `WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Bifunctor` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorColimits` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorCommShift` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone` | `lem-pc-tensor-mapping-cone-iso` |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorShift` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.BifunctorTriangulated` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.CochainComplexMinus` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Double` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.DoubleHomology` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplexTrunc` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ComplementaryTrunc` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Embedding.HomEquiv` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidFiltration` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncGE` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Embedding.TruncLE` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.HomologicalBicomplex` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexLimits` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Acyclic` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.DegreewiseSplit` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Devissage` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.KInjective` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.MonoidalTriangulated` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.PreservesQuasiIso` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Pretriangulated` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.ShiftSequence` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.Basic` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplex` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Monoidal` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.ObjectProperty` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.Single` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.TotalComplex` | none recorded |
| `WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.CurryingThree` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerived` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedBifunctorComp` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedFour` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedThree` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedTrifunctorComp` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Derived.LeftDerivedTwo` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Functor.Quadrifunctor` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.GradedObject.Bifunctor` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.GradedObject.Colimits` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.GuitartExact.Basic` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Idempotents.Basic` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Limits.Constructions.EventuallyConstant` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Limits.ExactFunctor` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.Composition` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Derives` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesFour` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesThree` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.DerivesTwo` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Monoidal` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.DerivabilityStructure.Product` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Localization.LocalizerMorphism` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Derived` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat` | `def-pc-module-kflat-complex` |
| `WeilConjectures.FromJoel.CategoryTheory.Monoidal.Pentagon` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.FiniteProducts` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.ObjectProperty.Retract` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.QuotientThree` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.QuotientTwo` | none recorded |
| `WeilConjectures.FromJoel.CategoryTheory.Triangulated.HomologicalFunctor` | none recorded |
| `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FilteredColimits` | none recorded |
| `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` | none recorded |
| `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` | none recorded |
| `WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns` | none recorded |
| `WeilConjectures.Mathlib.Algebra.Homology.Double` | none recorded |
| `WeilConjectures.Mathlib.Algebra.Homology.ExactSequence` | none recorded |
| `WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian` | none recorded |
| `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic` | `lem-pur-quasi-iso-cone-acyclic` |
| `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.KInjective` | none recorded |
| `WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic` | none recorded |
| `WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence` | `lem-sp-first-quadrant-spectral-object-abutment` |
| `WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic` | none recorded |
| `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex` | `thm-sp-double-complex-spectral-sequences` |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.CommSq` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Limits` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Comma.CardinalArrow` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.EssentialImage` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Adjunction` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Generator.Abelian` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Generator.StrongGenerator` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.FunctorCategory.Basic` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.PiProd` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Localization.Bousfield` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Category` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.FunctorCategory` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Linear` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Limits` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Presentable.Limits` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.CompatiblePlus` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Equivalence` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Grothendieck` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.LeftExact` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Localization` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.Plus` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafHom` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.SmallObject.TransfiniteIteration` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Subobject.HasCardinalLT` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Subobject.Lattice` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits` | none recorded |
| `WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject` | none recorded |
| `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic` | none recorded |
| `WeilConjectures.Mathlib.SetTheory.Cardinal.HasCardinalLT` | none recorded |
| `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex` | none recorded |

## Where the brief, the DAG or earlier work was wrong

The original node and docstring propose K-flat tensor specialization followed by
transport of a universal derived pair when ring universes differ. This is a valid
plan, but it is unnecessarily large for the stated result: the result only asks for
some resolutions on which the counit is invertible, with no requirement that all
K-flat complexes compute it. K-projective models suffice, and their comparison maps
are already isomorphisms in the homotopy category. The original docstring is retained
as the existing documented plan; the updated DAG and this report describe the actual route.

The telescope proof of the new criterion must take place in the homotopy category,
using degreewise splitting. A derived-category telescope triangle alone would not
prove K-projectivity, since every acyclic target is already zero after localization.
No derived-only telescope statement is substituted for the required homotopy statement.
For `a = identity - successor`, its degreewise left inverse on summand j uses the
NEGATIVES of the composite retractions to earlier stages, which ensures the sign
of the identity component is positive. This sign is explicit in the new node.

The smaller-universe `ModuleCat.hasFunctorialFlatResolution` and monoidal instance
are not available as-is for the module universe in this item's general signature.
The already stated `exists_large_filtered_free_resolution` resolves this without
changing any target or ring assumptions. LeanSearch returned an internal server
error and is recorded as unavailable; LeanFinder, Loogle, local library/DAG grep,
and blueprint searches were also run.

## New nodes

`lem-pc-filtered-free-kprojective`, in
`dag/nodes/sec-picard-framework/lem-pc-filtered-free-kprojective.json`, is realized by
`CochainComplex.isKProjective_of_filtered_free` in
`lean/Sheaf/Algebra/Homology/FilteredFreeKProjective.lean`.
It is Stacks Tag 09KM (`dga.tex`, `lemma-property-P-K-projective`) specialized to
ordinary modules and to the exact filtration interface of the existing larger-universe
resolution. Its proof first establishes orthogonality on the shifted free quotients,
then finite stages by degreewise split triangles, and finally the entire complex by
the degreewise split telescope of Stacks Tag 09KL. The needed resolution-existence
node already exists (`lem-pc-large-filtered-free-resolution`) and was not duplicated.
Blueprint searches for `K-projective resolution`, `filtered free` and `09KM` found
no matching blueprint nodes. The DAG search found the existing free-resolution
construction but no K-projectivity criterion for its unbounded filtered output.
No change records.

## Second reading by W2

1. **Interfaces — pass.** Compared both delivered modules against the repository.
   The existing module differs only in proof imports and the theorem body. Its
   declaration signature is byte-for-byte identical, including the unequal ring
   universes and additive-extension assumption; the public imports, variables,
   visibility and definitions are unchanged. The criterion module is new.
   No change records or forced adaptations are needed.
2. **Proof and axioms — pass with the declared lower hole.** Compiled both modules
   locally in import order, without warnings. Scratch copies with `#print axioms`
   show only `propext`, `Classical.choice`, `Quot.sound` and `sorryAx` for each
   delivered theorem. The only delivered `sorry` is the named criterion listed
   above. There are no new definitions, arbitrary chosen data, or forbidden
   declarations. The resolving-class construction already imported upstream
   supplies the derived functor; no arbitrary witness is introduced as a definition.
3. **Split statement — pass.** Checked the filtration interface against the supplied
   large filtered-free resolution and the definition of `IsKProjective`. Verified
   [Stacks 09KM](https://stacks.math.columbia.edu/tag/09KM) and its telescope step
   [Stacks 09KL](https://stacks.math.columbia.edu/tag/09KL). The negative composite
   retractions in the node give the correct left inverse for identity minus successor.
   The zero ring, zero complex and empty bases satisfy the argument; no upper bound
   on degrees is used. The lemma is strictly a part of the argument and does not
   restate the item. Independent LeanFinder search for sequential split colimits,
   Loogle search for `CochainComplex.IsKProjective`, and local Mathlib/upstream/Sheaf
   searches for semi-free, semi-projective and K-projective results found no duplicate.
   Mathlib's projective criterion requires bounded-above support and cannot close
   this unbounded criterion in a few minutes. Its source, complete docstring proof
   and node are present.
4. **Route and pruning — pass after cleanup.** Read the resolution, K-projective
   quasi-isomorphism criterion and resolving-class construction. The latter two
   combine by an actual Lean proof, using homotopy equivalences to invert model
   comparisons without flatness of the scalar extension. Every project proof import
   is used. Both old unused proof dependencies are listed under No longer needed.
   Recomputed the project import closures against the current repository: 222
   modules leave this item's closure. The report previously omitted
   `WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`;
   added it and corrected the count. The unit's `realized` statement and step lists
   are empty, so no realized unit route is bypassed.
5. **DAG — pass.** The item's only changed node fields are `proof`, `proof_deps`
   and `proof_origin`. Its proof dependencies are exactly the three imported project
   declarations used. The new node's Lean statement matches its declaration exactly;
   its source, proof, searches, creation metadata, blueprint ancestry, chapter, unit
   and Lean attachment are present.

Second-reading changes: removed two redundant public Mathlib imports from the new
criterion module (`HomologicalComplexAbelian` and `Single`), already publicly reached
through `HomotopyCategory.KProjective`; both modules still compile. Corrected the
pruned-module inventory as above. No mathematical statements or proof bodies changed.
The delivery remains one upper hole closed and one lower hole added, a decomposition
with net zero holes before pruning.
