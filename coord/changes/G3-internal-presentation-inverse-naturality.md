# CategoryTheory.InternalActionSite.Presentation

## Reason

The inverse section equivalences lacked naturality in module morphisms, although the
node specifies a sectionwise inverse equivalence. The assigned theorem explicitly
uses these section maps to pin a natural restriction isomorphism. The omitted law
cannot follow from the old fields: on the one-object trivial-group site over ℤ,
replace inverseSections by its negative on a chosen module (for example ℤ) and
leave it unchanged on a different module (for example ℤ²). Both are linear
isomorphisms and commute with the identity restrictions and trivial actions. All
old fields still hold, but the inclusion ℤ → ℤ² shows that the new family is not
natural. The claimed restriction comparison for θ = id would force naturality,
since the core section maps, unitor and comparison are all natural. This was a
missing part of the formal presentation contract, not an extra mathematical
hypothesis on the site, group, coefficient ring or morphism.

Add inverse_morphisms and prove it in presentation. The proof transports the
existing inverse-map formula himap through the inverse-object equality hio and
the inverse sheaf-map equality hsmap. Both endpoint transports use the same
cast_apply lemma as the existing restriction and action proofs. The existence
theorem keeps its signature, introduces no sorry, and compiles in 18 seconds.
No existing field, attribute, instance or import is removed or changed. Existing
constructors only occur in this module; all consumers project or assume a
Presentation. This is an unclaimed module, not an adaptation of another group's
claimed theorem. All target statements and all seven module/tensor specification
bodies of the assigned item are unchanged. This repair makes their intended
sectionwise presentation interpretation explicit.

## Old

```lean
structure Presentation [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (S : Sheaf J.toGrothendieck CommRingCat.{u}) where
  /-- The equivalence before imposing the sheaf condition. -/
  presheafEquivalence : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj ≌
    PresheafOfModules.{u} (twistedRing K J hJ S).obj
  /-- Addition of component maps is preserved. -/
  presheaf_additive : presheafEquivalence.functor.Additive
  /-- The equivalence keeps the section modules. -/
  sections (M : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj) (X : C) :
    (presheafEquivalence.functor.obj M).obj (op (Object.mk (K := K) X)) ≃ₗ[
      (baseRing J.toGrothendieck S).obj.obj (op X)] M.val.obj (op X)
  /-- Twisted restriction is the action after ordinary restriction. -/
  restriction (M : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj)
      {X Y : C} (f : X ⟶ Y) (a : K.obj (op X))
      (m : (presheafEquivalence.functor.obj M).obj (op (Object.mk (K := K) Y))) :
    sections M X ((presheafEquivalence.functor.obj M).map (opArrow K f a) m) =
      M.action.act (op X) a (M.val.map f.op (sections M Y m))
  /-- Morphisms have the same sectionwise linear maps. -/
  morphisms {M N : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj} (f : M ⟶ N)
      (X : C) (m : (presheafEquivalence.functor.obj M).obj (op (Object.mk (K := K) X))) :
    sections N X ((presheafEquivalence.functor.map f).app _ m) =
      f.val.app (op X) (sections M X m)
  /-- The additive equivalence on sheaves. -/
  sheafEquivalence : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S) ≌
    ringedSiteModules (twistedRing K J hJ S)
  /-- The sheaf equivalence is additive. -/
  sheaf_additive : sheafEquivalence.functor.Additive
  /-- It is the restriction of the presheaf equivalence. -/
  underlying : inclusion J.toGrothendieck (baseRing J.toGrothendieck S) ⋙
      presheafEquivalence.functor ≅
    sheafEquivalence.functor ⋙ SheafOfModules.forget (twistedRing K J hJ S)
  /-- Inverse section modules, displaying restriction to normalized arrows. -/
  inverseSections (N : ringedSiteModules (twistedRing K J hJ S)) (X : C) :
    (sheafEquivalence.inverse.obj N).obj.val.obj (op X) ≃ₗ[
      (baseRing J.toGrothendieck S).obj.obj (op X)] N.val.obj (op (Object.mk (K := K) X))
  /-- The inverse restricts along (f,1). -/
  inverse_restriction (N : ringedSiteModules (twistedRing K J hJ S))
      {X Y : C} (f : X ⟶ Y)
      (m : (sheafEquivalence.inverse.obj N).obj.val.obj (op Y)) :
    inverseSections N X ((sheafEquivalence.inverse.obj N).obj.val.map f.op m) =
      N.val.map (opArrow K f 1) (inverseSections N Y m)
  /-- The inverse recovers the action from (1,a). -/
  inverse_action (N : ringedSiteModules (twistedRing K J hJ S)) (X : C)
      (a : K.obj (op X)) (m : (sheafEquivalence.inverse.obj N).obj.val.obj (op X)) :
    inverseSections N X ((sheafEquivalence.inverse.obj N).obj.action.act (op X) a m) =
      N.val.map (opArrow K (𝟙 X) a) (inverseSections N X m)
  /-- Module sheafification equipped with the induced group action. -/
  equivariantSheafification : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj ⥤
    EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S)
  /-- Its universal property is among equivariant maps. -/
  adjunction : equivariantSheafification ⊣ inclusion J.toGrothendieck (baseRing J.toGrothendieck S)
  /-- After forgetting the action it is ordinary module sheafification on C. -/
  baseComparison : equivariantSheafification ⋙
      forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck S) ≅
    forgetPresheaf ⋙ PresheafOfModules.sheafification (𝟙 (baseRing J.toGrothendieck S).obj)
  /-- The comparison keeps the ordinary sheafification unit. -/
  base_unit (M : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj) :
    (PresheafOfModules.toPresheaf (baseRing J.toGrothendieck S).obj).map
        (forgetPresheaf.map (adjunction.unit.app M)) ≫
      ((SheafOfModules.toSheaf (baseRing J.toGrothendieck S)).map (baseComparison.hom.app M)).hom =
        toSheafify J.toGrothendieck M.val.presheaf
  /-- Sheafification on the action site agrees with equivariant sheafification. -/
  siteComparison : presheafEquivalence.functor ⋙
      PresheafOfModules.sheafification (𝟙 (twistedRing K J hJ S).obj) ≅
    equivariantSheafification ⋙ sheafEquivalence.functor
  /-- This comparison too is the canonical one commuting with the unit. -/
  site_unit (M : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj) :
    (PresheafOfModules.toPresheaf (twistedRing K J hJ S).obj).map
        (presheafEquivalence.functor.map (adjunction.unit.app M) ≫
          underlying.hom.app (equivariantSheafification.obj M)) =
      toSheafify (topology K J) (presheafEquivalence.functor.obj M).presheaf ≫
        ((SheafOfModules.toSheaf (twistedRing K J hJ S)).map
          (siteComparison.hom.app M)).hom
  /-- Forgetting the group creates kernels. -/
  createsKernels
      (M N : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S))
      (f : M ⟶ N) :
    Nonempty (CreatesLimit (parallelPair f 0)
      (forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck S)))
  /-- Forgetting the group creates cokernels. -/
  createsCokernels
      (M N : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S))
      (f : M ⟶ N) :
    Nonempty (CreatesColimit (parallelPair f 0)
      (forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck S)))
  /-- Zero is detected after restricting to the base site. -/
  zero_iff (N : ringedSiteModules (twistedRing K J hJ S)) :
    IsZero N ↔ IsZero ((forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck S)).obj
      (sheafEquivalence.inverse.obj N))

```

## New

```lean
structure Presentation [HasFiniteLimits C] (J : Precoverage C)
    (hJ : J.IsSiteForCoverings)
    (S : Sheaf J.toGrothendieck CommRingCat.{u}) where
  /-- The equivalence before imposing the sheaf condition. -/
  presheafEquivalence : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj ≌
    PresheafOfModules.{u} (twistedRing K J hJ S).obj
  /-- Addition of component maps is preserved. -/
  presheaf_additive : presheafEquivalence.functor.Additive
  /-- The equivalence keeps the section modules. -/
  sections (M : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj) (X : C) :
    (presheafEquivalence.functor.obj M).obj (op (Object.mk (K := K) X)) ≃ₗ[
      (baseRing J.toGrothendieck S).obj.obj (op X)] M.val.obj (op X)
  /-- Twisted restriction is the action after ordinary restriction. -/
  restriction (M : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj)
      {X Y : C} (f : X ⟶ Y) (a : K.obj (op X))
      (m : (presheafEquivalence.functor.obj M).obj (op (Object.mk (K := K) Y))) :
    sections M X ((presheafEquivalence.functor.obj M).map (opArrow K f a) m) =
      M.action.act (op X) a (M.val.map f.op (sections M Y m))
  /-- Morphisms have the same sectionwise linear maps. -/
  morphisms {M N : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj} (f : M ⟶ N)
      (X : C) (m : (presheafEquivalence.functor.obj M).obj (op (Object.mk (K := K) X))) :
    sections N X ((presheafEquivalence.functor.map f).app _ m) =
      f.val.app (op X) (sections M X m)
  /-- The additive equivalence on sheaves. -/
  sheafEquivalence : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S) ≌
    ringedSiteModules (twistedRing K J hJ S)
  /-- The sheaf equivalence is additive. -/
  sheaf_additive : sheafEquivalence.functor.Additive
  /-- It is the restriction of the presheaf equivalence. -/
  underlying : inclusion J.toGrothendieck (baseRing J.toGrothendieck S) ⋙
      presheafEquivalence.functor ≅
    sheafEquivalence.functor ⋙ SheafOfModules.forget (twistedRing K J hJ S)
  /-- Inverse section modules, displaying restriction to normalized arrows. -/
  inverseSections (N : ringedSiteModules (twistedRing K J hJ S)) (X : C) :
    (sheafEquivalence.inverse.obj N).obj.val.obj (op X) ≃ₗ[
      (baseRing J.toGrothendieck S).obj.obj (op X)] N.val.obj (op (Object.mk (K := K) X))
  /-- The inverse restricts along (f,1). -/
  inverse_restriction (N : ringedSiteModules (twistedRing K J hJ S))
      {X Y : C} (f : X ⟶ Y)
      (m : (sheafEquivalence.inverse.obj N).obj.val.obj (op Y)) :
    inverseSections N X ((sheafEquivalence.inverse.obj N).obj.val.map f.op m) =
      N.val.map (opArrow K f 1) (inverseSections N Y m)
  /-- The inverse recovers the action from (1,a). -/
  inverse_action (N : ringedSiteModules (twistedRing K J hJ S)) (X : C)
      (a : K.obj (op X)) (m : (sheafEquivalence.inverse.obj N).obj.val.obj (op X)) :
    inverseSections N X ((sheafEquivalence.inverse.obj N).obj.action.act (op X) a m) =
      N.val.map (opArrow K (𝟙 X) a) (inverseSections N X m)
  /-- Inverse section identifications are natural in module morphisms. -/
  inverse_morphisms {M N : ringedSiteModules (twistedRing K J hJ S)} (f : M ⟶ N)
      (X : C) (m : (sheafEquivalence.inverse.obj M).obj.val.obj (op X)) :
    inverseSections N X ((sheafEquivalence.inverse.map f).hom.val.app (op X) m) =
      f.val.app (op (Object.mk (K := K) X)) (inverseSections M X m)
  /-- Module sheafification equipped with the induced group action. -/
  equivariantSheafification : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj ⥤
    EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S)
  /-- Its universal property is among equivariant maps. -/
  adjunction : equivariantSheafification ⊣ inclusion J.toGrothendieck (baseRing J.toGrothendieck S)
  /-- After forgetting the action it is ordinary module sheafification on C. -/
  baseComparison : equivariantSheafification ⋙
      forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck S) ≅
    forgetPresheaf ⋙ PresheafOfModules.sheafification (𝟙 (baseRing J.toGrothendieck S).obj)
  /-- The comparison keeps the ordinary sheafification unit. -/
  base_unit (M : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj) :
    (PresheafOfModules.toPresheaf (baseRing J.toGrothendieck S).obj).map
        (forgetPresheaf.map (adjunction.unit.app M)) ≫
      ((SheafOfModules.toSheaf (baseRing J.toGrothendieck S)).map (baseComparison.hom.app M)).hom =
        toSheafify J.toGrothendieck M.val.presheaf
  /-- Sheafification on the action site agrees with equivariant sheafification. -/
  siteComparison : presheafEquivalence.functor ⋙
      PresheafOfModules.sheafification (𝟙 (twistedRing K J hJ S).obj) ≅
    equivariantSheafification ⋙ sheafEquivalence.functor
  /-- This comparison too is the canonical one commuting with the unit. -/
  site_unit (M : EquivariantPresheaf K (baseRing J.toGrothendieck S).obj) :
    (PresheafOfModules.toPresheaf (twistedRing K J hJ S).obj).map
        (presheafEquivalence.functor.map (adjunction.unit.app M) ≫
          underlying.hom.app (equivariantSheafification.obj M)) =
      toSheafify (topology K J) (presheafEquivalence.functor.obj M).presheaf ≫
        ((SheafOfModules.toSheaf (twistedRing K J hJ S)).map
          (siteComparison.hom.app M)).hom
  /-- Forgetting the group creates kernels. -/
  createsKernels
      (M N : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S))
      (f : M ⟶ N) :
    Nonempty (CreatesLimit (parallelPair f 0)
      (forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck S)))
  /-- Forgetting the group creates cokernels. -/
  createsCokernels
      (M N : EquivariantSheaf (K := K) J.toGrothendieck (baseRing J.toGrothendieck S))
      (f : M ⟶ N) :
    Nonempty (CreatesColimit (parallelPair f 0)
      (forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck S)))
  /-- Zero is detected after restricting to the base site. -/
  zero_iff (N : ringedSiteModules (twistedRing K J hJ S)) :
    IsZero N ↔ IsZero ((forgetSheaf J.toGrothendieck (baseRing J.toGrothendieck S)).obj
      (sheafEquivalence.inverse.obj N))

```

The implementation of presentation adds inverse_morphisms := ?_ and the complete
proof from himap, hio and hsmap; its theorem signature is unchanged.

## Users

The downstream.py --uses result is a textual over-approximation on the final
identifier `Presentation`; all its hits are included below. Most Paper hits refer
to different local Presentation declarations. The 15 current direct importers of the
changed module are checked through lcompile.py (the assigned item is checked as
part of the delivery). Unchanged temporary importer copies are removed immediately
after their check. No consumer needs an adapted signature or proof.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent | unclaimed | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.AlgebraicGeometry.FieldActionDerivedSectionTransport | unclaimed | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.AlgebraicGeometry.FieldRingedScalarAdjunctionTransport | unclaimed | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.CategoryTheory.ActionToposGeometricRestriction | unclaimed | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.CategoryTheory.CondensedDerivedInflationArrows | P9 | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.CategoryTheory.CondensedNormalSubgroupComparison | unclaimed | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.CategoryTheory.CondensedSplitCosetInduction | unclaimed | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.CategoryTheory.InternalActionDiagonalTensor | unclaimed | New module; uses the repaired presentation specification. |
| Sheaf.CategoryTheory.InternalActionSheafEquivalence | F3 | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.CategoryTheory.InternalActionSitePresentation | unclaimed | Add inverse-map law and its complete construction proof. |
| Sheaf.CategoryTheory.InternalRestrictionModulePullback | unclaimed | New module; uses the repaired presentation specification. |
| Sheaf.CategoryTheory.InternalRestrictionModuleTensor | G3 | Use repaired presentation; theorem signature unchanged; assemble strict subarguments. |
| Sheaf.CategoryTheory.InternalRestrictionModuleTensorData | unclaimed | New module; uses the repaired presentation specification. |
| Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison | unclaimed | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.CategoryTheory.RelativeCyclicRestrictionModel | unclaimed | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.CategoryTheory.SheafActionGrothendieckInflation | unclaimed | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.CategoryTheory.SheafProductFixedAdjunction | unclaimed | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.DiagonalTracePresentationExistence | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.DiagonalTraceResultExistence | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.FieldActionToposCoefficients | unclaimed | Direct importer; all existing projections and theorem signatures remain unchanged; compile checked. |
| Sheaf.Paper.IndUnipotentProcyclicDifference | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.IntegralDirectImageTowerData | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.IntegralTowerGeometryLimits | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.IntegralTowerImageReconstruction | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.PolynomialRankOneDifferenceModel | A6 | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.PrimeToEllDerivedInvariantsReduction | M6 | Direct importer unchanged; its baseline compilation independently exceeds the 60-second limit (66–68 seconds), so this timeout is pre-existing and is not attributed to the presentation repair. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | S5 | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.SfFieldMateDomain | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.SmoothPurityTowerP1Data | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1ComparisonsWithLine | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1DiagonalProjectionFactor | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1DiagonalTransport | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1FiniteAdjunctionAssembly | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1FirstTraceReordering | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1KernelFiniteComparison | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1KernelScalarData | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1KernelSplittingBaseChange | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1ProjectionTraceIdentification | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1SecondTraceReordering | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1SingleLevelConstruction | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1SingleLevelData | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1SingleLevelTransport | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1SingleLevelTriangles | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1TriangleFactorization | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1TriangleWords | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TowerP1UniformPresentation | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.SixFunctors.TensorExchangeCoherentConclusions | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.SixFunctors.TensorExchangeNormalizedModels | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.SixFunctors.TensorExchangePresentation | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |
| WeilConjectures | unclaimed | Textual Presentation hit in transitive importer; no structure constructor to adapt; existing declarations unchanged. |


Compiler evidence (all through the prescribed lcompile service):

- The final assigned theorem compiles in 6.1 s; repaired presentation in 18–22 s.
- The first five checked consumers passed: CondensedGaloisGlobalDescent,
  FieldActionDerivedSectionTransport, FieldRingedScalarAdjunctionTransport,
  ActionToposGeometricRestriction and CondensedDerivedInflationArrows.
- The batch passed CondensedSplitCosetInduction, InternalActionSheafEquivalence,
  LatticeKoszulTriangulatedCupComparison, RelativeCyclicRestrictionModel,
  SheafActionGrothendieckInflation, SheafProductFixedAdjunction and
  FieldActionToposCoefficients. Their service return codes were zero.
- PrimeToEllDerivedInvariantsReduction hit the per-file limit. Profiling the
  unchanged consumer against the published baseline also returns 124 at 66.2 s;
  the repaired overlay returns 124 at 68.3 s. Both profiles spend about 50–54 s
  on type checking and 52–55 s on linting. There is no signature or elaboration
  error caused by the new field. This module is held by M6 and is not changed.
- CondensedNormalSubgroupComparison passed separately (service return code 0)
  after the batch stopped on that pre-existing timeout. All unchanged importer
  copies have been removed and are omitted from the delivery.

## Status

landed 20261026T081855-L-2094745 2026-10-26 (merge of deliver/G3/Sheaf.CategoryTheory.InternalRestrictionModuleTensor)
