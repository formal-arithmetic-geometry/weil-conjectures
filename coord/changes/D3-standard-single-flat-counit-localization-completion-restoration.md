# AlgebraicGeometry.standardSingleFlatCounit_localization_completion restoration

## Reason

Restore the exact item recorded in coord/rework.tsv from its quarantine archive.
The archive has zero holes; its absence is a cluster-recovery quarantine, not a
withdrawal. Preserve the theorem's binders, universe, conclusion, docstring and
sole public import. The existing localization homology theorem already constructs
the correct stalk complex and supplies the complete comparison. The proof names
that result and destructures it before dropping only its extra equality witness.

Synchronize the existing node's proof with this actual argument. Its old plan
separately obtained an arbitrary bounded flat complex and a derived pair before
applying homology. That is not the Lean proof: the homology theorem itself gives
one complex tied to the supplied local presentation. Its scalar-extension pair
remains needed transitively. No target or definition changes.

## Old

The live source path is absent; the exact preserved archive is
quarantine/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationCompletion.lean.
Its complete text is:

```lean
module

public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationHomology

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Completion from the actual localized sheaf presentation data.
Source: Stacks Project, Tags 0DJ9, 06YB and 0D5S.
(blueprint: lem-pc-standard-single-flat-counit-localization-completion).
Proof: unpack hpres into its bounded flat complex K on S, its direct-image
identification e, ordinary-pullback identification t, and counit equation. Take
K's termwise stalk at g(a), regarded as a point of S. Exactness and additivity of
stalks preserve the complex, zero terms and its upper bound. Flat sheaves have
flat stalks. Transport this complex along the open-stalk ring isomorphism
O_S,g(a) = O_B,g(a); this is the required P, not an arbitrary flat complex.
Choose a universal left-derived extension-of-scalars pair for g.stalkMap a.
The ordinary tensor-pullback stalk formula, derived using exact stalk functors,
identifies the stalk of derived pullback with that left-derived scalar extension.
Its counit agrees with the stalk of the sheaf counit: on flat representatives this
is the pure-tensor stalk formula, and localization descends that identity.
Apply these comparisons to e and t and then take degree-n homology. Exact stalks
commute with homology, so the presentation equation gives the required square.
Finally transport from V and S to A and B by their open-stalk ring isomorphisms.
Derived direct image commutes with restriction to full inverse-image opens,
and derived pullback commutes with open restriction; the unit-and-counit mate
identities identify the restricted standard base-change map with the original
one. Thus the resulting eL and eR have exactly the displayed endpoints and
factor the original map. One complex P works in every integer degree. No global
bound on B, flatness of g, or arbitrary witness of unproved existence is used. -/
theorem standardSingleFlatCounit_localization_completion
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A)
    (S : B.Opens) (V : A.Opens) (hS : g a ∈ S) (hV : a ∈ V)
    (hSaff : IsAffine S.toScheme) (hVaff : IsAffine V.toScheme)
    (hVS : V ≤ g ⁻¹ᵁ S)
    (hpres : StandardSingleFlatCounitPresentation (p ∣_ S)
      (M.restrict (p ⁻¹ᵁ S).ι) (g.resLE S V hVS)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    let T := A.presheaf.stalk a
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} T)
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Flat R (P.X i)) ∧
      ∃ (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          (ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory (.up ℤ) ⋙
            DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) ∧
        ∀ n : ℤ,
          ∃ (eL : (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
              ((DerivedCategory.homologyFunctor _ n).obj
                ((derivedPullback g).obj ((schemeDerivedDirectImage p).obj
                  ((DerivedCategory.singleFunctor _ 0).obj M)))) ≅
              (DerivedCategory.homologyFunctor _ n).obj
                (LF.obj (DerivedCategory.Qh.obj
                  ((HomotopyCategory.quotient _ (.up ℤ)).obj P))))
            (eR : (DerivedCategory.homologyFunctor _ n).obj
                (DerivedCategory.Qh.obj
                  (((ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory
                    (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≅
              (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
                ((DerivedCategory.homologyFunctor _ n).obj
                  ((schemeDerivedDirectImage (pullback.snd p g)).obj
                    ((DerivedCategory.singleFunctor _ 0).obj
                      (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))))),
            (RingedSpace.moduleStalkFunctor A.toRingedSpace a).map
                ((DerivedCategory.homologyFunctor _ n).map (standardSingleBaseChangeMap p M g)) =
              eL.hom ≫ (DerivedCategory.homologyFunctor _ n).map
                (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ eR.hom := by
  dsimp
  obtain ⟨P, hPident, hPbound, hPflat, LF, ε, hLF, hhom⟩ :=
    standardSingleFlatCounit_localization_homology
      h_affine p M hM g a S V hS hV hSaff hVaff hVS hpres
  exact ⟨P, hPbound, hPflat, LF, ε, hLF, hhom⟩


end AlgebraicGeometry
```

## New

Restore lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationCompletion.lean
with this complete text:

```lean
module

public import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitPresentation
import Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationHomology

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Completion from the actual localized sheaf presentation data.
Source: Stacks Project, Tags 0DJ9, 06YB and 0D5S.
(blueprint: lem-pc-standard-single-flat-counit-localization-completion).
Proof: unpack hpres into its bounded flat complex K on S, its direct-image
identification e, ordinary-pullback identification t, and counit equation. Take
K's termwise stalk at g(a), regarded as a point of S. Exactness and additivity of
stalks preserve the complex, zero terms and its upper bound. Flat sheaves have
flat stalks. Transport this complex along the open-stalk ring isomorphism
O_S,g(a) = O_B,g(a); this is the required P, not an arbitrary flat complex.
Choose a universal left-derived extension-of-scalars pair for g.stalkMap a.
The ordinary tensor-pullback stalk formula, derived using exact stalk functors,
identifies the stalk of derived pullback with that left-derived scalar extension.
Its counit agrees with the stalk of the sheaf counit: on flat representatives this
is the pure-tensor stalk formula, and localization descends that identity.
Apply these comparisons to e and t and then take degree-n homology. Exact stalks
commute with homology, so the presentation equation gives the required square.
Finally transport from V and S to A and B by their open-stalk ring isomorphisms.
Derived direct image commutes with restriction to full inverse-image opens,
and derived pullback commutes with open restriction; the unit-and-counit mate
identities identify the restricted standard base-change map with the original
one. Thus the resulting eL and eR have exactly the displayed endpoints and
factor the original map. One complex P works in every integer degree. No global
bound on B, flatness of g, or arbitrary witness of unproved existence is used. -/
theorem standardSingleFlatCounit_localization_completion
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A)
    (S : B.Opens) (V : A.Opens) (hS : g a ∈ S) (hV : a ∈ V)
    (hSaff : IsAffine S.toScheme) (hVaff : IsAffine V.toScheme)
    (hVS : V ≤ g ⁻¹ᵁ S)
    (hpres : StandardSingleFlatCounitPresentation (p ∣_ S)
      (M.restrict (p ⁻¹ᵁ S).ι) (g.resLE S V hVS)) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let R := B.presheaf.stalk (g a)
    let T := A.presheaf.stalk a
    letI := HasDerivedCategory.standard (ModuleCat.{u} R)
    letI := HasDerivedCategory.standard (ModuleCat.{u} T)
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ),
      (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, Module.Flat R (P.X i)) ∧
      ∃ (LF : DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} T))
        (ε : DerivedCategory.Qh ⋙ LF ⟶
          (ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory (.up ℤ) ⋙
            DerivedCategory.Qh),
        LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) ∧
        ∀ n : ℤ,
          ∃ (eL : (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
              ((DerivedCategory.homologyFunctor _ n).obj
                ((derivedPullback g).obj ((schemeDerivedDirectImage p).obj
                  ((DerivedCategory.singleFunctor _ 0).obj M)))) ≅
              (DerivedCategory.homologyFunctor _ n).obj
                (LF.obj (DerivedCategory.Qh.obj
                  ((HomotopyCategory.quotient _ (.up ℤ)).obj P))))
            (eR : (DerivedCategory.homologyFunctor _ n).obj
                (DerivedCategory.Qh.obj
                  (((ModuleCat.extendScalars (g.stalkMap a).hom).mapHomotopyCategory
                    (.up ℤ)).obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) ≅
              (RingedSpace.moduleStalkFunctor A.toRingedSpace a).obj
                ((DerivedCategory.homologyFunctor _ n).obj
                  ((schemeDerivedDirectImage (pullback.snd p g)).obj
                    ((DerivedCategory.singleFunctor _ 0).obj
                      (Scheme.Modules.tensorPullbackObj (pullback.fst p g) M))))),
            (RingedSpace.moduleStalkFunctor A.toRingedSpace a).map
                ((DerivedCategory.homologyFunctor _ n).map (standardSingleBaseChangeMap p M g)) =
              eL.hom ≫ (DerivedCategory.homologyFunctor _ n).map
                (ε.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫ eR.hom := by
  dsimp
  have hlocal := standardSingleFlatCounit_localization_homology
    h_affine p M hM g a S V hS hV hSaff hVaff hVS hpres
  rcases hlocal with ⟨P, hPident, hPbound, hPflat, LF, ε, hLF, hhom⟩
  exact ⟨P, hPbound, hPflat, LF, ε, hLF, hhom⟩


end AlgebraicGeometry
```

## Users

The live downstream query with --allow-missing reports zero users, since the item
and its direct parent are quarantined. Scanning both lean/ and quarantine/, with
live files taking precedence, gives one direct importer and 92 transitive consumers.
Their existing public statements and definitions retain exactly their meaning.
No consumer source is adapted in this delivery. All archives stay intact.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CartesianFlatSingleLocalizedBaseChange | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleTermwiseComparison | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineCechModelPerfect | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveModel | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineStructureProjectiveRepresentation | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardAffineTargetNormalization | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreNaturality | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridge | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueBridgeCore | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparison | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonSource | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricComparisonTargets | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceResidueComparison | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankPerfectChart | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardSingleRankUnrestrictedPerfectChart | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCore | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusCoreRank | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocus | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalSingleRankLocusFinitePresentation | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineCechPerfectModel | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatBoundedPresentationModel | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyModel | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatCohomologyProperties | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatDirectImagePerfectChart | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatFinitePresentationModel | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalHomCompositeIso | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatImageGlobalHomBaseChangeIso | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleDerivedDirectImagePerfect | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenNoetherianComparison | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleOpenPseudoCoherent | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChangeEpi | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization | unclaimed | Direct archived consumer; theorem call and statement remain valid unchanged. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationCompletion | D3 | Restore the complete theorem with its exact archived signature and public import. |
| Sheaf.AlgebraicGeometry.StandardSingleStalkFlatCounitModel | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Transitive consumer; same theorem type, public exports and mathematical meaning; no adaptation. |

## Status

landed 20261021T012353-L-2181178 2026-10-21 (merge of deliver/D3/Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationCompletion)
