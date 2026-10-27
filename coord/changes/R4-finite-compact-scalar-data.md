# Finite compact-support scalar comparison data

## Reason

The independent open and proper transport lemmas must refer to the actual canonical
comparison definitions. Move those definitions into a data module, then publicly
re-export it from the assigned item, so its proof may import the two factor lemmas
without an import cycle. All nine existing comparison definitions and abbreviations
retain their exact names, signatures, attributes and bodies. The old public imports
remain public imports of the data module. No target statement or mathematical data
changes. The new open/proper coordinate isomorphisms are actual composites, without
chosen existence witnesses.

## Old

The following is the original data-bearing portion of the assigned module:

```lean
module
public import Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension
public import Sheaf.Paper.StratumScalarExtension
public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.EtaleDerivedScalarTensor
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import Sheaf.Paper.SfCompactSupportRestrictionOfScalars
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import Sheaf.Paper.EtaleProEtaleScalarMate

/-!
# Canonical transport of the finite compact-support scalar mate

Source: Stacks Tags 0GL6 and 09AL; the scalar-mate compatibility of the etale and
pro-etale comparisons, followed by the normalized intrinsic realization.
(blueprint: lem-finite-compact-support-scalar-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteCompactScalar

/-- The scalar/open comparison fixed by uniqueness of the left adjoint. -/
@[irreducible] def openScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        scalarExtension φ Z ≅
      scalarExtension φ X ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory := by
  let ea := upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j
  let eb := upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j
  let adjA := ((openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} A) j).ofNatIsoRight ea.symm).mapDerivedCategoryAdjunction
  let adjB := ((openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} B) j).ofNatIsoRight eb.symm).mapDerivedCategoryAdjunction
  let adjX := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let adjZ := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
  let e := Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j)
  exact (adjA.comp adjZ).leftAdjointUniq ((adjX.comp adjB).ofNatIsoRight e.symm)

/-- Proper scalar extension followed by the open scalar comparison. -/
@[irreducible] def compactScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian c.Z] [IsNoetherian Y] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        scalarExtension φ Y ≅
      scalarExtension φ X ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c := by
  have : ∀ L, IsIso ((scalarMate φ c.g).app L) :=
    (properFiniteCoefficientExtension φ c.g).1
  have : IsIso (scalarMate φ c.g) := NatIso.isIso_of_isIso_app _
  let e := asIso (scalarMate φ c.g)
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openScalarIso φ c.i) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.Etale.FiniteCompactScalar

namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- The actual sheaf map of constant coefficient rings. -/
abbrev scalarRingMap
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    proEtaleConstantRing T A ⟶ proEtaleConstantRing T B :=
  proEtaleConstantRingMap (T := T) φ

/-- The scalar comparison through intrinsic realization, fixed by its right square. -/
@[irreducible] def realizationScalarIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T A).functor ⋙
        pbcDerivedExtend.{u} (scalarRingMap φ T) ≅
      @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
        (sfIntrinsicDerivedEquivalence T B).functor := by
  let EA := sfIntrinsicDerivedEquivalence T A
  let EB := sfIntrinsicDerivedEquivalence T B
  let ρ : proEtaleConstantRing T A ⟶ proEtaleConstantRing T B := scalarRingMap φ T
  let adj : pbcDerivedExtend.{u} ρ ⊣ pbcDerivedRestrict.{u} ρ := pbcDerivedScalarAdjunction ρ
  let rightIso : pbcDerivedRestrict.{u} ρ ⋙
      (sfIntrinsicModuleEquivalence T A).inverse.mapDerivedCategory ≅
      (sfIntrinsicModuleEquivalence T B).inverse.mapDerivedCategory ⋙
      @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
        (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) := by
    simpa only [ρ, pbcDerivedRestrict, pbcRestrict, scalarRingMap, proEtaleConstantRingMap,
      proEtaleCoefficientRestrictScalars, sfFixedRestriction, Sheaf.restrictScalars,
      Sheaf.derivedRestrictScalars] using
      Functor.mapDerivedCategorySquareIso (sfInverseRealizationRestriction T φ)
  let s : EA.functor ⋙ pbcDerivedExtend.{u} ρ ≅
      @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙ EB.functor :=
    ((EA.toAdjunction.comp adj).ofNatIsoRight
      rightIso).leftAdjointUniq
      ((Adjunction.ofIsRightAdjoint
        (@Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
        (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
        (RingHom.ulift.{u + 1, u + 1, u, u} φ))).comp EB.toAdjunction)
  exact s

/-- The termwise factorization of intrinsic site comparison through realization. -/
def intrinsicSiteFunctorIso (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :
    ProEtale.finiteCoefficientIntrinsicDerivedComparison T A ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence T A).functor :=
  Functor.mapDerivedCategoryCompIso _ _

/-- Site comparison and coefficient extension, in the intrinsic ringed presentation. -/
@[irreducible] def siteScalarIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    ProEtale.finiteCoefficientIntrinsicDerivedComparison T A ⋙
        pbcDerivedExtend.{u} (scalarRingMap φ T) ≅
      Etale.scalarExtension.{u} (RingHom.ulift.{u + 1, u + 1, u, u} φ) T ⋙
        ProEtale.finiteCoefficientIntrinsicDerivedComparison T B :=
  Functor.isoWhiskerRight (intrinsicSiteFunctorIso A T) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (realizationScalarIso φ T) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ProEtale.pbcComparisonReduction.{u} T (RingHom.ulift.{u + 1, u + 1, u, u} φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (intrinsicSiteFunctorIso B T).symm

/-- Compact support through realization, using the normalized proper comparison. -/
@[irreducible] def compactRealizationIso
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfIntrinsicCompactSupport c A ≅
      ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor := by
  let EX := sfIntrinsicModuleEquivalence X A
  let EZ := sfIntrinsicModuleEquivalence c.Z A
  let J := ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i
  let o : EX.functor ⋙ sfIntrinsicExtensionByZero c.i A ≅ J ⋙ EZ.functor :=
    EX.funInvIdAssoc (J ⋙ EZ.functor)
  let od := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso o ≪≫ Functor.mapDerivedCategoryCompIso _ _
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight od _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison c.g A) ≪≫
    (Functor.associator _ _ _).symm

/-- The compact-support site comparison at a bounded-below etale input. -/
@[irreducible] def compactSiteIso
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y A).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj G.obj) ≅
      (sfIntrinsicCompactSupport c A).obj
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj) :=
  (intrinsicSiteFunctorIso A Y).app _ ≪≫
    (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
      ((ProEtale.compactSupportSiteComparison (ULift.{u + 1, u} A) c).app G).symm ≪≫
    (compactRealizationIso A c).symm.app _ ≪≫
    (sfIntrinsicCompactSupport c A).mapIso ((intrinsicSiteFunctorIso A X).app G.obj).symm

/-- The explicit transported proper/open coefficient isomorphism at an etale origin. -/
@[irreducible] def intrinsicCompactScalarIsoOfOrigin
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian c.Z] [IsNoetherian Y]
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (GB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
    (eGB : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj G.obj ≅
      GB.obj) :
    (pbcDerivedExtend.{u} (scalarRingMap φ Y)).obj
        ((sfIntrinsicCompactSupport c A).obj
          ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj)) ≅
      (sfIntrinsicCompactSupport c B).obj
        ((pbcDerivedExtend.{u} (scalarRingMap φ X)).obj
          ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj)) :=
  (pbcDerivedExtend.{u} (scalarRingMap φ Y)).mapIso (compactSiteIso A c G).symm ≪≫
    (siteScalarIso φ Y).app _ ≪≫
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y B).mapIso
      ((Etale.FiniteCompactScalar.compactScalarIso
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) c).app G.obj ≪≫
        (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).mapIso eGB) ≪≫
    compactSiteIso B c GB ≪≫
    (sfIntrinsicCompactSupport c B).mapIso
      ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).mapIso eGB.symm ≪≫
        (siteScalarIso φ X).symm.app G.obj)

```

## New

The code displayed above is retained verbatim in
`lean/Sheaf/Paper/FiniteCompactSupportScalarTransportData.lean`, except for the two
proof-only imports at the end of the import list, which are needed by the proper
factor and now occur in its module. The item starts with:

```lean
module
public import Sheaf.Paper.FiniteCompactSupportScalarTransportData
import Sheaf.Paper.FiniteOpenScalarTransport
import Sheaf.Paper.FiniteProperScalarTransport
```

`intrinsicCompactScalarIsoOfOrigin_hom` keeps its complete original signature.
Its proof is assembled from the independently stated open and proper squares.
All previously public definitions and public imports remain publicly accessible
through the same original module. No instances, simp attributes or definitional
bodies change. The only newly added definitions are the explicit component
coordinates `openRealizationIso`, `openSiteIso` and `properSiteIso` in
`FiniteCompactScalarCoordinates`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedTransportedHomCounitFormula | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedOpenCounitTensorAction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceCentredChartConstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceChartRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceFrameData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceNormalFrameConstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.DiagonalDifferenceReesFrame | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineCounitTensorNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineLineTensorCounit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineProjectionReassociation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTensorActions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryAffineTowerTensorCounit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1TensorAction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperOpenRefinementMatePlusCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousCoefficientGeometricCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleLatticeData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.ContinuousConstructibleStratifiedLattices | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.GeometricCurveDiagramDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.MarkedGeometricCurveModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.NormalizedContinuousCoefficientFamily | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.NormalizedStratifiedEmbeddedLattices | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.OrdinarySectionScalarComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.PairEigenvalueCurveTest | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicComparisonBridge | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicStrataBridge | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.SmoothAffineConstituentPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicActualSystemsNormalized | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicClosureScalarCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicCommonStageFibreTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicCommonStageFibreZeroMap | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicCommonStageHeartExactness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicCompletedProjectionShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicCompletedTensorRealizationDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicFiniteConstructibilityComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicFiniteRealizationCocone | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicFiniteRealizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicFiniteScalarCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStage | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreCommonStageData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibrePullback | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreScalar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedPuritySystems | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensorComponents | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPuritySourceNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPuritySourceTransitionSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicPurityTwistRestrictionComponents | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicRealizationFamilyData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicReindexingCore | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicReindexingFunctoriality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicReindexingHom | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicReindexingTensor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | N3 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicTraceTensorShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdmissibleCupCoefficientPassages | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdmissibleHomSubstitution | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineCoefficientCounitNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineCompactificationComparisonNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineCounitScalar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalDncCoordinateIdentity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalDncNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationConstructions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationTranslationIntegration | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalIntegrationTranslationTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalPowerCoefficient | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalPresentedBaseChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalRawTransposePower | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalRestrictedTransposes | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalSectionCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalTraceRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineDiagonalTransposePower | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineIntegrationExponentTransition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineLineCanonicalScalarCounit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineLineComparisonNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineLineCompositeTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineLineStandingTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineOrderedEvaluationContraction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineOrderedFirstLineCounit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineOrderedIntegrationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineOrderedIntegrationSuccessor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineOrderedIntegrationTransposes | H7 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineOrderedTransposeCounit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpacePurityCompositionMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpacePurityCoordinateInvariance | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpacePurityOrderedBlocks | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceProductData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionConstructions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineTargetDiagonalDnc | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineTowerIntegrationSiteTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BarrettIndRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BaseChangedLineTraceEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BasicOperationCoefficientCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BasicOperationReductionAndEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryFiniteEvaluationRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryFiniteSiteData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryFiniteSiteRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryFiniteTorDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.BoundedSiteExchangeTransposes | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CanonicalTateArrowNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CanonicalTateComparisons | E9 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CartierSupportedComparisonSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartCounitScalarTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalAssemblyData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartDncNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartDncSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactorData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartDncVectorFactors | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartEpsilonPasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartExceptionalCounitEquation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartExceptionalMateCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartIntegrationAdjoints | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartNormalIntegrationSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChartTargetOpenDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalFiltrationDiagramFibres | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalFiltrationExactDiagram | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalFrontierExistence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonFibres | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseFiniteConstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseFiniteOperations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseIntrinsicFibrePullback | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseOperations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRealizationLocalSpectrum | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRealizationPunctualPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalRealizedAnchorEigenvalue | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreCommonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalWeilCoherentDiagramStages | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationTransportData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiniteDiagramDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalWeilPrescribedIsomorphismLifts | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClopenCompletedTowerRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClopenCounitAdjointComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClopenPrescribedWeilFiltration | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemRealizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClosedCoefficientTransposeCocycles | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClosedEmbeddingPerfectEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClosedScalarDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ClosedSupportExceptionalMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CochainLocalizationTensorIso | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefSupportOpenTensorModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsComparisonExistence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefSupportPointSectionsModelExistence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefficientEvaluationNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefficientMapGeometricSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoefficientUnitTowerNormalized | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonProjectionCompactificationOnStage | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonProjectionComparisonEquations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonProjectionCompositionOnStage | J1 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonProjectionProperOnStage | J2 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonProjectionTensorCompatibility | A7 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageOpenHeartAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStagePerfectEvaluationDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStagePointReturn | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageRestrictionTensorDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationCore | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageSmoothOperationShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactExchangeOperationCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientExchangeInvertible | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientModelsOrdinaryExistence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCompletedProjectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCompletedScalarArrow | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCompositeTransposeDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | J1 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportExchangeDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteScalarMateNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportLimitEquationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportLimitEquationRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedScalarDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedTowerLimit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportPathReductionSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionCoefficientChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionCoherenceLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFieldStages | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFiniteStages | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | H3 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionIntegralStages | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionRightUnit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportRationalScalarIso | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportRealizationIdentity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportReductionAdjoint | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportScalarLimitReduction | F5 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportScalarProjectionIdentification | A4 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportScalarShiftNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportScalarShiftStructures | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportScalarShiftWitness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarComposition | S2 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportStrictScalarRefinement | A4 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportSystemTransposeNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportTermHomFinite | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportTotalLimitRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactSupportTowerReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactWeilCocycleEndomorphismRecurrence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactificationBOrdinaryProjectionSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactificationBProjectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactificationBProjectionDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactificationBProjectionReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactificationFiniteProjectionModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactificationOpenLimit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactificationPushLimit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactificationScalarData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactificationStrictRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ComparedSmoothExchangeComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ComparisonImageClosedSectionNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompleteCompactificationLimitRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompleteCompactificationLimitSupport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompleteIntegralConstantRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompleteProjectionDescentMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompleteProjectionMateDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompleteProjectionReductionSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompletedContinuousHomHypotheses | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompletedLocalFibreComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompletedPullbackFractionDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompletedScalarAssociatorLocalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompletedScalarExactLocalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompositionComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompositionIteratedMateExpansion | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDefinitions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompositionModelOrientationDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompositionSingleMatePresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CompositionTensorMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConcreteIntegralProjectionCone | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConcreteOpenScalarTensorSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConcreteProjectionCoefficientCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConcreteProjectionFactorizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConcreteProjectionFieldDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConcreteProjectionReductionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConcreteProjectionReductionSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConcreteProperScalarTensorSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConcreteSupportScalarIsomorphism | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CondensedExceptionalCounitRepresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CondensedExceptionalRealizationProperties | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CondensedExceptionalRefinementCounits | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CondensedExceptionalSystemRecognition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CondensedOpenCoefficientModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitRealizationSupport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CondensedOpenUnitComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantCompletedOrdinaryAssociativity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantCompletedScalarAssociativity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantDirectImageTowerRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionCyclicSheetPartition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackReturnResidue | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionPullbackSheetComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionRestrictionLocalConjugacy | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnExactFunctor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalOperators | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnLocalSpectra | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionReturnTransportComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCoefficientEquivalences | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetCommonStageEquivalences | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetGeometry | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetHeartData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionSheetTensorSplitting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantScalarTowerAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstantScalarTowerMates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientStages | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCompositor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCompositorData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalLeftRefinements | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalRefinementMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleLeftCompositorCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleTensorComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ConstructibleWeilModelSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateAdjunctionComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateCartierBoundarySign | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateLineAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateLineAdjunctionMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateLineAugmentationRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateLineConjugateExponents | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateLineCounitTensor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjectiveTrace | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionSiteTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateSectionTensorTrace | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateSupportedProductRecursion | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateTowerCompactTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateTowerExceptionalCompositors | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationFusion | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CtfCoefficientStageSelectors | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CurveClassicalFiltrationPullback | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CurveClassicalPullbackExists | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.CurveRestrictionLocalPowers | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DerivedHomSubstitutionCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DerivedPoincarePairing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DerivedTensorRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineCounitRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineIntegrationSiteSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineRankZeroActual | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceMapAgreement | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalAffineTraceSiteData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalCounitComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncAffineModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncAssemblyGlobal | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncChartNormalization | G5 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncEtaleNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalDncEtaleNaturalityTwist | A8 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryChartLift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryOrientationGluing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryOrientationNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryOverlap | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrdinaryRealizeRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationChartExistence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationCharts | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationChoiceIndependent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationRefinement | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DiagonalOrientationRefinementData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DifferenceCoordinateSectionIdentifications | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DifferenceFirstInputRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DifferenceSecondInputRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DoubleDiagonalSectionIdentifications | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DualBaseChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DualizingCocycleSourceEtale | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DualizingCompositionCoefficientMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DualizingPrimitiveOpenRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DualizingSigmaCocycleLocality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleAffineIntegrationCoefficientEquation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleAffineProjectionCoefficientMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleCartesianTowerTensorComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleCompositeEComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleMiddleTensorAssembly | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleOpenCounitFlatModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleOrientationLocality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleOriginScalarProjectionSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleSumCounitScalar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EtaleTensorSourceTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EvenLineBinaryProductNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EvenLineCoefficientProjectionNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EvenLineCoordinateIntertwining | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EvenLineProductIntegrationSymmetry | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.EvenTateLineSelfSymmetry | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExactProperOpenProjectionMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalBaseChangeIntegralMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalDualizingBaseChangePasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFieldDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteIntrinsicBounds | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteOperations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRestrictionAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteScalarMates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalIntegralScalarMates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FdPullbackWeilReturnSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldCohomologyPerfectDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExceptionalFiniteCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExceptionalNormalizedAdjoints | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemAdjoints | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemComponents | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemFiniteComposite | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemIso | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExceptionalSystemLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionCompletedStrictLimit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionIntegralModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionLimitEquations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionRationalComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionRationalDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionRationalModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionReductionDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionReductionLimits | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionSourceNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionStrictLimits | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionSystemCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldExtensionTowers | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemFiniteOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemHeart | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemNormalizations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldOrientationSystemRigidity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldOrientedExchangeSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldProjectionOpenSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldProjectionOriginWitnesses | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldProjectionProperSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldProjectionRefinementSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldProjectionSystemData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldProjectionSystemSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldProjectionTensorConstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldPuritySystemTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldPuritySystemTransposeBase | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldPuritySystemTransposeCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldPurityTransposeArrows | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldPurityTransposeLevelWords | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionCoefficientSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionIntegralComponent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionIntegralNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekSupportEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekSystemCocycle | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekSystemCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekSystemComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekSystemEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekSystemFiniteLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekSystemMixed | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekSystemMixedCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekSystemModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekSystemRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekSystemTransitionWords | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldShriekSystemTransitions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FilteredCondensedCanonicalComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitBijective | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FilteredCondensedCounitFiniteFormula | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPair | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointCompositorTransposes | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportCoefficientSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportEvaluationRefinement | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactSupportScalarComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactificationEigenvalues | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactificationStalkReturn | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalBaseChangeReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalDncReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationAssembly | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalReductionComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteDiagonalVectorReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteExceptionalCompositorCoefficients | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteExceptionalSiteNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFirstRootChart | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteForwardCompactifiedSwap | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteForwardProductCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtensionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportGeometricSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportSiteSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteGammaEvaluationIsIso | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteGeometricOrientationExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityFactors | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteGeometricPurityMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteGeometricTensorExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteHorizontalShriekMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteIdentityCompositionNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteMateDomain | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteOrientationReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteOrientationScalarPresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FinitePointCounitUnitNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FinitePositiveChartFrameExt | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FinitePositiveChartRecursion | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FinitePositiveRootChartPower | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FinitePositiveRootCharts | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProductOpenRestrictionPasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProductOrdinaryNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionBinarySquare | B6 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionCompactificationSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionCompactificationTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionCompositionTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionFromDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionIdentityNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionInputNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionOpenAssembly | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionOperationPresentation | B7 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionPresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionRefinementLeft | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteProjectionTensorSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FinitePublishedRootChartPower | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteQuotientModuleBalancing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteRationalHeartComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteRealizationEtaleOrigin | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionBaseChangeSource | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionExceptionalFiniteModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionLineChartScalars | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionLineInputConstructible | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionPositiveLineComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionReassociation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionShiftedPullbackCube | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorFactors | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionTensorSource | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteReductionThetaFactor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteRefinementProjectionRealization | B8 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteRestrictionDiagramNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteRootLinePowerTransition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteRootTensorPresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteScalarCochainComparisonIso | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteScalarMonoidalRepresentative | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteScalarRepresentativeIso | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteScalarTensorData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteScalarTensorSource | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteSheafH0Augmentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteSignedTwistProducts | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteSourceChartScalarTransition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteSupportCompositorCoefficient | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteSupportCompositorExistence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteSupportOriginComparison | C5 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteSupportedReductionEquation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTargetChangeCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTateSourceMap | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTateSourceStructuralCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorFixedComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorLineChartReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorPresentationReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorProductFrameExt | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorProductMap | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorProductMapIsIso | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorPullbackCompositionReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorPullbackTensorReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorSemilinearReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftFirst | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorShiftSecond | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorSignedReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTensorSymmetryCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTripleProductDefinitions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTripleProductNormalForms | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FirstRootLinePullback | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FixProjectionCompactificationComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FixedPairTruncationCohomology | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ForwardProductCoordinateTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcIntegralComparisonLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrameworkPbcRawComparisonLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | B9 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | C9 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.FrobeniusSystemExchangeInverse | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GeneralChartComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GeometricCommonStageDirectImage | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GeometricQuotientWeilCompositionSeries | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GeometricScalarFiniteEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GermReparametrizationDerivedDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GlobalIdentityNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.GlobalVerdierDualityData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.HigherIdentityCompositionNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IdentificationCoefficientTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IdentityCoefficientTransportData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IdentityCompactificationLimitComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IdentityCompactificationSystemMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IdentityOpenSystemEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionBijection | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionReconstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralAdjunctionSourceComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralClosedSupportNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralCoefficientModelComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | D8 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralCompositionCoefficientSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralCompositorLimitRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionHom | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralDualizingExceptionalUnit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralLissePullbackNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralOpenEmptyPullbackVanishing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralOpenSupportNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralOrdinaryProjectionReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralOrientationReductionInjectivity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralOrientationShiftedSheafModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralOrientedExchangeSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | E3 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralProjectionCoordinateData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralProjectionOperationPresentation | C6 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralProjectionReductionCoordinates | C7 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralProjectionReductionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralProjectionReductionNormalization | C9 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralProjectionRefinementSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralProjectionSystemCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralPullbackAugmentationAmbient | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralPurityCounitReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralQuotientCohomologicalBounds | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralReconstructionComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralReductionJointFaithfulness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralReductionShiftedHomFiniteQcqs | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralScalarIsomorphismExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralSectionsPerfectReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralSemilinearGermSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralSmoothAdjunctionPresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralStageProjectionReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralStageProjectionStructuralIdentities | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralSupportFunctorNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralSupportNormalizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralSupportReductionNormalization | D5 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralTowerImageReconstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegralTowerProjectionMates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegrationAffineExponentTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegrationCoefficientProjectionNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegrationExponentTransposeData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegrationExponentTransposeTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntegrationProjectiveExponentSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IsomorphismFiniteExchangeCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IteratedPurityScalarPasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IteratedTateSourceComposite | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.KummerSiteCohomologyNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LineCounitComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LineKummerFieldRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LineZeroClassExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseLatticeChoiceExistence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLiftData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseLatticeLisseDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseLatticeNormalizedRealizations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseLatticeRealizationFaithful | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseLatticeSingleComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseLocalizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseLocalizationExistence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseLocalizationLocalFreeness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseLocalizationRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseLocalizationSlices | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionAssociativity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeScalarTower | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeTransportAddition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeTransportNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeWeilAddition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusStepCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocallyClosedScalarPasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCompactSupportExchangeData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupCoefficientSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupFieldCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupFieldNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupFieldOperations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupNormalizedScalars | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupOperationComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorClosure | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorElementary | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.MixedCupTensorNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ModelAffineIntegrationOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ModelChartOrientationAssembly | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ModelOrientationChartDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ModelOrientationSourceNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ModelOrientationTateDetection | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeCompactProjectionFormula | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeConstantSupportModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeDerivedWeilTensorConstructible | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeGeometricBrownConstructibleComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeGeometricTensorComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeOpenDerivedTensor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeReductionCounitKFlat | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeWeilDualizingHomTransposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeWeilLocalizingBrownAdjoints | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeWeilScalarCounitData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalModelSectionOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalSectionIntegrationBaseChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalSectionIntegrationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalSectionIntegrationOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedCommonCoefficientLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedEtaleComparisonComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedEtaleRestrictionComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTrace | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedPullbackCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedPullbackNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedPullbackObjects | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedRationalLeftLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedRingRefinementLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedSmoothOrientationUnits | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedStageCoefficientCalculus | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.NormalizedSupportEtalePresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OpenExceptionalScalarLocality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OpenProEtaleCounitScalar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OpenProjectionFactorCoefficientChange | D6 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OpenScalarCounitSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OpenWeilCarrierRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OpenWeilCoefficientFibres | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OpenWeilFiniteStageFrobenius | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OpenWeilGeometricFibres | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OpenWeilPunctualSpectrum | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OperationCoefficientActionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrderedAffineComparisonNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrderedAffineLineTransposeNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrderedAffineTransposeData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrderedAffineTransposeProjection | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrderedAffineTransposeSuccessor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrderedCompactificationScalarSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrderedIntegrationComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrderedLineLevelBounds | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrderedTateScalarNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrderedTowerOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrdinaryOpenScalarComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrdinaryScalarBalancingLevel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrdinaryScalarReductionGenerators | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationCoordinateBoundaryPullback | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationCoordinateModelBoundary | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationGroundFieldRetagging | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationLocalResidue | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationPerfectLines | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientationScalarTowerTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OrientedPerfectDuality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.OriginalScalarMateShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.P1CounitScalar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.P1KummerTraceSiteTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.P1SplittingScalar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PairingData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PfReductionProperOpenIdentities | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PodCtfAdjunctions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PodMixedSupportCupProduct | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PodReconstructionCommonStageCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PodReconstructionCommonStageData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PodReconstructionRawRationalNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PodReconstructionScalarRealizations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PoincareDualityConventions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointFiniteMultiplicationInverse | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointFrobeniusNormalizationDefinitions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointFrobeniusTransportNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointIdentityExchangeRecipe | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointPowerRoosComparisonSpecialization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointPowerStrictInsertionSpecialization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointPullbackConeLocalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointQuotientComparisonCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointQuotientTowerHomotopy | E4 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointRestrictionWholeRoosSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointRootLimitCyclotomicAction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointScalarPunctualSpectrum | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSignedCyclotomicAction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSignedCyclotomicActionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSignedCyclotomicScalar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemInsertionComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemInsertionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemNormalizedComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemNormalizedComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemPowerRoosData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemRoosComparisonAssembly | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemRoosRestrictionAssembly | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemRoosTransportData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemRoosTransportRepresentative | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemStrictInsertions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointSystemTransportDescent | D4 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTateCommonStageCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTateDerivedComparisonCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTateFiberCanonicalComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTateFiberCoefficientComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTateFiberComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTateFiniteSectionComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTateNormalizedSectionGenerators | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTransportResolutionCancellation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTransportStrictQuotientFiniteEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTransportStrictQuotientIdentities | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTransportStrictQuotientModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointTransportStrictQuotientSections | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointWeilAlgebraicFlag | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlagData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointWeilPairingCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointWeilPairingRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointWeilTensorRepresentatives | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PointWeilTransportUnitShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PositiveRootGeneratorExt | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PositiveRootTensorProduct | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProEtaleCtfPullbackDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProductCompositionCoordinateComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProductExchangeCoordinateDefinitions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProductExchangeCounitCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProductHorizontalExchangeFactorization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProductOpenAdjunctionNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProductOpenCounitNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProductOpenSupportNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProductOpenTensorProjection | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProductOpenTensorProjectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionCompactificationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionFactorCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoherence | J4 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionPurityCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionReductionPresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionReductionWitnessedFlatDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionScalarSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientCocycles | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | F2 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionTensorIntegration | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionTensorModelComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionUnitIntegration | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectionWeilTensorDomainBridge | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperCoefficientDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperCoefficientDescentData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperCompactCoefficientActionComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperCompactIntegralComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperCompactRationalFunctorComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperEtaleOriginScalarData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperEtaleOriginScalarIsomorphism | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperIntegralScalarSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperIntegralTowerComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperRationalScalarSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperSupportCoefficientAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperSupportFiniteAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperSystemEvaluationTransitions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ProperWeilIterateGermFormula | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PulledOrderedLineSingle | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurCoordinateRepresentingFamily | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurIntegralRepresentingPairData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurIntegralSupportDerivedComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurIntegralSupportOrdinaryComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurRepresentingPairFiniteScalar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurSupportPresentationAlpha | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineBoundaryRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityCompactSupportTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityCompositionComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityConjugatesTowerReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityConstantFamilyBaseChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityFiniteReductionTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityFiniteTateSourceComparisonCalculus | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityKappaStages | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityKummerTriangleConcentration | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityOrientationDatum | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityPullbackLevelBounds | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityPullbackReductionTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityRankZeroFamilyReadings | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PuritySectionBaseComparisonLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PuritySectionConstantTrivialization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PuritySectionEtaleRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PuritySectionFibreSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PuritySectionNormalizedSpecialization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PuritySectionRestrictionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PuritySectionRestrictionEtaleFunctorial | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityTateDatum | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityTensorMapNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityTowerReductionComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityWitnessedMateNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.PurityWitnessedOpenChartTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportFiniteComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportFiniteMates | P3 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportImageComplete | P4 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportNormalizedLift | M4 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.QuotientGermTower | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.QuotientStalkNaturalDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RamifiedImageBalancingEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RamifiedQuotientSectionPushout | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalAmbientPullComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalAmbientPullModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalBalancedFreePullback | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalContinuousComparisonCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalContinuousFiltrationModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalContinuousPullbackTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalCoverReflectsIso | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalEvaluationCover | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalOrdinaryCohomologyTensor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalProjectionComparisonEquations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalProjectionTensorCompatibility | R2 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalPullSingleComputation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalPurityCoefficientModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalPurityCompactLattices | B2 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalPurityCompactScalarInvertible | B3 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalPurityComparisonDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | A2 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalPurityScalarLocalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalPuritySourceLocalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationFiniteConeModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationHomTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalReturnBlockPower | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalScalarBalancedLocalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalScalarCompletionUnitSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalScalarMixedUnitCancellation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | N4 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalStratumPullbackData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalStratumPullbackModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalTwistedPullbackCompositor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalizationOrientedExchangeSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RawChartScalarCounitPasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RealWeights | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ReconstructedBrownMateLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ReconstructedPairRefinementData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementCommon | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementSingleDegree | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ReconstructedRefinementTraceTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ReductionSiteCoefficientPasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RefinementFiniteOriginEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RelativeKummerSiteNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RelativeKunnethClosedFibre | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RelativeKunnethConstructions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RelativeProductCoefficientFactorSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RelativeProductFactorSquaresCore | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RelativeProductFactors | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RelativeProductProperCompatibilityCore | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ResidueCompatiblePullbackFrobenius | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RestrictedAffineDiagonalDncTrace | E5 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RestrictedAffineDiagonalSectionTrace | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RestrictedAffineDiagonalTraceBaseChange | E6 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RetaggingCoefficientTowerTransfer | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.RetaggingCoordinateOrientations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SbcDatumExchangeComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarFibreCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarFibreComponentData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarFibreComponents | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarFibreNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarHomPresentationEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarLimitConstraintShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarLimitTensorComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarLimitTensorRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarPullTensorCoefficientCoherence | E7 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarReductionTowerBalancing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarRefinementOriginsE | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarRefinementOriginsF | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarSourceCounitUniversal | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ScalarTargetCounitUniversal | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SectionDncIntegrationSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SectionEtaleOpenCancellation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SectionsRationalModelComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SemilinearCommonOrdinaryCubes | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SemilinearCommonRefinementCubes | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SemilinearCommonSupportCubes | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SemilinearExchangeDescentData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SemilinearExchangeReindexing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SemilinearExchangeReindexingData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SemilinearGermIterationDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SemilinearRationalOrdinaryCubes | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SemilinearRationalRefinementCubes | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SemilinearRationalSupportCubes | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfAdicCommonStageDescentEquivalence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfBcCompletedMateDomain | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfCompletedExchangeTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfExactLocalizationTriangle | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfFieldMateDomain | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfIntegralClosedKernelRoos | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfIntegralKernelRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfIntegralLocalizationConstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfIntegralOpenKernelCompactSupport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfNormalizedCommonStageDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalClosedComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfNormalizedRationalWeilSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfNormalizedRecollementScalarCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfNormalizedRecollementTriangles | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageBaseChangeDomainRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageCommonStageTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageIntegralRecollementNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageIntegralRecollementSource | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageIntegralSupportTowerNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationBoundaryData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationBoundaryDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageLocalizationRationalTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPackageQbarAdjunctionMapDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfPositiveFiniteLocalizationConstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationCommonStage | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationExactDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationFiniteCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfQbarLocalizationFiniteData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfRationalLocalizationOrthogonality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfRecollementReductionBoundary | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SfRecollementRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ShiftedCoefficientLinesInvertible | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ShriekNormalizedTransitionComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorMixedSupportCupProduct | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothExceptionalTensorPasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothOperationCoefficientModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothOperationDescentSpecification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothOrientationPuritySquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothOrientationStageExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothOrientationTransportSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | C3 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCompositionFactors | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateChartModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateFoundations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateProjectionModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateRightComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityCoordinateTensorComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityFieldExtension | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitPredicates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsDomain | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBoundsOperations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartAdmissibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerChartData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompactBounds | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGamma | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGammaData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerGluingData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerOpenHomComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Data | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReductionTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SourceSectionAutomorphismModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SourceSectionIdentityModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SourceSectionRestrictionModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SourceSectionStalkConeComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SourceSectionStalkConeData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SpecifiedIntegralUnitOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictDirectImageMixedUnit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictDirectImageMixedUnitData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictMixedFiniteEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictMixedScalarSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictMixedSystemModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictProperCompositionRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictQuotientStalkReindexing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictReductionCompactSupportNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictRefinementRestrictionSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictRefinementSeedRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictScalarFiniteEvaluationTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictScalarMateEvaluationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictScalarMateFiniteEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictScalarMateShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.StrictScalarOpenUnit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SupportedCartierDerivedPullback | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SupportedProjectiveChernComparison | H6 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemCompactSupportRestrictionCocycle | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemCompositorRefinementSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | A3 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemProjectionChangeCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemProjectionTriangleCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemPullbackCompositorEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemScalarBasisDistributivity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemScalarRefinementRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemScalarTensorConstituents | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationCoreExistence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.SystemTensorSemilinearRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TensorExchangeCtfDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TensorHeartSpecialization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TensorHomExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TensorMapPresentationIndependent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TensorMateBaseChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TensorMateInvertibleInput | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TensorTransposeFiniteEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TensorTransposeTowerNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerAdjointCompositorRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerCompositorFiniteEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerGeometricPurityMate | P4 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerIntrinsicShriekTransition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerNormalizationPreservation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerOrientationEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1CoefficientCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1ComparisonsWithLine | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1CtfData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1DiagonalProjectionFactor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1DiagonalTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1EtaleOriginComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1FiniteAdjunctionAssembly | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1FirstTraceReordering | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1FixedTotalTensor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1FormulaLevelComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1GeometricCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1KernelFiniteComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1KernelScalarData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1KernelScalarNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1KernelSplittingBaseChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1LevelCtfModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1LevelWords | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1OrdinaryPushCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1ProjectionLevelComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1ProjectionTraceIdentification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1ProjectiveCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1ProperCtf | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1PushCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1SecondTraceReordering | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelConstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1SingleLevelTriangles | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1TensorChainCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1TensorCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1TensorOrdinaryCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1TriangleFactorization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1TriangleWords | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1UniformCtfDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerP1UniformPresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerPurityAdjointTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerPurityRealizedTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerTensorAdjointDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerTensorTransposeWords | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerTraceCanonicalIntegral | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerTraceNormalizedPresentations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerTraceOrientationUniqueness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerTraceScalarCounit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TowerUniformEtaleDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceBoundedQuotientStalkRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceStalkCompositorTowerData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceStalkCompositorTowerRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceStalkTowerDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TraceStrictStalkTowers | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCartier | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCoprojection | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionCore | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionOrdinary | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionProjective | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedCoordinateSectionSign | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackCofinalModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackLineMembership | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackReductionTower | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackTateReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerBounds | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomain | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerDomainDefinitions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.TwistedPullbackTowerOrigins | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.UniformTowerTensorClosure | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VaryingDimensionDualizingInverse | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleFrameOrientationRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThom | NB | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationChartTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | Q4 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorIntegrationUnitTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorModelChartDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VectorZeroSectionIntegrationBaseChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VerdierCompositionMateNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VerdierHomChainCompositionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VerdierIdentityProjection | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VerdierPairingThreeTransposes | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilBaseChangeSemilinearPasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchangeData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilChosenExchangeConstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilChosenTransposeNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilCompactStructureTensorComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilGenericLissity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilGeometricFiberProperties | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilIndOpenRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilIndOpenRepresentability | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilIndProperHigherRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilIndProperHigherRepresentability | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilIndProperOpenHigher | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilPullbackFibreReturn | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WfTateTwist | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionCohomology | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionPunctualSpectrum | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlCanonicalImmersionStalkConjugacy | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlFrameworkQuotientAugmentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlImmersionFilteredReductionTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlImmersionPullbackWeightPreservation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlImmersionRestrictionAssembly | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlOpenCompactSupportRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlOpenExtensionAssembly | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlOpenExtensionTExact | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlOpenWeilUnitEmptyFibre | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlSfPbcNormalizedHeartModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlWeilHeartLocalizationExact | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlWeilPullCompositorEquivariance | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.DncCoefficientTransportData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingExponent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRingTensorFormula | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteSmoothDualizingScalar | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | R2 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineChartFormulas | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineFormulaData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineIntegrationRegrouping | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineNormalizedInputs | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.NestedAffineOrientationCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.OpenScalarInverseTransposeFactorization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.Reduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptionalChart | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptionalConservativity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptionalObjects | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptionalRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionOrientation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.SectionScalarBaseChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SecSmoothPurity.SupportedScalarTorInterval | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.AffineDualizingCoefficient | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientExactClopenData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientOrdinaryClopenLocalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenCalculus | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientSystemBetaLocalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientSystemClopenLocalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CanonicalOpenReductionIsIso | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CanonicalReductionPullComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CartesianCompactSupportCompositor | F5 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefDualizingSiteMates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefFinitePairingEvaluationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefPairingCompactificationModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefPairingFiniteNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefPairingFrameNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefPairingHomRepresentativeComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefPairingSystemDinaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierCore | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierDualizing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierExceptional | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdierInternalHom | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefScalarReductionExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefSystemProjectionEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairingData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefWeilExceptionalCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefWeilLeftExchangeCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefWeilNormalizedDuality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientProjectionPointData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientUnitFiniteTor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientUnitNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedOpenCartesianIdentity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeDomains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangePaths | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedProjectionExchangeSystem | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedShriekCompositionLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedSystemPullbackPreservation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorShiftAddOnGood | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedTensorSlotShiftLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ConstantOrdinaryCompactificationComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ConstructibleReductionGood | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.DualizingSupportEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ExceptionalIntegralReconstruction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemDuality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransitionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdierData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteCounitRestrictionSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizingAffineRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizingCoefficientNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizingData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizingScalarRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalDomain | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalQuotientCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptionalQuotientIso | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicBidualComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBiduality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteIntrinsicVerdierBounds | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunctionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentIsIso | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingEtaleDescentTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteOpenCartesianCalculus | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteReductionCompletionUnit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteTorOrdinaryPullComplete | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteTorOrdinaryTensorComplete | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteVerdierCoefficientDiagrams | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteVerdierProEtaleLeftTor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusAffineEqualizerPresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyCoefficientCocycle | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyComparisonFactors | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyRationalCocycle | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyRealizationTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFiniteExchangeInverse | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IndependentExpressionReductionShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IndependentExpressionShiftNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicRealizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCanonicalAmbientModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationOrdinaryScalarAction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationRealizationData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralComparisonRecursionLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransportComplete | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralConstantCompleteTransportHom | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingFiniteBounds | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingMappingLimit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizingRoosModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalLimitConstructible | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionCoefficientSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralNormalizedRefinementPasting | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralOpenMateNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralProperTowerTransition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationAssemblyData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralReductionPullbackModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSupportRealizationComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSupportTowerNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCompositorAssociativity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemDualityCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorLeftShiftUnique | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorRightShiftExt | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorRightShiftUnique | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorShiftProperties | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierReductionPairing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdierSignedCalculus | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.KappaCoefficientCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.KappaGeometricComparisons | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.KappaMixedCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.KunnethFirstOpenSubstitution | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.KunnethSecondOpenSubstitution | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.NormalizedRingCompactScalarCocycle | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeReductionSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeSquareData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCoefficient | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateCompletion | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateDescent | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateFinite | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateIntegral | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenDvrRingedIdentification | F9 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherenceData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorExchangeRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorOpenRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorProjectionRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenInterchangeReductionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenNormalizedProductCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionCompletedSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionOrdinaryRoos | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRestrictionNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenReconstructionEffectivity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenReductionMateLocalization | G5 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenSupportStepBounds | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenTensorAugmentationLimitSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientCochains | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientGeometry | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OpenTensorReductionSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OrdinaryAmbientProperOpenLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OrdinaryOpenReductionMate | G7 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.OrdinaryProperOpenInvertibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.PrimitiveCompletionEffectivity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.PrimitiveQuotientAugmentations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ProductCompactificationIdentity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ProductNormalizationRealizationTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ProductSystemUniformRealizationDomain | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionRefinementDescent | U1 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ProjectionSystemCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ProperOpenLambdaReductionSquare | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ProperSupportStepBounds | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.PublishedSystemTensorComposition | U2 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.PullQuotientAugmentationOnGood | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarPreparation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarSupportCompatibility | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalDualizingIdentification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalExceptionalIdentifications | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalHomIdentifications | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalOperationsData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierDatum | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierExtension | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdierUnit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RealizationTreeShiftTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionCounit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionLocalTensor | U4 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionProperComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.RefinementProjectionWords | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisComparisonNormalForm | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SemilinearOpenExternalCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SemilinearOrdinaryCompactificationComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ShortWordCompletionIsomorphism | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ShortWordIntegralDomain | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.StructuralReductionWordSubstitution | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenLambdaExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenProjectionShift | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemProperOpenSupport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemPullbackCompositorIdentification | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemPushCompositionLaws | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemPushIdentityPullUnit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemTensorLeftShiftUnique | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemTensorRightShiftUnique | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftCoherence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.SystemTotalEnrichedTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.TensorCompletionChainUniqueness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.TensorCompletionModelExistence | S4 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.TensorExchangeCoherentConclusions | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.TensorExchangeNormalizedModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.TensorExchangePresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.TensorHomTranspositionData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.TensorQuotientAugmentationOnGood | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.ThreeCellCompositor | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionCompositorContraction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionSystemNormalForm | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.VerdierExchangeData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryBinaryProductTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryProductTransposeData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryTripleLeftComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryTripleProductTranspose | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.SmoothPurity.OrdinaryTripleRightComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.TraceFormula.CompactDirectPowerTransportNormalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.TraceFormula.FrobeniusCompactPowerExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.TraceFormula.FrobeniusProperPowerExchange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.TraceFormula.LocalNormalizationStrictRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.TraceFormula.PointConeLiftsChainNaturality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportBrownConstructibility | H7 | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalForgetfulData | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalLeftModels | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalPointUnit | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeExceptionalStructuralTransport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.OrdinaryClosedPresentation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.WeilSheaf.StructuralOmegaHomPairs | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.Statement | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | C4 | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed in shared snapshot | Identical declarations and public import closure through re-export; no adaptation. |

The direct importers are checked against the delivered module before delivery.
There are no forced adaptations. Transitive users retain the same declarations and
public import closure; no mathematical interpretation or target statement changes.

## Status

landed 20261026T235932-L-1471754 2026-10-26 (merge of deliver/R4/Sheaf.Paper.FiniteCompactSupportScalarTransport)
