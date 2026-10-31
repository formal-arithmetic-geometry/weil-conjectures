/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicSmoothDualizingIntegralDetection
public import WeilConjectures.AlgebraicGeometry.PuritySourceTransports
public import WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientSmoothPurity
public import WeilConjectures.AlgebraicGeometry.SmoothTrace
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
import WeilConjectures.SixFunctors.FiniteTorOrdinaryPullComplete
import WeilConjectures.AlgebraicGeometry.IntegralPullbackAugmentationAmbient
import WeilConjectures.AlgebraicGeometry.QcqsCompletionUnitCriterion

/-! # Finite trace and strict pullback setup for canonical smooth purity

The finite unit comparisons and finite integration retain their original maps.
The strict pullback augmentation is invertible on the finite-Tor domain.
(blueprint: def-pur-canonical-finite-trace-setup).
-/

set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Endofunctor MonoidalCategory
namespace WeilConjectures

namespace RationalSmoothPurityCanonical

attribute [local instance 3000] instCategoryDerivedCategory ScalarLocalization.category

attribute [local instance 0] ConstructibleExceptionalCoefficients.category

private theorem isIso_map_comp_of_isIso_maps
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A B C' : C} (f : A ⟶ B) (g : B ⟶ C')
    (hf : IsIso (F.map f)) (hg : IsIso (F.map g)) : IsIso (F.map (f ≫ g)) := by
  rw [F.map_comp]
  exact IsIso.comp_isIso' hf hg

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted
  PurCompactSupport.image sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar
  IntegralOnSlice.duality ordinaryModel
  integralDerivedPullback integralCompletedTensor sfRationalScalarExtension
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  rationalDerivedTensor rationalDerivedPullback rationalSource
  Functor.mapIso Iso.trans Iso.prod Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.leftAdjoint
  IntegralOnSlice.completion
  IntegralOnSlice.completionUnit IntegralOnSlice.completionComparison IntegralOnSlice.roosUnit
  IntegralAmbient.pull IntegralAmbient.pullTowerIso IntegralAmbient.pullOperationUnit

private theorem completionUnit_onGood (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) (M : (IntegralOnSlice.Good l E T none).FullSubcategory) :
    (IntegralOnSlice.completionUnit l E T none).app (DerivedCategory.Q.obj M.obj) ≫
        (IntegralOnSlice.completionComparison l E T none).hom.app M =
      DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E T none M.obj) := by
  unfold IntegralOnSlice.completionUnit
  exact Classical.choose_spec (ExistsUnique.exists
    (IntegralOnSlice.completionUnit_existsUnique l E T none)) M

/-- Ordinary pullback preserves completeness on the constructible finite-Tor domain.
Consequently the already specified strict pullback augmentation is invertible.
The smooth-purity application is its special case over the given coefficient field.
Source: rational purity proof, integral pullback comparison
(blueprint: def-pur-canonical-finite-trace-setup).
Proof: finiteTorOrdinaryPullComplete makes ordinary ringed pullback complete.
Use integralPullbackAugmentation_ambient to identify its good complex model and
its actual strict augmentation. The canonical completion-unit criterion makes
that unit invertible. Its normalization identifies it with the localized Roos
unit; compose with the specified tower isomorphism and the ambient comparison.
This argument also applies to identity maps, empty schemes, and zero complexes. -/
theorem smoothPullAugmentation_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (C : CochainComplex (integralTowerModules l E Y) ℤ)
    (hC : integralOperationsGoodComplex l E Y C)
    (hK : finiteTorConstructibleIntegral l E Y (DerivedCategory.Q.obj C)) :
    IsIso (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation l E f).app C)) := by
  let : (show integralTowerModules l E Y ⥤ integralTowerModules l E X from
      FrobeniusCoefficientTwists.modulePull l E f).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (show integralTowerModules l E Y ⥤ integralTowerModules l E X from
        FrobeniusCoefficientTwists.modulePull l E f)
      (proEtaleRingModulePullback_additive f
        ((PurCompactSupport.completed l E).ring Y)
        ((PurCompactSupport.completed l E).ring X)
        ((PurCompactSupport.completed l E).pull f))
  let : (IntegralAmbient.pull l E f).PreservesZeroMorphisms :=
    @Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (IntegralAmbient.pull l E f) (IntegralAmbient.pull_additive l E f)
  obtain ⟨b, hb⟩ := integralPullbackAugmentation_ambient l E f
  let M := (IntegralAmbient.pullComplex l E f).obj C
  have hM : IntegralOnSlice.Good l E X none M :=
    IntegralAmbient.pull_good l E f C hC
  let e : DerivedCategory.Q.obj M ≅
      (IntegralSystemRealization.ringedPull l E f).obj (DerivedCategory.Q.obj C) :=
    (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex b (.up ℤ)).app C)).symm ≪≫
      ((FrobeniusCoefficientTwists.modulePull l E f).mapDerivedCategoryFactors.app C).symm
  have hc := GeneratorReduction.finiteTorOrdinaryPullComplete l E f
    inferInstance inferInstance inferInstance (DerivedCategory.Q.obj C) (Or.inl hK)
  let MG : (IntegralOnSlice.Good l E X none).FullSubcategory := ⟨M, hM⟩
  have hu := (IntegralOnSlice.canonicalCompletionUnitCriterion l E X _).mpr hc
  have huM : IsIso ((IntegralOnSlice.completionUnit l E X none).app
      (DerivedCategory.Q.obj M)) :=
    (NatTrans.isIso_app_iff_of_iso (IntegralOnSlice.completionUnit l E X none) e).mpr hu
  have hn : (IntegralOnSlice.completionUnit l E X none).app
      (DerivedCategory.Q.obj M) ≫
        (IntegralOnSlice.completionComparison l E X none).hom.app MG =
      DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none M) := by
    exact completionUnit_onGood l E X MG
  have hr : IsIso (DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E X none M)) :=
    hn ▸ IsIso.comp_isIso' huM
      (NatIso.hom_app_isIso (IntegralOnSlice.completionComparison l E X none) MG)
  have hmap : IsIso (DerivedCategory.Q.map
      (integralOperationsRoosFunctor.map ((IntegralAmbient.pullTowerIso l E f).hom.app C))) :=
    by
      simpa only [Functor.mapIso_hom, Iso.app_hom] using
        (DerivedCategory.Q.mapIso (integralOperationsRoosFunctor.mapIso
          ((IntegralAmbient.pullTowerIso l E f).app C))).isIso_hom
  have ha : IsIso (DerivedCategory.Q.map (IntegralAmbient.pullOperationUnit l E f C)) := by
    unfold IntegralAmbient.pullOperationUnit
    set_option backward.isDefEq.respectTransparency.types true in
    exact isIso_map_comp_of_isIso_maps
      (DerivedCategory.Q (C := integralTowerModules l E X))
      (IntegralOnSlice.roosUnit l E X none M)
      (integralOperationsRoosFunctor.map ((IntegralAmbient.pullTowerIso l E f).hom.app C))
      hr hmap
  have hi : IsIso (DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app C)) :=
    by
      simpa only [Functor.mapIso_hom, Iso.app_hom] using
        (DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex b (.up ℤ)).app C)).isIso_hom
  rw [hb C]
  set_option backward.isDefEq.respectTransparency.types true in
  exact isIso_map_comp_of_isIso_maps
    (DerivedCategory.Q (C := integralTowerModules l E X))
    ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app C)
    (IntegralAmbient.pullOperationUnit l E f C) hi ha

/-- Comparison pullback carries the ordinary constant coefficient to the tensor unit.
Source: rational purity proof Step 1, finite unit comparison
(blueprint: def-pur-canonical-finite-trace-setup). -/
@[irreducible]
def finiteComparisonUnit (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj
      (Etale.ordinaryFiniteUnit A X) ≅
        𝟙_ (DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.mapIso
      (PurityFiniteSetting.smoothPurityUnitIso A X) ≪≫
    ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso A X

/-- Tensor left unitor transported through a specified presentation of the tensor.
Source: rational purity proof Step 1, finite unit comparison
(blueprint: def-pur-canonical-finite-trace-setup). -/
def tensorUnitFromPresentation {C : Type v} [Category.{u} C] [MonoidalCategory C]
    (T : C ⥤ C ⥤ C) (h : T = curriedTensor C) (M : C) :
    ((T.obj (𝟙_ C)).obj M) ≅ M :=
  eqToIso (congrArg (fun F ↦ (F.obj (𝟙_ C)).obj M) h) ≪≫ (λ_ M)

/-- Transport the tensor left unitor through a tensor presentation and unit isomorphism.
Source: rational purity proof Step 1, tensor-unit constraint
(blueprint: def-pur-canonical-finite-trace-setup). -/
def tensorLeftUnitorFromPresentation {C : Type v} [Category.{u} C]
    (M : MonoidalCategory C) (T : C × C ⥤ C)
    (h : T = @MonoidalCategory.tensor C _ M) (A K : C)
    (e : A ≅ M.tensorUnit) : T.obj (A, K) ≅ K :=
  eqToIso (congrArg (fun F ↦ F.obj (A, K)) h) ≪≫
    (@MonoidalCategory.tensor C _ M).mapIso (Iso.prod e (Iso.refl K)) ≪≫
    @MonoidalCategory.leftUnitor C _ M.toMonoidalCategoryStruct K

/-- The finite tensor left unitor in the published tensor presentation.
Source: rational purity proof Step 1, finite unit comparison
(blueprint: def-pur-canonical-finite-trace-setup). -/
@[irreducible]
def finiteTensorUnit (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))) :
    ((PurityFiniteSetting.smoothPurityTensor A X).obj (𝟙_ _)).obj M ≅ M :=
  tensorUnitFromPresentation _
    (PurityFiniteSetting.smoothPurityTensorPresentation (ModuleCat.{u + 1} A) X) M

/-- Pullback of the finite coefficient unit, with the constant-section normalization.
All factors are the existing site comparison, ordinary constant-unit pullback,
and single-complex monoidal-unit comparison.
Source: rational purity proof Step 1, unit-object adic reconstruction
(blueprint: def-pur-canonical-finite-trace-setup). -/
@[irreducible]
def finitePullUnit (Q : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Q.smoothPurityPullback f).obj
      ((sfIntrinsicDerivedEquivalence Y Q.Ring).inverse.obj (Q.coefficientUnit Y)) ≅
        𝟙_ (DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Q.Coefficient))) :=
  Q.smoothPurityPullbackComparison f _ (Etale.ordinaryFiniteUnit Q.Coefficient Y)
    ((sfIntrinsicDerivedEquivalence Y Q.Ring).unitIso.app
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
        Y).mapDerivedCategory.obj (Etale.ordinaryFiniteUnit Q.Coefficient Y))) ≪≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
      X).mapDerivedCategory.mapIso (Etale.ordinaryFiniteUnitPullback Q.Coefficient f) ≪≫
    finiteComparisonUnit Q.Coefficient X

/-- At the unit the finite smooth-purity source is the shifted Tate line, through
shift reassociation, pullback of the constant unit, and the tensor left unitor.
Source: rational purity proof Step 1, canonical finite source identifications
(blueprint: def-pur-canonical-finite-trace-setup). -/
@[irreducible]
def finiteUnitSource (Q : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) :
    (sfIntrinsicDerivedEquivalence X Q.Ring).functor.obj
      ((((PurityFiniteSetting.smoothPurityTensor Q.Coefficient X).obj
        ((Q.smoothPurityPullback f).obj
          ((sfIntrinsicDerivedEquivalence Y Q.Ring).inverse.obj (Q.coefficientUnit Y)))).obj
            ((Q.diagonalTwist X d)⟦-(2*(d : ℤ))⟧))⟦2*(d : ℤ)⟧) ≅
      (sfIntrinsicDerivedEquivalence X Q.Ring).functor.obj (Q.diagonalTwist X d) :=
  (sfIntrinsicDerivedEquivalence X Q.Ring).functor.mapIso
    (Q.smoothPurityReassociation X d
      ((Q.smoothPurityPullback f).obj
        ((sfIntrinsicDerivedEquivalence Y Q.Ring).inverse.obj (Q.coefficientUnit Y))) ≪≫
      ((PurityFiniteSetting.smoothPurityTensor Q.Coefficient X).mapIso
        (finitePullUnit Q f)).app (Q.diagonalTwist X d) ≪≫
      finiteTensorUnit Q.Coefficient X (Q.diagonalTwist X d))

section RelativeOrientation
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The shifted completed coefficient line in the existing finite-Tor category.
Source: rational purity proof, integral orientation
(blueprint: def-pur-canonical-finite-trace-setup). -/
abbrev twist (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  AdicSmoothDualizing.integralTwist P T aT d

/-- The finite ordinary dualizing object is bounded below by smooth purity.
Source: rational purity proof Step 1, finite trace
(blueprint: def-pur-canonical-finite-trace-setup).
Proof: the ordinary comparison in existsUnique_diagonalDualizingObject identifies
this object with the finite Tate line shifted by 2d. A single sheaf has cohomology
only in degree zero; its shift is bounded below. Transport that bound across the iso. -/
theorem finiteDualizingPlus (n d : ℕ) [SmoothOfRelativeDimension d f] :
    (fun [hc : HasCompactification f] ↦ DerivedCategory.TStructure.t.plus
      ((AdicSmoothDualizing.levelSetting P n).diagonalOrdinaryDualizing f))
        (hc := c.hasCompactification) := by
  let : HasCompactification f := c.hasCompactification
  let : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of P.field.k))
  exact Etale.plus_rightDerivedUpperShriek_obj
    (AdicSmoothDualizing.levelSetting P n).Coefficient f _
    ((AdicSmoothDualizing.levelSetting P n).diagonalUnitPlus Y)

set_option backward.isDefEq.respectTransparency.types false in

/-- The normalized finite integration for this relative smooth morphism.
The finite diagonal orientation and the exceptional counit are the published maps.
Source: rational purity proof Step 1 and its finite smooth normalization
(blueprint: def-pur-canonical-finite-trace-setup). -/
@[irreducible]
def finiteIntegration (n d : ℕ) [SmoothOfRelativeDimension d f] :
    (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n)) c).obj
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
          ((AdicSmoothDualizing.levelSetting P n).diagonalTwist X d)) ⟶
      (AdicSmoothDualizing.levelSetting P n).coefficientUnit Y := by
  let hfSep : IsSeparated f := inferInstance
  let hfType : LocallyOfFiniteType f := inferInstance
  let hfQc : QuasiCompact f := inferInstance
  let hfSmooth : SmoothOfRelativeDimension d f := inferInstance
  let hYType : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) := inferInstance
  let hYQc : QuasiCompact (Y ↘ Spec (.of P.field.k)) := inferInstance
  letI : HasCompactification f := c.hasCompactification
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek
    (AdicSmoothDualizing.levelSetting P n).Coefficient f
  refine (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n c).hom.app _ ≫ ?_
  refine (ProEtale.sfIntrinsicCompactSupportComparison
      (AdicSmoothDualizing.levelSetting P n).Ring c).hom.app _ ≫ ?_
  exact (sfIntrinsicDerivedEquivalence Y (AdicSmoothDualizing.levelSetting P n).Ring).functor.map
      ((ProEtale.sfFixedCompactSupport
        (AdicSmoothDualizing.levelSetting P n).Ring c).map
        ((@PurityFiniteSetting.diagonalDualizingObject
          (AdicSmoothDualizing.levelSetting P n) X Y d f
          hfSep hfType
          hfQc hfSmooth
          (Y ↘ Spec (.of P.field.k))
          hYType
          hYQc).inv ≫
          ((AdicSmoothDualizing.levelSetting P n).diagonalDualizingComparison f).hom) ≫
        (ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient) c).hom.app
            ⟨_, finiteDualizingPlus P f c n d⟩ ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
          Y).mapDerivedCategory.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso
              (AdicSmoothDualizing.levelSetting P n).Coefficient c
              (HasCompactification.compactification f)).hom.app
                ⟨_, finiteDualizingPlus P f c n d⟩ ≫
              (Etale.rightDerivedUpperShriekAdjunction
                (AdicSmoothDualizing.levelSetting P n).Coefficient
                f).counit.app _))

/-- The published compact-support functor at a reindexed level, with the original
over-field structures supplied explicitly. Source: rational purity proof Step 1
(blueprint: def-pur-canonical-finite-trace-setup). -/
def levelSmoothCompactSupport (n : ℕ) :=
  @PurityFiniteSetting.smoothCompactSupport (AdicSmoothDualizing.levelSetting P n) X Y f
    (inferInstanceAs (X.Over (Spec (.of P.field.k))))
    (inferInstanceAs (Y.Over (Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) ))
    (inferInstanceAs (QuasiCompact (X ↘ Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k))))
    (inferInstanceAs (f.IsOver (Spec (.of P.field.k))))
    (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
    (inferInstanceAs (QuasiCompact f))

/-- The recorded finite smooth-purity map with the inherited over-field instances.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-finite-trace-setup). -/
def levelSmoothPurityMap (n d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y (AdicSmoothDualizing.levelSetting P n).Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) Y K) :=
  @PurityFiniteSetting.smoothPurityMap (AdicSmoothDualizing.levelSetting P n) X Y
    (inferInstanceAs (X.Over (Spec (.of P.field.k))))
    (inferInstanceAs (Y.Over (Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (X ↘ Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k)))) f
    (inferInstanceAs (f.IsOver (Spec (.of P.field.k))))
    (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
    (inferInstanceAs (QuasiCompact f)) d (inferInstanceAs (SmoothOfRelativeDimension d f)) K hK

/-- The recorded exceptional counit with the inherited over-field instances.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-finite-trace-setup). -/
def levelSmoothExceptionalCounit (n : ℕ)
    (K : Scheme.proEtaleDerivedCategory Y (AdicSmoothDualizing.levelSetting P n).Ring) :=
  @PurityFiniteSetting.smoothExceptionalCounit (AdicSmoothDualizing.levelSetting P n) X Y
    (inferInstanceAs (X.Over (Spec (.of P.field.k))))
    (inferInstanceAs (Y.Over (Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (X ↘ Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k)))) f
    (inferInstanceAs (f.IsOver (Spec (.of P.field.k))))
    (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
    (inferInstanceAs (QuasiCompact f)) K

end RelativeOrientation

set_option warn.classDefReducibility false in

/-- The ordinary monoidal structure with its integral derived category explicit.
Source: rational purity proof Step 1, tensor-unit constraint
(blueprint: def-pur-canonical-finite-trace-setup). -/
def ordinaryMonoidal (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) : MonoidalCategory (DerivedCategory (integralTowerModules l E T)) :=
  (@RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
    _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
    (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
    (IntegralOnSlice.duality.{u, u} l E T none)).monoidal

attribute [local irreducible] ordinaryMonoidal

private theorem ordinaryMonoidal_tensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T : Scheme.{u}) :
    (ordinaryModel l E T).tensor = @MonoidalCategory.tensor _ _ (ordinaryMonoidal l E T) := by
  unfold ordinaryModel ordinaryMonoidal
  exact (ordinaryModel_existsUnique l E T).exists.choose_spec.1


end RationalSmoothPurityCanonical

end WeilConjectures
