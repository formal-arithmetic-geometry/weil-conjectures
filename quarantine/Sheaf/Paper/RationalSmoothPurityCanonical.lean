/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.AdicSmoothDualizingComplexes
public import Sheaf.Paper.PuritySourceTransports
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import Sheaf.Paper.FiniteCoefficientSmoothPurity
public import Sheaf.Paper.SmoothTrace
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence
import Sheaf.Paper.IntegralResidueTor
import Sheaf.SixFunctors.FiniteTorOrdinaryPullComplete
import Sheaf.Paper.IntegralPullbackAugmentationAmbient
import Sheaf.Paper.QcqsCompletionUnitCriterion

/-! # Canonical rational purity in the intrinsic constructible presentation

Source: main-20261015, prop-weil-operations.proof.md, sentences 3--4;
sk-prop-sp-rational, Steps 1--2, and thm-pur-adic-reconstruction
(blueprint: def-pur-canonical-rational-purity-realization).

The family is the localized trace transpose of the adically reconstructed unit
orientation. Its source transports retain the actual shift comparisons.
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

attribute [local instance 0] ConstructibleExceptionalCoefficients.category

/-- The inherited shift retains the specified ambient object. -/
private theorem fullSubcategory_shift_obj {C : Type*} [Category C]
    (P0 : ObjectProperty C) (A : Type*) [AddMonoid A] [HasShift C A]
    [P0.IsStableUnderShift A] (K : P0.FullSubcategory) (a : A) :
    (K⟦a⟧).obj = K.obj⟦a⟧ := by
  unfold shiftFunctor ObjectProperty.hasShift
  rfl

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
(blueprint: def-pur-canonical-rational-purity-realization).
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
(blueprint: def-pur-canonical-rational-purity-realization). -/
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
(blueprint: def-pur-canonical-rational-purity-realization). -/
def tensorUnitFromPresentation {C : Type v} [Category.{u} C] [MonoidalCategory C]
    (T : C ⥤ C ⥤ C) (h : T = curriedTensor C) (M : C) :
    ((T.obj (𝟙_ C)).obj M) ≅ M :=
  eqToIso (congrArg (fun F ↦ (F.obj (𝟙_ C)).obj M) h) ≪≫ (λ_ M)

/-- Transport the tensor left unitor through a tensor presentation and unit isomorphism.
Source: rational purity proof Step 1, tensor-unit constraint
(blueprint: def-pur-canonical-rational-purity-realization). -/
def tensorLeftUnitorFromPresentation {C : Type v} [Category.{u} C]
    (M : MonoidalCategory C) (T : C × C ⥤ C)
    (h : T = @MonoidalCategory.tensor C _ M) (A K : C)
    (e : A ≅ M.tensorUnit) : T.obj (A, K) ≅ K :=
  eqToIso (congrArg (fun F ↦ F.obj (A, K)) h) ≪≫
    (@MonoidalCategory.tensor C _ M).mapIso (Iso.prod e (Iso.refl K)) ≪≫
    @MonoidalCategory.leftUnitor C _ M.toMonoidalCategoryStruct K

/-- The finite tensor left unitor in the published tensor presentation.
Source: rational purity proof Step 1, finite unit comparison
(blueprint: def-pur-canonical-rational-purity-realization). -/
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
(blueprint: def-pur-canonical-rational-purity-realization). -/
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
(blueprint: def-pur-canonical-rational-purity-realization). -/
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
(blueprint: def-pur-canonical-rational-purity-realization). -/
abbrev twist (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (d : ℕ) :=
  AdicSmoothDualizing.integralTwist P T aT d

/-- The finite ordinary dualizing object is bounded below by smooth purity.
Source: rational purity proof Step 1, finite trace
(blueprint: def-pur-canonical-rational-purity-realization).
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
    (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient) f _
    ((AdicSmoothDualizing.levelSetting P n).diagonalUnitPlus Y)

set_option backward.isDefEq.respectTransparency.types false in

/-- The normalized finite integration for this relative smooth morphism.
The finite diagonal orientation and the exceptional counit are the published maps.
Source: rational purity proof Step 1 and its finite smooth normalization
(blueprint: def-pur-canonical-rational-purity-realization). -/
@[irreducible]
def finiteIntegration (n d : ℕ) [SmoothOfRelativeDimension d f] :
    (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n)) c).obj
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
          ((AdicSmoothDualizing.levelSetting P n).diagonalTwist X d)) ⟶
      (AdicSmoothDualizing.levelSetting P n).coefficientUnit Y := by
  letI : HasCompactification f := c.hasCompactification
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek f
    (AdicSmoothDualizing.levelSetting P n).Coefficient
  refine (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n c).hom.app _ ≫ ?_
  refine (ProEtale.sfIntrinsicCompactSupportComparison
      (AdicSmoothDualizing.levelSetting P n).Ring c).hom.app _ ≫ ?_
  exact (sfIntrinsicDerivedEquivalence Y (AdicSmoothDualizing.levelSetting P n).Ring).functor.map
      ((ProEtale.sfFixedCompactSupport
        (AdicSmoothDualizing.levelSetting P n).Ring c).map
        ((@PurityFiniteSetting.diagonalDualizingObject
          (AdicSmoothDualizing.levelSetting P n) X Y d f
          (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
          (inferInstanceAs (QuasiCompact f)) (inferInstanceAs (SmoothOfRelativeDimension d f))
          (Y ↘ Spec (.of P.field.k))
          (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
          (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k))))).inv ≫
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
                (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
                f).counit.app _))

/-- The published compact-support functor at a reindexed level, with the original
over-field structures supplied explicitly. Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
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
(blueprint: def-pur-canonical-rational-purity-realization). -/
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
(blueprint: def-pur-canonical-rational-purity-realization). -/
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

/-- The finite integration used in the integral orientation is the actual transpose
of smoothPurityMap at the coefficient unit. The source comparison is explicitly
finiteUnitSource; the compact-support comparison is the existing open/proper one.
This pins the map, including its shift and unit normalization, rather than merely
asserting that two isomorphic objects have some compatible isomorphism.
Source: rational purity proof Step 1; def-pur-smooth-purity-map; thm-pur-adic-reconstruction
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: expand smoothPurityMap and use its characterization in the ordinary unit
presentation. Reassociation cancels with finiteUnitSource. Pullback of the constant
unit and the tensor left unitor reduce its tensor mate to inverse diagonal orientation.
The comparison adjunction triangles then identify its counit transpose with
finiteIntegration. finiteImageIso preserves the open and proper units separately,
and the ordinary compactification comparison preserves the exceptional counit.
This proves the displayed equality for every positive level, including d=0. -/
theorem finiteIntegration_smoothPurityMap (n d : ℕ) [SmoothOfRelativeDimension d f]
    (hUnit : finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) Y
      ((AdicSmoothDualizing.levelSetting P n).coefficientUnit Y)) :
    (fun [hc : HasCompactification f] ↦
      (levelSmoothCompactSupport P f n).map
        (levelSmoothPurityMap P f n d
          ((AdicSmoothDualizing.levelSetting P n).coefficientUnit Y) hUnit) ≫
        levelSmoothExceptionalCounit P f n
          ((AdicSmoothDualizing.levelSetting P n).coefficientUnit Y) =
      (levelSmoothCompactSupport P f n).map
        (finiteUnitSource (AdicSmoothDualizing.levelSetting P n) f d).hom ≫
        (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n
          (HasCompactification.compactification f)).inv.app _ ≫
        finiteIntegration P f (HasCompactification.compactification f) n d)
      (hc := c.hasCompactification) := by
  sorry

/-- Finite trace normalization, using the actual coefficient comparison and root projection.
Source: rational purity proof, reconstruction of the coefficient-unit orientation
(blueprint: def-pur-canonical-rational-purity-realization). -/
def IsNormalizedTrace (d : ℕ) [SmoothOfRelativeDimension d f]
    (t : (PurCompactSupport.image
        (PurCompactSupport.completed P.coefficients.l P.extension) c).obj
          (twist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
      (twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj) : Prop :=
  ∀ n : ℕ,
    (PurCompactSupport.comparison (PurCompactSupport.reduction P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) c).app
          (twist P X (X ↘ Spec (.of P.field.k)) d).obj ≫
      (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
        (n + 1) (Nat.succ_pos n)) c).map
          (AdicSmoothDualizing.twistReduction P X (X ↘ Spec (.of P.field.k)) n d) ≫
      finiteIntegration P f c n d =
    (pbcDerivedExtend (PurCompactSupport.projection P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n) Y)).map t ≫
        AdicSmoothDualizing.twistReduction P Y (Y ↘ Spec (.of P.field.k)) n 0

variable (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
  P.field P.coefficients.different (f := f))

/-- The specified constructible operation, retaining its actual adjunction.
Source: rational purity proof, exceptional pullback
(blueprint: def-pur-canonical-rational-purity-realization). -/
abbrev operation (s : ConstructibleExceptionalCoefficients.Stage.{u} P.coefficients.l) :=
  S.ring.operation c s

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The coefficient-unit orientation's trace in ordinary compact-support coordinates.
Source: rational purity proof Step 1, trace transpose
(blueprint: def-pur-canonical-rational-purity-realization). -/
def orientationTrace (d : ℕ)
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0)) :
    (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension) c).obj
      (twist P X (X ↘ Spec (.of P.field.k)) d).obj ⟶
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj :=
  (S.ring.left c (ConstructibleExceptionalCoefficients.RingStage.integral
      (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).inv.app
      (twist P X (X ↘ Spec (.of P.field.k)) d) ≫
    (finiteTorConstructibleIntegral P.coefficients.l P.extension Y).ι.map
      ((operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).F.map a.hom ≫
        (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).adjunction.counit.app
          (twist P Y (Y ↘ Spec (.of P.field.k)) 0))

/-- The unit orientation is uniquely fixed by the finite diagonal traces.
This uniqueness is only for a shifted rank-one line, not for arbitrary derived lifts.
Source: rational purity proof Step 1; finite diagonal orientation
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: adic reconstruction of the finite unit-object purity gives the orientation.
Its counit reductions are precisely finiteIntegration by scalar compatibility.
If two orientations have these traces, transpose under the specified adjunction and
use either orientation to identify their quotient with an endomorphism of the shifted
completed line. This is an ordinary degree-zero line endomorphism. Its projections
to every finite quotient vanish, so it vanishes, since completed coefficients are the
inverse limit of those quotients. This proves uniqueness without a phantom-map claim. -/
theorem orientation_existsUnique (d : ℕ) [SmoothOfRelativeDimension d f] :
    ∃! a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
        (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
          (twist P Y (Y ↘ Spec (.of P.field.k)) 0),
      IsNormalizedTrace P f c d (orientationTrace P f c S d a) := by
  sorry

/-- The unique finite-trace-normalized unit orientation.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def orientation (d : ℕ) [SmoothOfRelativeDimension d f] :
    twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0) :=
  (orientation_existsUnique P f c S d).exists.choose

/-- Transport of an adically reconstructed unit orientation is the orientation used
here. The premise is exactly the finite trace condition supplied by reconstruction;
it does not claim uniqueness of coherent lifts on arbitrary complexes.
Source: thm-pur-adic-reconstruction and rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: the reconstruction theorem realizes the normalized finite purity maps. By
finiteIntegration_smoothPurityMap their counit reductions are finiteIntegration.
Thus the transported unit orientation satisfies IsNormalizedTrace. The uniqueness
clause of orientation_existsUnique identifies it with orientation. This uniqueness
uses only endomorphisms of the shifted rank-one line, detected by finite quotients. -/
theorem orientation_eq_adic (d : ℕ) [SmoothOfRelativeDimension d f]
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0))
    (ha : IsNormalizedTrace P f c d (orientationTrace P f c S d a)) :
    orientation P f c S d = a := by
  unfold orientation
  exact (orientation_existsUnique P f c S d).unique
    (orientation_existsUnique P f c S d).exists.choose_spec ha

/-- Smooth completed-to-ordinary pullback on a good finite-Tor representative.
Source: rational purity proof, integral source
(blueprint: def-pur-canonical-rational-purity-realization). -/
@[irreducible]
def smoothPullToOrdinaryOnGood (d : ℕ) [SmoothOfRelativeDimension d f]
    (C : CochainComplex (integralTowerModules P.coefficients.l P.extension Y) ℤ)
    (hC : integralOperationsGoodComplex P.coefficients.l P.extension Y C)
    (hK : finiteTorConstructibleIntegral P.coefficients.l P.extension Y
      (DerivedCategory.Q.obj C)) :
    (integralDerivedPullback P.coefficients.l P.extension f).obj (DerivedCategory.Q.obj C) ≅
      (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
        f).obj (DerivedCategory.Q.obj C) :=
  (integralDerivedPullbackComparison P.coefficients.l P.extension f).app ⟨C,hC⟩ ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map
      ((FrobeniusCoefficientTwists.pullbackAugmentation
        P.coefficients.l P.extension f).app C))
      (smoothPullAugmentation_isIso P.coefficients.l P.extension f C hC hK)).symm ≪≫
    ((FrobeniusCoefficientTwists.modulePull
      P.coefficients.l P.extension f).mapDerivedCategoryFactors.app C).symm

/-- The smooth comparison is fixed on every representative and every presentation map.
Source: rational purity proof, integral source
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: use good K-flat resolutions. The normalized strict augmentation is natural,
so its descent is independent of resolution and of the isomorphism presenting K.
Every K has a resolution, which also proves uniqueness. -/
theorem smoothPullToOrdinary_existsUnique (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    ∃! e : (integralDerivedPullback P.coefficients.l P.extension f).obj K.obj ≅
        (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
          f).obj K.obj,
      ∀ (C : CochainComplex (integralTowerModules P.coefficients.l P.extension Y) ℤ)
        (hC : integralOperationsGoodComplex P.coefficients.l P.extension Y C)
        (hK : finiteTorConstructibleIntegral P.coefficients.l P.extension Y
          (DerivedCategory.Q.obj C)) (a : DerivedCategory.Q.obj C ≅ K.obj),
        e = (integralDerivedPullback P.coefficients.l P.extension f).mapIso a.symm ≪≫
          smoothPullToOrdinaryOnGood P f d C hC hK ≪≫
          (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
            f).mapIso a := by
  sorry

/-- The specified smooth completed-to-ordinary comparison.
Source: rational purity proof, integral source
(blueprint: def-pur-canonical-rational-purity-realization). -/
def smoothPullToOrdinary (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :=
  (smoothPullToOrdinary_existsUnique P f d K).exists.choose

/-- Completed pullback preserves the finite-Tor constructible domain here.
Source: rational purity proof, bounded integral representatives
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: integral pullback preserves the constructible complete category. Its actual
reductions are finite pullbacks of the reductions of K and retain their one Tor
interval. Thus the result has the required complete membership and uniform bounds. -/
theorem pullFiniteTor (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegral P.coefficients.l P.extension X
      ((integralDerivedPullback P.coefficients.l P.extension f).obj K.obj) := by
  classical
  let (x : X) : Invertible (P.coefficients.l : X.residueField x) :=
    (show IsUnit (P.coefficients.l : X.residueField x) by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk X (X ↘ Spec (.of P.field.k)) x).map
          (X.residue x).hom).invertible
  let (y : Y) : Invertible (P.coefficients.l : Y.residueField y) :=
    (show IsUnit (P.coefficients.l : Y.residueField y) by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk Y (Y ↘ Spec (.of P.field.k)) y).map
          (Y.residue y).hom).invertible
  have hY := (integral_residue_tor P.field P.coefficients.l P.coefficients.different
    P.extension Y).2
  have hX := (integral_residue_tor P.field P.coefficients.l P.coefficients.different
    P.extension X).2
  rw [← hX]
  exact ((integralOperations_preserve_constructible P.coefficients.l P.extension f).1
    K.obj (by rw [hY]; exact K.property)).1

/-- The integral twisted pullback, with the even shift on the coefficient line.
This is canonically Lf*K(d)[2d] by the specified tensor symmetry and shift constraints.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: the coefficient line is complete constructible with uniform Tor interval [-2d,-2d].
Pullback of K has its original uniform interval. Completed tensor adds those intervals
and preserves constructibility. This proves finite-Tor membership of the displayed object. -/
theorem integralSource_mem (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegral P.coefficients.l P.extension X
      ((integralCompletedTensor P.coefficients.l P.extension X).obj
        ((twist P X (X ↘ Spec (.of P.field.k)) d).obj,
          (integralDerivedPullback P.coefficients.l P.extension f).obj K.obj)) := by
  classical
  let (x : X) : Invertible (P.coefficients.l : X.residueField x) :=
    (show IsUnit (P.coefficients.l : X.residueField x) by
      simpa only [map_natCast] using
        (P.coefficientPrime_isUnit_stalk X (X ↘ Spec (.of P.field.k)) x).map
          (X.residue x).hom).invertible
  have hX := (integral_residue_tor P.field P.coefficients.l P.coefficients.different
    P.extension X).2
  apply (congrFun hX _).mp
  have hK := (congrFun hX _).mpr (pullFiniteTor P f d K)
  exact ((integralOperations_preserve_constructible P.coefficients.l P.extension (𝟙 X)).2
    X (Or.inl rfl) _ _ (twist P X (X ↘ Spec (.of P.field.k)) d).property.1 hK).1

/-- The integral source in the existing finite-Tor full subcategory.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralSource (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension X :=
  ⟨_,integralSource_mem P f d K⟩

attribute [local irreducible] smoothPullToOrdinary

/-- The canonical source comparison to the ordinary tensor used by projection.
Source: rational purity proof, trace-transpose source
(blueprint: def-pur-canonical-rational-purity-realization). -/
def ordinarySource (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    (integralSource P f d K).obj ≅
      (ordinaryModel P.coefficients.l P.extension X).tensor.obj
        ((twist P X (X ↘ Spec (.of P.field.k)) d).obj,
          (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
            f).obj K.obj) :=
  tensorToOrdinary P.coefficients.l P.extension X
    (twist P X (X ↘ Spec (.of P.field.k)) d)
    ⟨_,pullFiniteTor P f d K⟩ ≪≫
    (ordinaryModel P.coefficients.l P.extension X).tensor.mapIso
      (Iso.prod (Iso.refl _) (smoothPullToOrdinary P f d K))

attribute [local irreducible] ordinarySource

attribute [local semireducible] PurCompactSupport.image in
/-- The actual proper/open projection transformation for the fixed compactification.
Source: rational purity proof, inverse projection in the trace transpose
(blueprint: def-pur-canonical-rational-purity-realization). -/
def projection (d : ℕ) (K : finiteTorConstructibleIntegralCategory
    P.coefficients.l P.extension Y) :
    (ordinaryModel P.coefficients.l P.extension Y).tensor.obj
      (((PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
        c).obj (twist P X (X ↘ Spec (.of P.field.k)) d).obj), K.obj) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
        c).obj ((ordinaryModel P.coefficients.l P.extension X).tensor.obj
          ((twist P X (X ↘ Spec (.of P.field.k)) d).obj,
            (PurCompactSupport.pull (PurCompactSupport.completed P.coefficients.l P.extension)
              f).obj K.obj)) :=
  ((PurCompactSupport.projectionMap
    (PurCompactSupport.completed P.coefficients.l P.extension) c
    (ordinaryModel P.coefficients.l P.extension X)
    (ordinaryModel P.coefficients.l P.extension c.Z)
    (ordinaryModel P.coefficients.l P.extension Y)
    (PurCompactSupport.completedPull_comp P.coefficients.l P.extension c.i c.g)).app
      (twist P X (X ↘ Spec (.of P.field.k)) d).obj).app K.obj

/-- Projection is invertible on the indicated constructible finite-Tor inputs.
The asserted map is the actual counit-first proper/open composite above.
Source: rational purity proof, projection formula
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: finite coefficient projection is invertible for a bounded flat constructible
second input. Ordinary coefficient tensor agrees with completed tensor on this domain.
The normalized strict quotient-tower realization carries the finite projection and its
inverse to the displayed ordinary map and inverse. Proper and open comparisons retain
their original units and counits throughout, so this proves invertibility of this map. -/
theorem projection_isIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    IsIso (projection P f c d K) := by
  sorry

/-- The published ordinary closed structure, with its presentation kept abstract locally.
Source: rational purity proof Step 1, tensor-unit constraint
(blueprint: def-pur-canonical-rational-purity-realization). -/
def ordinaryClosed (T : Scheme.{u}) :=
  @RingedSiteDualityModel.closed.{u + 1, u, u, u + 2}
    _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
    (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
    (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension T none)

attribute [local irreducible] ordinaryClosed

set_option warn.classDefReducibility false in

/-- The ordinary monoidal structure with its integral derived category explicit.
Source: rational purity proof Step 1, tensor-unit constraint
(blueprint: def-pur-canonical-rational-purity-realization). -/
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

/-- The shifted zero-power line is the coefficient unit of the normalized ordinary tensor.
Source: rational purity proof, tensor-unit constraint
(blueprint: def-pur-canonical-rational-purity-realization). -/
def ordinaryCoefficientUnit (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) :
    (twist P T aT 0).obj ≅
      (ordinaryMonoidal P.coefficients.l P.extension T).tensorUnit := by
  unfold ordinaryMonoidal
  exact (shiftFunctorZero _ ℤ).app _ ≪≫
    (@RingedSiteDualityModel.unitIso.{u + 1, u, u, u + 2}
      _ _ _ (IntegralOnSlice.abSheafify.{u, u} T none)
      (IntegralOnSlice.abLocallyBijective.{u, u} T none) _ _
      (IntegralOnSlice.duality.{u, u} P.coefficients.l P.extension T none)).symm

/-- Extract the first conjunct of the property determining a unique object.
Source: the universal property of ordinary tensor presentation
(blueprint: def-pur-canonical-rational-purity-realization). -/
theorem uniqueChosen_left {A : Sort v} (p q : A → Prop) (h : ∃! x, p x ∧ q x) :
    p h.exists.choose := h.exists.choose_spec.1

/-- Equality of the published ordinary tensor and its closed monoidal presentation.
Source: rational purity proof Step 1, tensor-unit constraint
(blueprint: def-pur-canonical-rational-purity-realization). -/
theorem ordinaryTensor_eq (T : Scheme.{u}) :
    (ordinaryModel P.coefficients.l P.extension T).tensor =
      @MonoidalCategory.tensor _ _ (ordinaryMonoidal P.coefficients.l P.extension T) := by
  exact ordinaryMonoidal_tensor P.coefficients.l P.extension T

attribute [local irreducible] ordinaryCoefficientUnit CoefficientClosedStructure.tensor

/-- The ordinary tensor's coefficient left unitor, retaining its scalar normalization.
Source: rational purity proof, trace transpose
(blueprint: def-pur-canonical-rational-purity-realization). -/
def ordinaryLeftUnitor
    (K : DerivedCategory (integralTowerModules P.coefficients.l P.extension Y)) :
    (ordinaryModel P.coefficients.l P.extension Y).tensor.obj
      ((twist P Y (Y ↘ Spec (.of P.field.k)) 0).obj,K) ≅ K :=
by
  exact tensorLeftUnitorFromPresentation (ordinaryMonoidal P.coefficients.l P.extension Y)
    (ordinaryModel P.coefficients.l P.extension Y).tensor
    (ordinaryTensor_eq P Y) _ K
    (ordinaryCoefficientUnit P Y (Y ↘ Spec (.of P.field.k)))

section
attribute [local semireducible] PurCompactSupport.image
attribute [local irreducible] orientationTrace ordinaryLeftUnitor projection

/-- The actual trace/projection composite whose adjoint is smooth purity.
Source: rational purity proof Step 1, trace-transpose construction
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralTraceTransposeOfOrientation (d : ℕ) [SmoothOfRelativeDimension d f]
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0))
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).F.obj
      (integralSource P f d K) ⟶ K :=
  ObjectProperty.homMk
    ((S.ring.left c (ConstructibleExceptionalCoefficients.RingStage.integral
      (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).hom.app
        (integralSource P f d K) ≫
      (PurCompactSupport.image (PurCompactSupport.completed P.coefficients.l P.extension)
        c).map (ordinarySource P f d K).hom ≫
      (@asIso _ _ _ _ (projection P f c d K) (projection_isIso P f c d K)).inv ≫
      (ordinaryModel P.coefficients.l P.extension Y).tensor.map
        (Prod.mkHom (orientationTrace P f c S d a) (𝟙 K.obj)) ≫
      (ordinaryLeftUnitor P K.obj).hom)

end

attribute [local irreducible] integralTraceTransposeOfOrientation

/-- The fixed transpose uses the transported, finite-trace-normalized adic unit
orientation. Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralTraceTranspose (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :=
  integralTraceTransposeOfOrientation P f c S d (orientation P f c S d) K

attribute [local irreducible] integralTraceTranspose

/-- Integral purity is the actual adjoint transpose of that fixed composite.
The only chosen orientation is uniquely determined on the coefficient unit.
Source: rational purity proof Step 1 and the trace-transpose convention
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralMap (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    integralSource P f d K ⟶
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj K :=
  (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).adjunction.homEquiv _ _
    (integralTraceTranspose P f c S d K)

attribute [local irreducible] integralMap

/-- On every integral input, the chosen purity map is the transpose constructed
from the transported adic unit orientation. The trace premise is exactly the
finite-reduction normalization of that orientation, with the finite maps pinned
by finiteIntegration_smoothPurityMap. Thus this compares maps, not only objects.
Source: thm-pur-adic-reconstruction; rational purity proof Step 1;
lem-pur-tower-trace-purity-comparison
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: orientation_eq_adic identifies the finite-trace-normalized orientation
with the transported reconstructed unit map a. Substitute that equality in the
explicit projection/trace composite integralTraceTranspose. Applying the actual
constructible adjunction homEquiv gives the asserted equality for every K.
No uniqueness of a coherent lift for a general K is used. -/
theorem integralMap_eq_adicTraceTranspose (d : ℕ) [SmoothOfRelativeDimension d f]
    (a : twist P X (X ↘ Spec (.of P.field.k)) d ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj
        (twist P Y (Y ↘ Spec (.of P.field.k)) 0))
    (ha : IsNormalizedTrace P f c d (orientationTrace P f c S d a))
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    integralMap P f c S d K =
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).adjunction.homEquiv _ _
        (integralTraceTransposeOfOrientation P f c S d a K) := by
  unfold integralMap integralTraceTranspose
  rw [orientation_eq_adic P f c S d a ha]

/-- The trace-transpose integral comparison is invertible.
Source: rational purity proof Step 1, transporting adic purity
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: the finite diagonal orientations are compatible with reduction and yield the
normalized tower orientation. The finite tensor-counit transpose is exactly
smoothPurityMap, including its shift reassociation. Strict tower reconstruction
carries that map to integralMap, because all tensor, compactification, and coefficient
comparisons preserve their normalized units and counits. Each finite purity map is
invertible. Normalized reconstruction preserves its inverse, hence integralMap is
invertible. This uses the full trace transpose, not uniqueness of arbitrary lifts. -/
theorem integralMap_isIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    IsIso (integralMap P f c S d K) := by
  sorry

/-- The canonical integral purity isomorphism, with its map already constructed.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def integralIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y) :
    integralSource P f d K ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.integral
        (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.obj K :=
  @asIso _ _ _ _ (integralMap P f c S d K) (integralMap_isIso P f c S d K)

end RelativeOrientation

section Rational
variable (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := f))

/-- Every underlying integral representative is in the finite-Tor category.
There is no stable-lattice assumption on any rational arrow.
Source: rational purity proof Step 1; integral residue-Tor theorem
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: an object of the scalar localization has an actual integral constructible
representative. integral_residue_tor identifies its object predicate with the
uniform finite-Tor constructible predicate, proving the asserted membership. -/
theorem representativeTor
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegral P.coefficients.l P.extension Y K.obj.obj := by
  apply (congrFun (integral_residue_tor P.field P.coefficients.l
    P.coefficients.different P.extension Y).2 _).mp
  exact K.obj.property

/-- The unchanged integral object presenting a rational object.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def representative
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension Y :=
  ⟨K.obj.obj,representativeTor P K⟩

/-- Rationalization returns the original object, literally in the scalar localization.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: rationalization includes the integral full subcategory and changes only Hom
groups by scalar localization. Both objects therefore have the same integral
representative; their membership proofs are equal by proof irrelevance. -/
theorem representative_eq
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) Y).obj (representative P K) = K := by
  cases K
  rfl

/-- The rational tensor and pullback retain their integral object formulas.
The first input here is the localization of the *integrally* shifted line, so this
identity makes no claim that a rational shift by 2d is literally the integral shift.
Source: rational purity proof Step 1, localization of integral representatives
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: use the recorded object clauses of rationalDerivedTensor and
rationalDerivedPullback. The nonnegative integral Tate line is the positive root
tensor power used by twist; inherited integral shifts retain the ambient shift.
The resulting ambient objects agree. Full-subcategory membership proofs agree by
proof irrelevance, yielding this object equality. -/
theorem rationalIntegralSource_eq (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalDerivedTensor P.coefficients.l P.extension X).obj
      ((sfRationalConstructibleLocalization P.coefficients.l P.extension X).obj
        ((sfIntegralTwistingCoefficient P.coefficients.l P.extension X (d : ℤ))⟦2*(d : ℤ)⟧),
        (rationalDerivedPullback P.coefficients.l P.extension f).obj K) =
      (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldStage P) X).obj
        (integralSource P f d (representative P K)) := by
  have hTensor : ∀ MN,
      (rationalDerivedTensor P.coefficients.l P.extension X).obj MN =
        ⟨(constructibleIntegralTensor P.coefficients.l P.extension X).obj
          (MN.1.obj, MN.2.obj)⟩ := by
    unfold rationalDerivedTensor
    exact (rationalDerivedTensor_existsUnique P.coefficients.l P.extension X).exists.choose_spec.1
  have hPull : (rationalDerivedPullback P.coefficients.l P.extension f).obj K =
      ⟨(constructibleIntegralPullback P.coefficients.l P.extension f).obj K.obj⟩ := by
    unfold rationalDerivedPullback
    exact (rationalDerivedPullback_existsUnique
      P.coefficients.l P.extension f).exists.choose_spec.2.1 K
  rw [hTensor, hPull]
  apply congrArg ScalarLocalization.mk
  apply ObjectProperty.FullSubcategory.ext
  change (integralCompletedTensor P.coefficients.l P.extension X).obj (_, _) =
    (integralCompletedTensor P.coefficients.l P.extension X).obj (_, _)
  congr 1
  change (((sfIntegralTwistingCoefficient P.coefficients.l P.extension X
      (d : ℤ))⟦2 * (d : ℤ)⟧).obj,
      (integralDerivedPullback P.coefficients.l P.extension f).obj K.obj.obj) =
    ((twist P X (X ↘ Spec (.of P.field.k)) d).obj,
      (integralDerivedPullback P.coefficients.l P.extension f).obj K.obj.obj)
  rw [fullSubcategory_shift_obj]
  unfold twist
  rfl

attribute [local irreducible] integralIso integralSource representative
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The source comparison uses the inverse localization commShiftIso at 2d,
followed by the unchanged integral tensor/pullback object formulas. The rational
shift is only normalized at one; its coherent comparison supplies all other shifts.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def rationalSourceComparison (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalSource P.coefficients.l P.extension f d).obj K ≅
      (ConstructibleExceptionalCoefficients.rationalization P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldStage P) X).obj
        (integralSource P f d (representative P K)) :=
by
  unfold rationalSource
  exact
    (rationalDerivedTensor P.coefficients.l P.extension X).mapIso
      (Iso.prod
        (((sfRationalConstructibleLocalization P.coefficients.l P.extension X).commShiftIso
          (2*(d : ℤ))).symm.app
            (sfIntegralTwistingCoefficient P.coefficients.l P.extension X (d : ℤ)))
        (Iso.refl _)) ≪≫ eqToIso (rationalIntegralSource_eq P f d K)

attribute [local irreducible] rationalSourceComparison

/-- The canonical rational purity isomorphism: rationalize the constructed integral
trace transpose, then use the specified counit-preserving exceptional comparison.
Source: rational purity proof Step 1
(blueprint: def-pur-canonical-rational-purity-realization). -/
def rationalIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (rationalSource P.coefficients.l P.extension f d).obj K ≅
      (operation P f c S (ConstructibleExceptionalCoefficients.Stage.rational
        (l := P.coefficients.l)
        (AdicSmoothDualizing.fieldStage P))).G.obj K :=
by
  refine rationalSourceComparison P f d K ≪≫ ?_
  refine (ConstructibleExceptionalCoefficients.rationalization
    P.coefficients.l P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P) X).mapIso
      (integralIso P f c S d (representative P K)) ≪≫ ?_
  refine (S.fields.rationalizationComparison c (AdicSmoothDualizing.fieldStage P)).b.app
    (representative P K) ≪≫ ?_
  exact (operation P f c S (ConstructibleExceptionalCoefficients.Stage.rational
    (l := P.coefficients.l) (AdicSmoothDualizing.fieldStage P))).G.mapIso
      (eqToIso (representative_eq P K))

attribute [local irreducible] rationalIso

end Rational

section CommonPurity
attribute [local instance 2000] IntermediateField.algebra'
attribute [local instance 0] ConstructibleExceptionalCoefficients.category

open AlgebraicallyClosedCoefficients GeneralAlgebraicallyClosedCoefficients
variable (P : PurityFiniteSetting.{u})

/-- Cache the published field structure on the small coefficient model.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
local instance commonModelField (i : Index P.coefficients.l P.coefficients.Qbar) :
    Field (Coefficient.{u} P.coefficients.l P.coefficients.Qbar i) :=
  (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
    i).field

/-- Cache the published algebra structure on the small coefficient model.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
local instance commonModelAlgebra (i : Index P.coefficients.l P.coefficients.Qbar) :
    Algebra (Padic P.coefficients.l)
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      i) :=
  (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
    i).algebra

/-- Cache the finite-dimensionality of the published small coefficient model.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
local instance commonModelFinite (i : Index P.coefficients.l P.coefficients.Qbar) :
    FiniteDimensional (Padic P.coefficients.l)
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      i) :=
  (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
    i).finite

/-- The fixed purity datum at an arbitrary finite subfield; only the coefficient field changes.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-rational-purity-realization). -/
abbrev stageSetting (L : Index P.coefficients.l P.coefficients.Qbar) : PurityFiniteSetting.{u} :=
  { P with extension := L.val, finiteExtension := L.property }

/-- The inverse of the published small-model algebra equivalence.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
def modelInverse : Coefficient.{u} P.coefficients.l P.coefficients.Qbar
    (AdicSmoothDualizing.fieldIndex P) →ₐ[Padic P.coefficients.l] P.extension :=
  (Shrink.algEquiv (Padic P.coefficients.l) P.extension).toAlgHom

/-- Scalar transport from the small model back to the given finite coefficient field.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-rational-purity-realization). -/
def modelBack (T : Scheme.{u}) :
    sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) T ⥤
      sfRationalConstructibleCategory P.coefficients.l P.extension T :=
  sfRationalScalarExtension P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) T 0
      (Fact.out : P.coefficients.l.Prime).ne_zero P.extension (modelInverse P)

/-- The two actual algebra equivalences compose to the identity.
Source: rational purity proof Step 2, small-model identity
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: apply the left inverse identity of Shrink.algEquiv pointwise. AlgHom
extensionality gives exactly the identity of algebra homomorphisms. -/
theorem modelComposite :
    (AdicSmoothDualizing.modelEmbedding P).comp (modelInverse P) =
      AlgHom.id (Padic P.coefficients.l)
        (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
          (AdicSmoothDualizing.fieldIndex P)) := by
  apply AlgHom.ext
  intro x
  change (AdicSmoothDualizing.modelEmbedding P) (modelInverse P x) = x
  exact (Shrink.algEquiv (Padic P.coefficients.l) P.extension).symm_apply_apply x

/-- The canonical round trip is balanced scalar associativity followed by the unit.
Source: rational purity proof Step 2, small-model transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
def modelRoundtrip (T : Scheme.{u}) :
    modelBack P T ⋙ AdicSmoothDualizing.modelScalar P T ≅
      𝟭 (sfRationalConstructibleCategory P.coefficients.l
        (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
          (AdicSmoothDualizing.fieldIndex P)) T) :=
  scalarAssociator P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) P.extension
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P))
    (modelInverse P) (AdicSmoothDualizing.modelEmbedding P)
    (AlgHom.id (Padic P.coefficients.l) _) (modelComposite P) T ≪≫
    sfRationalScalarUnit P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) T 0
        (Fact.out : P.coefficients.l.Prime).ne_zero

variable {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [QuasiCompact (X ↘ Spec (.of P.field.k))]
  [IsSeparated (X ↘ Spec (.of P.field.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [IsSeparated (Y ↘ Spec (.of P.field.k))]
  [∀ x : X, Invertible (P.coefficients.l : X.residueField x)]
  [∀ y : Y, Invertible (P.coefficients.l : Y.residueField y)]
  (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)
  (S : ConstructibleExceptionalCoefficients.System P.coefficients.l P.coefficients.Qbar
    P.field P.coefficients.different (f := f))

attribute [local irreducible] sourceScalar modelRoundtrip
  AdicSmoothDualizing.modelEmbedding

/-- Rational purity in the actual small coefficient model, transported through the
specified algebra equivalence and counit-preserving exceptional comparison.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-rational-purity-realization). -/
def smallModelIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) Y) :
    (rationalSource P.coefficients.l
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) f d).obj K ≅
    (S.ring.operation c (ConstructibleExceptionalCoefficients.Stage.rational (l := P.coefficients.l)
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).G.obj K :=
  (rationalSource P.coefficients.l
    (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldIndex P)) f d).mapIso ((modelRoundtrip P Y).app K).symm ≪≫
    (sourceScalar P.coefficients.l P.extension
      (Coefficient.{u} P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) (AdicSmoothDualizing.modelEmbedding P)
      f d ((modelBack P Y).obj K)).symm ≪≫
    (AdicSmoothDualizing.modelScalar P X).mapIso
      (rationalIso P f c S d ((modelBack P Y).obj K)) ≪≫
    (S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)) (AdicSmoothDualizing.modelEmbedding P)).b.app
          ((modelBack P Y).obj K) ≪≫
    (S.ring.operation c (ConstructibleExceptionalCoefficients.Stage.rational (l := P.coefficients.l)
      (ConstructibleExceptionalCoefficients.commonField P.coefficients.l P.coefficients.Qbar
        (AdicSmoothDualizing.fieldIndex P)))).G.mapIso ((modelRoundtrip P Y).app K)

attribute [local irreducible] smallModelIso

/-- The two published rational-stage category instances agree.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
theorem commonCategory_eq (T : Scheme.{u})
    (i : Index P.coefficients.l P.coefficients.Qbar) :
    ConstructibleExceptionalCoefficients.category P.coefficients.l
      P.coefficients.Qbar T (.rational (ConstructibleExceptionalCoefficients.commonField
        P.coefficients.l P.coefficients.Qbar i)) =
      GeneralAlgebraicallyClosedCoefficients.stageCategory
        P.coefficients.l P.coefficients.Qbar T i := by
  unfold ConstructibleExceptionalCoefficients.category
    GeneralAlgebraicallyClosedCoefficients.stageCategory
  rfl

/-- Transport an isomorphism along equality of the inherited category structures.
Source: rational purity proof Step 2, coefficient size transport
(blueprint: def-pur-canonical-rational-purity-realization). -/
def transportIsoCategory {C : Type (u + 2)} (cat cat' : Category.{u + 2} C)
    (h : cat = cat') {A B : C} (e : @Iso C cat A B) : @Iso C cat' A B := h ▸ e

/-- The canonical common-stage purity family. Each object is treated at its literal
finite stage, transported by its actual field-model equivalence, then included with the
specified exceptional coefficient comparison.
Source: rational purity proof Step 2
(blueprint: def-pur-canonical-rational-purity-realization). -/
def commonIso (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : generalAlgebraicallyClosedConstructibleCategory P.coefficients.l
      P.coefficients.Qbar Y) :
    (commonSource P.coefficients.l P.coefficients.Qbar f d).obj K ≅
      (S.ring.operation c .closed).G.obj K :=
by
  have e := smallModelIso (stageSetting P K.stage) f c S d K.obj
  dsimp only [stageSetting, AdicSmoothDualizing.fieldIndex,
    commonModelField, commonModelAlgebra, commonModelFinite] at e
  have e' := transportIsoCategory _ _ (commonCategory_eq P X K.stage) e
  refine commonSourceComparison P.coefficients.l P.coefficients.Qbar f d K ≪≫ ?_
  refine (GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := P.coefficients.l) (Ω := P.coefficients.Qbar) (Y := X) K.stage).mapIso e' ≪≫ ?_
  exact (S.common.commonComparison c K.stage).b.app K.obj

attribute [local irreducible] ScalarLocalization.category

attribute [-instance] commonModelField commonModelAlgebra commonModelFinite
attribute [local instance 1000] IntermediateField.algebra'
attribute [local instance 0] ConstructibleExceptionalCoefficients.category
attribute [local irreducible] AlgebraicGeometry.Scheme.ProEt
  AlgebraicGeometry.Scheme.instCategoryProEt AlgebraicGeometry.Scheme.ProEt.precoverage
  SheafOfModules.instAbelian SheafOfModules.instCategory scalarReductionSourceDerived

/-- Finite scalar extension carries the trace-normalized rational purity map to
that over the enlarged coefficient field, with the specified exceptional mate.
Source: rational purity proof Step 2, the finite-extension compatibility equation
(blueprint: def-pur-canonical-rational-purity-realization).
Proof: on the degree-zero unit orientation, reduce at every finite quotient.
The diagonal finite trace is compatible with coefficient scalar extension and its
fixed root generators. Finite reduction of maps from the shifted rank-one line is
jointly faithful, so the integral unit trace square commutes. Tensoring with an
arbitrary lattice, apply the actual projection formula and its counit compatibility;
the defining adjunction hom-equivalence yields the integral purity square. The
finite-free completed-scalar comparison identifies ordinary scalar tensor with
strict adic scalar extension. Rationalize this square. Since scalar localization
is linear, the equation holds on every object and respects the normalized source
comparison and the counit-preserving exceptional comparison in the display. -/
theorem rationalIso_scalar (L : AlgebraicallyClosedCoefficients.Index
      P.coefficients.l P.coefficients.Qbar)
    (a : P.extension →ₐ[Padic P.coefficients.l] L.val)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension Y) :
    (ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l P.coefficients.Qbar
      (AdicSmoothDualizing.fieldStage P) (AdicSmoothDualizing.fieldStage (stageSetting P L))
      a X).map (rationalIso P f c S d K).hom ≫
        (ConstructibleExceptionalCoefficients.FieldComparison.b
          (l := P.coefficients.l) (Ω := P.coefficients.Qbar)
          (X := X) (Y := Y)
          (s := .rational (AdicSmoothDualizing.fieldStage P))
          (t := .rational (AdicSmoothDualizing.fieldStage (stageSetting P L)))
          (A := S.ring.operation c (.rational (AdicSmoothDualizing.fieldStage P)))
          (B := S.ring.operation c
            (.rational (AdicSmoothDualizing.fieldStage (stageSetting P L))))
          (TX := ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
            P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
            (AdicSmoothDualizing.fieldStage (stageSetting P L)) a X)
          (TY := ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
            P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
            (AdicSmoothDualizing.fieldStage (stageSetting P L)) a Y)
          (S.fields.rationalComparison c (AdicSmoothDualizing.fieldStage P)
            (AdicSmoothDualizing.fieldStage (stageSetting P L)) a)).hom.app K =
      (sourceScalar P.coefficients.l P.extension L.val a f d K).hom ≫
        (rationalIso (stageSetting P L) f c S d
          ((ConstructibleExceptionalCoefficients.rationalScalar P.coefficients.l
            P.coefficients.Qbar (AdicSmoothDualizing.fieldStage P)
            (AdicSmoothDualizing.fieldStage (stageSetting P L)) a Y).obj K)).hom := by
  sorry

end CommonPurity

end RationalSmoothPurityCanonical

end WeilConjectures
