/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.CanonicalFiniteUnitOrientation
import WeilConjectures.PoincareDuality.RationalSmoothPurityCanonical.CanonicalRealizationTensorUnit

/-! # Tensor normalization at the finite coefficient unit

Source: latest def-pur-smooth-purity-map and def-pur-smooth-trace.
(blueprint: lem-pur-canonical-finite-unit-tensor).
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

attribute [local irreducible] sfIntrinsicModuleEquivalence ProEtale.comparisonUpperStar
  Functor.mapDerivedCategory HasDerivedCategory.standard

private theorem tensorUnitFromPresentation_naturality {C : Type*} [Category C]
    [MonoidalCategory C] (T : C ⥤ C ⥤ C) (h : T = curriedTensor C)
    {M N : C} (a : M ⟶ N) :
    (T.obj (𝟙_ C)).map a ≫ (tensorUnitFromPresentation T h N).hom =
      (tensorUnitFromPresentation T h M).hom ≫ a := by
  subst T
  simpa only [tensorUnitFromPresentation, eqToIso_refl, Iso.trans_hom, Iso.refl_hom,
    Category.id_comp, curriedTensor_obj_obj, curriedTensor_obj_map] using leftUnitor_naturality a

private theorem mapFour {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B E G H : C} (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ G) (d : G ⟶ H) :
    F.map (a ≫ b ≫ c ≫ d) = F.map (a ≫ b) ≫ F.map (c ≫ d) := by
  simp only [Functor.map_comp, Category.assoc]

private theorem map_comp_factor {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B E G : C} (r : A ⟶ B) (t : B ⟶ G) (u : B ⟶ E)
    (v : F.obj E ⟶ F.obj G) (h : F.map t = F.map u ≫ v) :
    F.map r ≫ F.map t = F.map (r ≫ u) ≫ v := by
  rw [h, ← Category.assoc, ← Functor.map_comp]

private theorem tensorMap_presentation (Q : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of Q.field.k))] [Y.Over (Spec (.of Q.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of Q.field.k))]
    [QuasiCompact (X ↘ Spec (.of Q.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of Q.field.k))]
    [QuasiCompact (Y ↘ Spec (.of Q.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of Q.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (K : Scheme.proEtaleDerivedCategory Y Q.Ring)
    (hK : finiteTorConstructible Q.coefficients.l Q.extension Q.level Q.level_pos Y K)
    (U : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Q.Coefficient)))
    (e : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
      Y).mapDerivedCategory.obj U ≅ (sfIntrinsicDerivedEquivalence Y Q.Ring).inverse.obj K) :
    Q.smoothPurityTensorMap f d K hK =
      (sfIntrinsicDerivedEquivalence X Q.Ring).functor.map
        (Q.smoothPurityTensorMapInPresentation f d (Y ↘ Spec (.of Q.field.k))
          ((sfIntrinsicDerivedEquivalence Y Q.Ring).inverse.obj K) U e) := by
  unfold PurityFiniteSetting.smoothPurityTensorMap
  exact congrArg (sfIntrinsicDerivedEquivalence X Q.Ring).functor.map
    ((Q.existsUnique_smoothPurityTensorMap f d K hK).exists.choose_spec U e)

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

/-- The tensor mate at the coefficient unit is the inverse diagonal orientation,
after pullback of the constant unit and the tensor left unitor.
Source: latest def-pur-smooth-purity-map, gamma^sm = (1 tensor Pi^-1) then theta;
def-pur-smooth-trace, coefficient-unit composite
(blueprint: lem-pur-canonical-finite-unit-tensor).
Proof: expand smoothPurityTensorMapInPresentation and use finiteUnitThetaFormula.
Naturality of the first-variable tensor comparison moves the inverse diagonal
orientation past the pullback-unit comparison. Naturality of the tensor left
unitor moves it past finiteTensorUnit. Apply the intrinsic realization functor,
distribute it over composition, and reassociate. This also covers dimension zero. -/
private theorem finiteUnitTensorPresentation (n d : ℕ) [SmoothOfRelativeDimension d f] :
    (sfIntrinsicDerivedEquivalence X (AdicSmoothDualizing.levelSetting P n).Ring).functor.map
      (@PurityFiniteSetting.smoothPurityTensorMapInPresentation
        (AdicSmoothDualizing.levelSetting P n) X Y f
        (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
        (inferInstanceAs (QuasiCompact f)) d (inferInstanceAs (SmoothOfRelativeDimension d f))
        (Y ↘ Spec (.of P.field.k))
        (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
        (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k))))
        ((sfIntrinsicDerivedEquivalence Y (AdicSmoothDualizing.levelSetting P n).Ring).inverse.obj
          ((AdicSmoothDualizing.levelSetting P n).coefficientUnit Y))
        (Etale.ordinaryFiniteUnit (AdicSmoothDualizing.levelSetting P n).Coefficient Y)
        ((sfIntrinsicDerivedEquivalence Y (AdicSmoothDualizing.levelSetting P n).Ring).unitIso.app
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
              Y).mapDerivedCategory.obj
                (Etale.ordinaryFiniteUnit (AdicSmoothDualizing.levelSetting P n).Coefficient Y)))) =
      (sfIntrinsicDerivedEquivalence X (AdicSmoothDualizing.levelSetting P n).Ring).functor.map
        ((((PurityFiniteSetting.smoothPurityTensor
          (AdicSmoothDualizing.levelSetting P n).Coefficient X).mapIso
            (finitePullUnit (AdicSmoothDualizing.levelSetting P n) f)).app
              ((AdicSmoothDualizing.levelSetting P n).diagonalTwist X d) ≪≫
          finiteTensorUnit (AdicSmoothDualizing.levelSetting P n).Coefficient X
            ((AdicSmoothDualizing.levelSetting P n).diagonalTwist X d)).hom) ≫
        finiteUnitOrientation P f c n d := by
  let : HasCompactification f := c.hasCompactification
  let Q := AdicSmoothDualizing.levelSetting P n
  let T := PurityFiniteSetting.smoothPurityTensor Q.Coefficient X
  let p := finitePullUnit Q f
  let a := @PurityFiniteSetting.diagonalDualizingObject Q X Y d f
    (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
    (inferInstanceAs (QuasiCompact f)) (inferInstanceAs (SmoothOfRelativeDimension d f))
    (Y ↘ Spec (.of P.field.k))
    (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k))))
  have hp := (T.map p.hom).naturality a.inv
  have hu : (T.obj (𝟙_ _)).map a.inv ≫
      (finiteTensorUnit Q.Coefficient X (Q.diagonalDualizing f)).hom =
      (finiteTensorUnit Q.Coefficient X (Q.diagonalTwist X d)).hom ≫ a.inv := by
    unfold finiteTensorUnit
    exact tensorUnitFromPresentation_naturality _ _ _
  unfold PurityFiniteSetting.smoothPurityTensorMapInPresentation finiteUnitOrientation
  erw [finiteUnitThetaFormula Q f]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc]
  erw [reassoc_of% hp, reassoc_of% hu]
  exact mapFour (sfIntrinsicDerivedEquivalence X Q.Ring).functor
    ((T.map p.hom).app (Q.diagonalTwist X d))
    (finiteTensorUnit Q.Coefficient X (Q.diagonalTwist X d)).hom a.inv
    ((Q.diagonalDualizingComparison f).hom ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
        X).mapDerivedCategory.map
        ((Etale.rightDerivedUpperShriek Q.Coefficient f).map
          ((ProEtale.derivedComparisonAdjunction
            (ModuleCat.{u + 1} Q.Coefficient) Y).unit.app
            (Etale.ordinaryFiniteUnit Q.Coefficient Y))) ≫
      (Q.smoothPurityExceptional f).map
        ((sfIntrinsicDerivedEquivalence Y Q.Ring).unitIso.hom.app
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Q.Coefficient)
            Y).mapDerivedCategory.obj (Etale.ordinaryFiniteUnit Q.Coefficient Y))))

section ChosenPresentation

attribute [local irreducible] levelSmoothExceptionalCounit sfIntrinsicDerivedEquivalence
  PurityFiniteSetting.smoothPurityExceptional PurityFiniteSetting.smoothPurityPullback

/-- At the coefficient unit, the specified smooth purity map factors through the
shift and tensor-unit source comparison followed by the explicit orientation.
Source: def-pur-smooth-purity-map, its unique ordinary presentation, and the
coefficient-unit composite in def-pur-smooth-trace
(blueprint: lem-pur-canonical-finite-unit-tensor).
Proof: characterize the chosen tensor map using its ordinary coefficient-unit
presentation. Apply the tensor comparison proved above. Naturality of realization
and its preservation of composition identify shift reassociation followed by the
pullback-unit and tensor-unit comparisons with finiteUnitSource. This is the
factorization before applying compact support or the exceptional counit. -/
theorem finiteUnitTensorFormula (n d : ℕ) [SmoothOfRelativeDimension d f]
    (hUnit : finiteTorConstructible P.coefficients.l P.extension (n + 1) (Nat.succ_pos n) Y
      ((AdicSmoothDualizing.levelSetting P n).coefficientUnit Y)) :
    levelSmoothPurityMap P f n d
      ((AdicSmoothDualizing.levelSetting P n).coefficientUnit Y) hUnit =
      (finiteUnitSource (AdicSmoothDualizing.levelSetting P n) f d).hom ≫
        finiteUnitOrientation P f c n d := by
  let : HasCompactification f := c.hasCompactification
  have hTensor := finiteUnitTensorPresentation P f c n d
  have hChosen := (@tensorMap_presentation
    (AdicSmoothDualizing.levelSetting P n) X Y
    (inferInstanceAs (X.Over (Spec (.of P.field.k))))
    (inferInstanceAs (Y.Over (Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (X ↘ Spec (.of P.field.k))))
    (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
    (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k)))) f
    (inferInstanceAs (f.IsOver (Spec (.of P.field.k))))
    (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
    (inferInstanceAs (QuasiCompact f)) d (inferInstanceAs (SmoothOfRelativeDimension d f))
    ((AdicSmoothDualizing.levelSetting P n).coefficientUnit Y) hUnit)
      (Etale.ordinaryFiniteUnit (AdicSmoothDualizing.levelSetting P n).Coefficient Y)
      ((sfIntrinsicDerivedEquivalence Y (AdicSmoothDualizing.levelSetting P n).Ring).unitIso.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
            Y).mapDerivedCategory.obj
              (Etale.ordinaryFiniteUnit (AdicSmoothDualizing.levelSetting P n).Coefficient Y)))
  unfold levelSmoothPurityMap PurityFiniteSetting.smoothPurityMap
  erw [hChosen]
  unfold finiteUnitSource
  simp only [Iso.trans_hom, Functor.mapIso_hom] at hTensor ⊢
  exact map_comp_factor _ _ _ _ _ hTensor

end ChosenPresentation

end RelativeOrientation
end RationalSmoothPurityCanonical
end WeilConjectures
