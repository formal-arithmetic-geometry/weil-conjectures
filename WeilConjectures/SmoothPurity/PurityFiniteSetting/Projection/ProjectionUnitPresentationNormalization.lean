/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityCoordinates
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionPurityCoordinates
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationTransposes
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tensor.SmoothPurityTensorUnit
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.CategoryTheory.Iso
import all Mathlib.Logic.Small.Defs
import all WeilConjectures.Compactification.Defs
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionTensorIntegration

/-! # Projection agreement at the coefficient unit

Source: projection-purity-agreement, final canonical reassociations.
(blueprint: lem-pur-projection-unit-presentation-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local instance] _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

end WeilConjectures.PurityFiniteSetting

namespace WeilConjectures.PurityFiniteSetting

private theorem projection_tensor_unit_cancel {C : Type v} [Category.{w} C]
    [MonoidalCategory C] {M T D S : C} (e : M ≅ 𝟙_ C) (r : S ≅ M ⊗ T)
    (m : T ⟶ D) {D' : C} (u : D ≅ D') :
    (r ≪≫ ((curriedTensor C).mapIso e).app T ≪≫ λ_ T).inv ≫ r.hom ≫
        ((curriedTensor C).obj M).map m ≫
        (((curriedTensor C).mapIso e).app D ≪≫ λ_ D ≪≫ u).hom = m ≫ u.hom := by
  have hn : ((curriedTensor C).obj M).map m ≫
      (((curriedTensor C).mapIso e).app D).hom =
      (((curriedTensor C).mapIso e).app T).hom ≫
        ((curriedTensor C).obj (𝟙_ C)).map m := by
    simpa only [Iso.app_hom, Functor.mapIso_hom] using
      ((curriedTensor C).map e.hom).naturality m
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn]
  simp only [Iso.inv_hom_id_assoc]
  have h₀ : (λ_ T).inv ≫ ((curriedTensor C).obj (𝟙_ C)).map m ≫ (λ_ D).hom = m :=
    (congrArg (fun z ↦ (λ_ T).inv ≫ z) (leftUnitor_naturality m)).trans
      (Iso.inv_hom_id_assoc (λ_ T) m)
  rw [reassoc_of% h₀]

/-- Projection agreement at the unit, with its actual unit and shift coordinates.
Source: blueprint latest, projection-purity-agreement, final canonical reassociations.
(blueprint: lem-pur-projection-unit-presentation-normalization).

Proof: specialize projection_presentation_coordinate to the coefficient unit.
The unit-mate identity smoothPurityTheta_unit identifies its final theta factor
with tensoring the specified pullback-unit map followed by the left unitor.
The presentation tensor map is tensoring the inverse diagonal orientation
followed by theta. Naturality of tensoring the unit map and the left unitor
moves that inverse orientation past the two unit constraints. The reassociation,
the tensor-unit comparison and the unitor then cancel with their inverses.
This argument allows any rank, including zero, and does not choose an orientation.
The hunit argument records the existing unit's finite-Tor property; its proof
is irrelevant to the map. -/
theorem projection_unit_presentation_normalization
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Y : Scheme.{u}) [IsAffine Y] (aY : Y ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] (d : ℕ)
    (hunit : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (projectionSetting F C E n).Coefficient) Y
      (Etale.ordinaryFiniteUnit (projectionSetting F C E n).Coefficient Y)) :
  let P := projectionSetting F C E n
  letI := (ProEtale.AffineSpacePurity.projection_geometry Y d).1
  letI := (ProEtale.AffineSpacePurity.projection_geometry Y d).2
  letI := projection_smooth Y d
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek P.Coefficient
    (iteratedAffineLineProj Y d)
  letI : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient)
      (HasCompactification.compactification (iteratedAffineLineProj Y d))).IsLeftAdjoint :=
    inferInstanceAs (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} P.Coefficient) (iteratedAffineLineProj Y d)).IsLeftAdjoint
  let K := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
      (Etale.ordinaryFiniteUnit P.Coefficient Y)
  let Kp : ProEtale.AffineSpacePurity.Plus P.Coefficient Y :=
    ⟨K, (ProEtale.DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
      (P.diagonalUnitPlus Y)).plus⟩
  let e :=
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (iteratedAffineLineProj Y d)).mapDerivedCategory.mapIso
        (X := K) (projectionUnitRaw P.Coefficient Y) ≪≫
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) (iteratedAffineLineProj Y d)).symm.app _ ≪≫
      ProEtale.leftDerivedUpperStarUnitIso
        (ModuleCat.{u + 1} P.Coefficient) (iteratedAffineLineProj Y d)
  let r := P.smoothPurityReassociation (iteratedAffineLine Y d) d
    ((P.smoothPurityPullback (iteratedAffineLineProj Y d)).obj K)
  (r ≪≫ ((curriedTensor (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology (iteratedAffineLine Y d))
        (ModuleCat.{u + 1} P.Coefficient)))).mapIso e).app
          (P.diagonalTwist (iteratedAffineLine Y d) d) ≪≫
      λ_ (P.diagonalTwist (iteratedAffineLine Y d) d)).inv ≫
    projectionAffineInPresentation F C E n Y aY Kp
      (Etale.ordinaryFiniteUnit P.Coefficient Y) hunit (Iso.refl _) d =
    (P.diagonalDualizingObject d (iteratedAffineLineProj Y d) aY).inv ≫
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) (iteratedAffineLine Y d)).mapDerivedCategory.mapIso
          (((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
              (ModuleCat.{u + 1} P.Coefficient)
              (HasCompactification.compactification (iteratedAffineLineProj Y d)))).rightAdjointUniq
            (Etale.rightDerivedUpperShriekAdjunction P.Coefficient
              (iteratedAffineLineProj Y d))).app _)).hom := by
  let P := projectionSetting F C E n
  let := (ProEtale.AffineSpacePurity.projection_geometry Y d).1
  let := (ProEtale.AffineSpacePurity.projection_geometry Y d).2
  let := projection_smooth Y d
  let := Etale.isLeftAdjoint_rightDerivedLowerShriek P.Coefficient
    (iteratedAffineLineProj Y d)
  let : (Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} P.Coefficient)
      (HasCompactification.compactification (iteratedAffineLineProj Y d))).IsLeftAdjoint :=
    inferInstanceAs (Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} P.Coefficient) (iteratedAffineLineProj Y d)).IsLeftAdjoint
  let K := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
      (Etale.ordinaryFiniteUnit P.Coefficient Y)
  let Kp : ProEtale.AffineSpacePurity.Plus P.Coefficient Y :=
    ⟨K, (ProEtale.DerivedCategory.plusEtaleOrigin_mapDerivedCategory_obj
      (P.diagonalUnitPlus Y)).plus⟩
  let e :=
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (iteratedAffineLineProj Y d)).mapDerivedCategory.mapIso
        (X := K) (projectionUnitRaw P.Coefficient Y) ≪≫
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) (iteratedAffineLineProj Y d)).symm.app _ ≪≫
      ProEtale.leftDerivedUpperStarUnitIso
        (ModuleCat.{u + 1} P.Coefficient) (iteratedAffineLineProj Y d)
  let r := P.smoothPurityReassociation (iteratedAffineLine Y d) d
    ((P.smoothPurityPullback (iteratedAffineLineProj Y d)).obj K)
  change (r ≪≫ ((curriedTensor (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology (iteratedAffineLine Y d))
        (ModuleCat.{u + 1} P.Coefficient)))).mapIso e).app
          (P.diagonalTwist (iteratedAffineLine Y d) d) ≪≫
      λ_ (P.diagonalTwist (iteratedAffineLine Y d) d)).inv ≫
    projectionAffineInPresentation F C E n Y aY Kp
      (Etale.ordinaryFiniteUnit P.Coefficient Y) hunit (Iso.refl _) d = _
  have hp : r.hom ≫
      P.smoothPurityTensorMapInPresentation (iteratedAffineLineProj Y d) d aY K
        (Etale.ordinaryFiniteUnit P.Coefficient Y) (Iso.refl _) =
      projectionAffineInPresentation F C E n Y aY Kp
        (Etale.ordinaryFiniteUnit P.Coefficient Y) hunit (Iso.refl _) d := by
    dsimp only [projectionAffineInPresentation]
    convert! projection_presentation_coordinate F C E n Y aY Kp
      (Etale.ordinaryFiniteUnit P.Coefficient Y) hunit (Iso.refl _) d using 1
  have ht : P.smoothPurityTheta (iteratedAffineLineProj Y d) K
      (Etale.ordinaryFiniteUnit P.Coefficient Y) (Iso.refl _) =
      (((curriedTensor (_root_.DerivedCategory
          (Sheaf (Scheme.ProEt.topology (iteratedAffineLine Y d))
            (ModuleCat.{u + 1} P.Coefficient)))).mapIso e).app
        (P.diagonalDualizing (iteratedAffineLineProj Y d)) ≪≫
        λ_ (P.diagonalDualizing (iteratedAffineLineProj Y d)) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) (iteratedAffineLine Y d)).mapDerivedCategory.mapIso
            (((Adjunction.ofIsLeftAdjoint (Etale.rightDerivedLowerShriekOfCompactification
                (ModuleCat.{u + 1} P.Coefficient)
                (HasCompactification.compactification
                  (iteratedAffineLineProj Y d)))).rightAdjointUniq
              (Etale.rightDerivedUpperShriekAdjunction P.Coefficient
                (iteratedAffineLineProj Y d))).app _)).hom := by
    convert! P.smoothPurityTheta_unit (iteratedAffineLineProj Y d) using 1
  rw [← hp]
  simp only [smoothPurityTensorMapInPresentation]
  rw [ht]
  convert! projection_tensor_unit_cancel e r
    (P.diagonalDualizingObject d (iteratedAffineLineProj Y d) aY).inv _ using 1

end WeilConjectures.PurityFiniteSetting
