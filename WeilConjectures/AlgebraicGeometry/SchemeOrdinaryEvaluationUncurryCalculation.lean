/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationChainCalculation
import WeilConjectures.AlgebraicGeometry.SchemeTensorEvaluationLocalizationCoherence

/-! # Uncurried ordinary evaluation calculation

## References

* [Stacks Project, Tag 08DJ](https://stacks.math.columbia.edu/tag/08DJ)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

set_option maxHeartbeats 1000000 in
-- Elaborating the fixed Hom and tensor maps uses the sheaf coproduct instances.
/-- The ordinary component equation determines the composite of explicit evaluation maps.
This statement involves only constructed chain maps and the lax tensor comparison;
it does not mention the derived tensor-Hom equivalence or transport to other objects. -/
theorem schemeOrdinaryEvaluation_uncurry_calculation (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (P F : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (f : pullbackTensorTotal Y F
        (homComplex (R := Y.sheaf) P
          ((HomologicalComplex.single _ (.up ℤ) 0).obj
            (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))))) ⟶
      homComplex (R := Y.sheaf) P F)
    (hf : IsSchemeOrdinaryEvaluation Y P F f) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    let V := homComplex (R := Y.sheaf) P O
    let eta := CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let phiF := f ≫ ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app F)
    let phiO := ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app O)
    (pullbackTensorModelMap Y F V ▷ DerivedCategory.Q.obj P) ≫
        pullbackTensorModelMap Y (pullbackTensorTotal Y F V) P ≫
        DerivedCategory.Q.map
          (schemeTensorHomUncurry Y (pullbackTensorTotal Y F V) P F phiF) ≫
        schemeHomResolutionInverse Y F =
      (α_ (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj V)
        (DerivedCategory.Q.obj P)).hom ≫
      DerivedCategory.Q.obj F ◁
        (pullbackTensorModelMap Y V P ≫
          DerivedCategory.Q.map (schemeTensorHomUncurry Y V P O phiO) ≫
          schemeHomResolutionInverse Y O ≫
          ((DerivedCategory.quotientCompQhIso _).app O).inv) ≫
      (ρ_ (DerivedCategory.Q.obj F)).hom := by
  classical
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let V := homComplex (R := Y.sheaf) P O
  let eta := CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  obtain ⟨e, hO, hF⟩ := schemeOrdinaryEvaluation_chain_calculation Y P F f hf
  have hc := schemeTensorEvaluation_localization_coherence Y F V P e
  have hres (M : CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
      DerivedCategory.Q.map (eta.app M) ≫ schemeHomResolutionInverse Y M =
        𝟙 (DerivedCategory.Q.obj M) := by
    have : IsIso (DerivedCategory.Q.map (eta.app M)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ M).2
    exact IsIso.hom_inv_id _
  dsimp only [eta] at hres
  have hrO := hres O
  dsimp only [O] at hrO
  dsimp only
  rw [hF, hO]
  simp only [Functor.map_comp, Category.assoc]
  rw [hres F, Category.comp_id, reassoc_of% hrO]
  exact hc

end AlgebraicGeometry
