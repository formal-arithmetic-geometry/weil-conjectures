/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryDifferential
import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationGradedAugmentation
/-! # Ordinary evaluation: a step of the chain calculation

## References

* [Stacks Project, Tag 08DJ](https://stacks.math.columbia.edu/tag/08DJ)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
/-- Ordinary evaluation factors through the single coefficient unit, independently of F. -/
theorem schemeOrdinaryEvaluation_chain_map_exists (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) :
    letI := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
    let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
    let V := homComplex (R := Y.sheaf) P O
    let eta := CochainComplex.toKInjectiveResolution.{u}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    let phiO := ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app O)
    ∃ e : pullbackTensorTotal Y V P ⟶ O,
      schemeTensorHomUncurry Y V P O phiO = e ≫ eta.app O := by
  classical
  let := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let O := (HomologicalComplex.single _ (.up ℤ) 0).obj
    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))
  let V := homComplex (R := Y.sheaf) P O
  let eta := CochainComplex.toKInjectiveResolution.{u}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let phiO := ((homComplexFunctor (R := Y.sheaf)).obj (op P)).map (eta.app O)
  let U := schemeTensorHomUncurry Y V P O phiO
  have hg (n : ℤ) : U.f n = schemeOrdinaryEvaluationGraded Y P O n ≫ (eta.app O).f n :=
    schemeOrdinaryEvaluationGraded_augmentation Y P O (eta.app O) n
  have : Mono (eta.app O) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} _ O).1
  let e : pullbackTensorTotal Y V P ⟶ O :=
    { f := schemeOrdinaryEvaluationGraded Y P O
      comm' := fun n m _ ↦ by
        apply (cancel_mono ((eta.app O).f m)).1
        have hc := (eta.app O).comm n m
        change (eta.app O).f n ≫ ((schemeHomKInjectiveResolution Y).obj O).d n m =
          O.d n m ≫ (eta.app O).f m at hc
        rw [Category.assoc, ← hc, ← Category.assoc, ← hg n, Category.assoc, ← hg m]
        exact U.comm n m }
  refine ⟨e, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  exact hg n
end AlgebraicGeometry
