/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
public import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
import WeilConjectures.AlgebraicGeometry.CanonicalCoefficientTensorNormalization
import WeilConjectures.AlgebraicGeometry.InternalPullNormalizationExistence
import WeilConjectures.AlgebraicGeometry.InternalScalarNormalizationExistence
import WeilConjectures.AlgebraicGeometry.SectionPullNormalizationTransport
import WeilConjectures.AlgebraicGeometry.SectionTensorNormalizationTransport

/-! # Normalized internal scalar extension and geometric pullback

## References

* Stacks Tags 03EK, 06YY, 0G7E and 07A6.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

/-- Scalar extension is restricted derived tensor and commutes with geometric pullback,
with the universal computation normalizations and the fixed section comparisons
(Stacks, Tags 03EK, 06YS, 06YY, 0G7E, 0D6D, 07A6 and 0B65). -/
theorem internal_scalar_pullback_normalization (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ (tX : TensorNormalization a X) (tY : TensorNormalization a Y)
      (b : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X)
      (sX : SectionScalarComparison a X) (sY : SectionScalarComparison a Y),
      TensorNormalized a X tX ∧ TensorNormalized a Y tY ∧ PullNormalized a f b ∧
      SectionScalarNormalized a X sX ∧ SectionScalarNormalized a Y sY ∧
      SectionTensorNormalized a X sX tX ∧ SectionTensorNormalized a Y sY tY ∧
      SectionPullNormalized a f sX sY b := by
  let tX := canonicalCoefficientTensorNormalization a X
  let tY := canonicalCoefficientTensorNormalization a Y
  have htX := (canonicalCoefficientTensorNormalization_normalized a).1 X
  have htY := (canonicalCoefficientTensorNormalization_normalized a).1 Y
  obtain ⟨b, hb⟩ := internal_pull_normalization_exists a f
  obtain ⟨sX, hsX⟩ := internal_section_scalar_normalization_exists a X
  obtain ⟨sY, hsY⟩ := internal_section_scalar_normalization_exists a Y
  exact ⟨tX, tY, b, sX, sY, htX, htY, hb, hsX, hsY,
    section_tensor_normalized_of_normalized a X sX hsX tX htX,
    section_tensor_normalized_of_normalized a Y sY hsY tY htY,
    section_pull_normalized_of_normalized a f sX sY hsX hsY b hb⟩

end AlgebraicGeometry.ProEtale.QuotientChange
