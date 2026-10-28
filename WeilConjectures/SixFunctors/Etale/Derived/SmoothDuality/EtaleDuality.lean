/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMapLinear
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationProjection
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Charts

/-!
# Smooth duality for étale morphisms

For an étale morphism `e : X ⟶ Y` admitting a compactification, `Re^! ≅ Le^*` and the canonical
tensor map `θ_{e,K} : ω_e ⊗ᴸ Le^* K ⟶ Re^! K` is an isomorphism for every `K`, with `ω_e ≅ Λ_X`
(`AlgebraicGeometry.Etale.etaleSmoothDuality`): the étale case of the proof of blueprint
`thm-asd-smooth-tensor`, from `lem-amb-etale-adjoint-locality`.

The compactly supported direct image `R(e)_!` is left adjoint to `Le^*`
(`AlgebraicGeometry.Etale.compactificationEtaleAdjunction`), and the unit of this adjunction is
compatible with the projection map
(`AlgebraicGeometry.Etale.compactificationEtaleUnit_tensor`). Hence the tensor map of
`R(e)_! ⊣ Le^*` is the inverse of the tensor comparison of `Le^*`
(`CategoryTheory.Adjunction.projectionTensorMap_eq_of_unit`), an isomorphism, and so is the
tensor map of `R(e)_! ⊣ Re^!`, the tensor maps of two right adjoints agreeing
(`CategoryTheory.Adjunction.projectionTensorMap_rightAdjointUniq_hom`).

## Main statements

- `AlgebraicGeometry.Etale.etaleSmoothDuality`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

variable {X Y : Scheme.{u}} (e : X ⟶ Y) [_root_.AlgebraicGeometry.Etale e] [HasCompactification e]

/-- The adjunction `R(e)_! ⊣ Le^*` of an étale morphism admitting a compactification. -/
noncomputable def rightDerivedLowerShriekEtaleAdjunction :
    R(e)_![ModuleCat.{u + 1} Λ] ⊣ L((e)^*[ModuleCat.{u + 1} Λ]) :=
  have := isIso_compactificationEtaleComparison Λ e (HasCompactification.compactification e)
  compactificationEtaleAdjunction Λ e (HasCompactification.compactification e)

/-- For an étale morphism `e`, the tensor map of `R(e)_! ⊣ Le^*` is an isomorphism. -/
theorem isIso_lowerShriekRightAdjointTensorMap_rightDerivedLowerShriekEtaleAdjunction
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (lowerShriekRightAdjointTensorMap (rightDerivedLowerShriekEtaleAdjunction Λ e) M N) := by
  have := isIso_compactificationEtaleComparison Λ e (HasCompactification.compactification e)
  refine Adjunction.isIso_projectionTensorMap_of_unit _ _
    (fun A B ↦ leftDerivedUpperStarTensorIso _ e A B)
    (fun φ B ↦ leftDerivedUpperStarTensorIso_hom_naturality_left e φ B) (fun M N ↦ ?_) M N
  rw [rightDerivedLowerShriekEtaleAdjunction, compactificationEtaleAdjunction_unit_app,
    compactificationEtaleAdjunction_unit_app]
  exact compactificationEtaleUnit_tensor Λ e _ M N

/-- For an étale morphism `e`, the tensor map `Re^! M ⊗ᴸ Le^* N ⟶ Re^!(M ⊗ᴸ N)` is an
isomorphism. -/
theorem isIso_rightDerivedUpperShriekTensorMap_of_etale
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    IsIso (rightDerivedUpperShriekTensorMap e M N) :=
  (Adjunction.isIso_projectionTensorMap_iff_of_adjunction _
    (rightDerivedUpperShriekAdjunction Λ e) (rightDerivedLowerShriekEtaleAdjunction Λ e)
    (projectionMap_app_app_naturality_left e) M N).2
    (isIso_lowerShriekRightAdjointTensorMap_rightDerivedLowerShriekEtaleAdjunction Λ e M N)

/-- For an étale morphism `e`, the dualizing complex is trivial: `ω_e = Re^! Λ_Y ≅ Le^* Λ_Y ≅
Λ_X`. -/
noncomputable def dualizingComplexIsoOfEtale : dualizingComplex Λ e ≅ 𝟙_ _ :=
  (Adjunction.rightAdjointUniq (rightDerivedUpperShriekAdjunction Λ e)
      (rightDerivedLowerShriekEtaleAdjunction Λ e)).app (𝟙_ _) ≪≫
    leftDerivedUpperStarUnitIso _ e

variable {Λ} in
/-- **Smooth duality for étale morphisms** (the étale case of the proof of blueprint
`thm-asd-smooth-tensor`): for every étale `e` admitting a compactification, the canonical tensor
map `θ_{e,K} : ω_e ⊗ᴸ Le^* K ⟶ Re^! K` is an isomorphism for every `K`, and `ω_e ≅ Λ`. -/
theorem etaleSmoothDuality : EtaleSmoothDuality Λ := by
  intro V W e _ _
  refine ⟨fun K ↦ ?_, ⟨dualizingComplexIsoOfEtale Λ e⟩⟩
  have := isIso_rightDerivedUpperShriekTensorMap_of_etale Λ e (𝟙_ _) K
  rw [dualizingComplexTensorMap, lowerShriekRightAdjointUnitTensorMap]
  infer_instance

end Etale

end AlgebraicGeometry
