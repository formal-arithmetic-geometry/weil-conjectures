/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # The actual connected-component inverse image

Source: Hemo--Richarz--Scholbach, construction (4.1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The relative-test inverse image is exact and strong symmetric monoidal.

Source: Hemo--Richarz--Scholbach, construction (4.1); Stacks Tags 00X1 and 00YV
(blueprint: lem-zl-condensed-component-inverse-image).

Proof: the relative-site theorem realizes direct image as precomposition with the
fixed test functor. Thus precomposition takes set sheaves to set sheaves, proving
continuity. The same theorem gives preservation of finite limits. The profinite
slice has finite limits, so the test functor is representably flat. Its opposite
left Kan extension consequently preserves finite limits; sheafification does too.
The constructed inverse image is therefore left exact. Its explicit adjunction
makes it preserve all colimits. Filtered Kan extension and tensor cocontinuity
make its oplax tensor and unit comparisons invertible. The right adjoint is lax
braided by pointwise restriction, so the monoidal adjunction makes the left
adjoint braided. These arguments include the empty affine scheme. -/
theorem condensed_component_inverse_image (T : Scheme.{u}) [IsAffine T] :
    ∃ (_ : (componentTests T).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (Scheme.ProEt.topology T)),
      Nonempty (componentInverse T).Braided ∧
      PreservesFiniteLimits (componentInverse T) ∧
      PreservesFiniteColimits (componentInverse T) := by
  obtain ⟨_, _, _, _, _, hlim, _, _, π, ⟨e⟩, _⟩ :=
    Classical.choose_spec (component_relative_profinite_site T)
  let hC : (componentTests T).IsContinuous
      ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
      (Scheme.ProEt.topology T) := by
    constructor
    intro G
    rw [← isSheaf_iff_isSheaf_of_type]
    exact (Presheaf.isSheaf_of_iso_iff (e.app G)).mp (π.direct.obj G).property
  let := hC
  let : PreservesFiniteLimits (componentTests T) := hlim
  let : RepresentablyFlat (componentTests T) := flat_of_preservesFiniteLimits _
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (componentTests T) Ab.{u + 1}
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)
  let : (componentInverse T).Monoidal := by
    dsimp only [componentInverse]
    infer_instance
  refine ⟨hC, ?_, ?_, ?_⟩
  · exact ⟨{ braided := fun X Y ↦ adj.μ_comp_map_braiding X Y }⟩
  · dsimp only [componentInverse]
    infer_instance
  · let : (componentInverse T).IsLeftAdjoint := adj.isLeftAdjoint
    infer_instance

end AlgebraicGeometry.ProEtale.CondensedRing
