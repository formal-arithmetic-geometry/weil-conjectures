/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafConstruction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Local ingredients of alternating Čech exactness

## References

* Stacks Project, Tags 02FU and 01FM
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- Sheafification does not change the explicit intersection-product terms (Stacks, Tag 02FU). -/
theorem alternatingCechSheafPresheafTerms_unit_isIso
    {X : Scheme.{u}} {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) (p : ℕ) :
    IsIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app (alternatingCechSheafPresheafTerms U G p)) :=
  by
    classical
    have hcap (W : X.Opens) : Presheaf.IsSheaf (Opens.grothendieckTopology X)
        (cechCapModule G W).presheaf := by
      let T := Opens.map W.ι.base ⋙ W.ι.opensFunctor
      let e : T ≅ cechCapFunctor W := NatIso.ofComponents (fun V ↦
        eqToIso (by
          change W.ι ''ᵁ W.ι ⁻¹ᵁ V = V ⊓ W
          simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_comm]))
      have : (cechCapFunctor W).IsContinuous (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology X) :=
        Functor.isContinuous_of_iso e _ _
      exact (cechCapFunctor W).op_comp_isSheaf_of_isSheaf _ _ G.val.presheaf G.isSheaf
    have ht : Presheaf.IsSheaf (Opens.grothendieckTopology X)
        (alternatingCechSheafPresheafTerms U G p).presheaf := by
      apply PresheafOfModules.isSheaf_of_isLimit (limit.isLimit _)
      intro t
      exact hcap (alternatingCechIntersection U t.as)
    let M : X.Modules := ⟨alternatingCechSheafPresheafTerms U G p, ht⟩
    apply (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).isIso_unit_app_of_iso (X := M)
    exact Iso.refl _

end AlgebraicGeometry
