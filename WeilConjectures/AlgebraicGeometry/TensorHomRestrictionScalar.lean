/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import all WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison

/-! # Restricting a tensor-Hom transpose with prescribed scalar values

## References

* [Stacks Project, Tag 01CN](https://stacks.math.columbia.edu/tag/01CN)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules

local instance localInst_TensorHomRestrictionScalar_1
    {X : Scheme.{u}} (M : X.Modules) {U W : X.Opens} (h : W ≤ U) :
    SMul ((SheafOfModules.unit X.ringCatSheaf).val.obj (op W))
      ((ModuleCat.restrictScalars (X.ringCatSheaf.obj.map (homOfLE h).op).hom).obj
        (M.val.obj (op W))) :=
  inferInstanceAs (SMul (X.sheaf.obj.obj (op W)) (M.val.obj (op W)))

set_option maxHeartbeats 600000 in
-- Normalizing the slice and scheme restriction comparisons requires extra elaboration fuel.
set_option backward.isDefEq.respectTransparency false in
/-- Transposition sends a local scalar multiple of a Hom section to multiplication
followed by the local morphism. No coherence or ideal-power hypothesis is required. -/
theorem tensorHom_restriction_of_local_scalar
    {X : Scheme.{u}} (A H F : X.Modules)
    (ι : A ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (s : (SheafOfModules.homObj (R := X.sheaf) H F).val.obj (op U))
    (α : A ⟶ SheafOfModules.homObj (R := X.sheaf) H F)
    (hα : ∀ (W : X.Opens) (h : W ≤ U) (a : A.val.obj (op W)),
      α.val.app (op W) a = ι.val.app (op W) a •
        (SheafOfModules.homObj (R := X.sheaf) H F).val.map (homOfLE h).op s) :
    letI : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    ∀ (β : A ⊗ H ⟶ F),
      (∀ (W : X.Opens) (a : A.val.obj (op W)) (g : H.val.obj (op W)),
        β.val.app (op W)
          ((SheafOfModules.tensorObjIsoSheafification A H).inv.val.app (op W)
            (((PresheafOfModules.sheafificationAdjunction.{u}
              (𝟙 X.ringCatSheaf.obj)).unit.app (A.val ⊗ H.val)).app (op W)
                (a ⊗ₜ[X.sheaf.obj.obj (op W)] g))) =
          (α.val.app (op W) a).app (op (Over.mk (𝟙 W))) g) →
      (restrictFunctor U.ι).map β =
        (restrictFunctor U.ι).map (ι ▷ H ≫ (λ_ H).hom) ≫
          (overFunctorEquiv U).inv.app H ≫
          (overEquiv U).functor.map (⟨s⟩ : H.over U ⟶ F.over U) ≫
          (overFunctorEquiv U).hom.app F := by
  intro β hβ
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let j := U.ι
  obtain ⟨e, he⟩ := exists_restriction_tensor_comparison j A H
  apply (cancel_epi e.inv).mp
  apply tensor_hom_ext
  intro V a g
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  have hev := he V a g
  change e.inv.app V (tmulSection a g) =
    tmulSection (M := A) (N := H) (U := j ''ᵁ V) a g at hev
  rw [hev]
  let W : X.Opens := j ''ᵁ V
  have hW : W ≤ U := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hb := hβ W a g
  change β.app W (tmulSection a g) = _ at hb
  erw [hb]
  rw [hα W hW a]
  change (((show X.sheaf.obj.obj (op W) from ι.app W a) •
    PresheafOfModules.restrictOverMap (homOfLE hW) s).app
    (op (Over.mk (𝟙 W)))) g = _
  rw [PresheafOfModules.smul_app]
  erw [ModuleCat.comp_apply, PresheafOfModules.sectionsSMul_app_apply,
    PresheafOfModules.overSections_coe_apply]
  have hid (r : X.sheaf.obj.obj (op W)) :
      X.sheaf.obj.map (𝟙 (op W)) r = r := by simp
  erw [hid]
  change (show Γ(X, W) from ι.app W a) • (s.app (op (Over.mk (homOfLE hW)))) g = _
  have hm : ((restrictFunctor U.ι).map (ι ▷ H ≫ (λ_ H).hom)).app V
      (tmulSection (M := A) (N := H) (U := W) a g) =
        (show Γ(X, W) from ι.app W a) • (show Γ(H, W) from g) := by
    change (ι ▷ H ≫ (λ_ H).hom).app W (tmulSection a g) = _
    rw [Hom.comp_app, ConcreteCategory.comp_apply,
      whiskerRight_app_tmulSection]
    exact leftUnitor_hom_app_tmulSection' (M := H) (ι.app W a) g
  rw [hm]
  change (show Γ(X, W) from ι.app W a) • (s.app (op (Over.mk (homOfLE hW)))) g =
    (s.app (op (Over.mk (homOfLE hW))))
      ((show Γ(X, W) from ι.app W a) • (show Γ(H, W) from g))
  exact ((s.app (op (Over.mk (homOfLE hW)))).hom.map_smul _ _).symm

end AlgebraicGeometry.Scheme.Modules
