/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.Mathlib.Topology.Category.TopCat.Opens

/-!
# Tensor pullback of the structure sheaf

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The structure-sheaf map adjoint to `g♯` under the tensor pullback adjunction. -/
def tensorPullbackObjUnitToUnit {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (tensorPullback g).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _).symm
    (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The adjoint structure-sheaf map is an isomorphism, and its composite with the unit
is the original structure-sheaf map. -/
theorem tensorPullbackObjUnitToUnit_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    IsIso (tensorPullbackObjUnitToUnit g) ∧
      (Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
          (SheafOfModules.unit Y.ringCatSheaf) ≫
        (pushforward g).map (tensorPullbackObjUnitToUnit g) =
          SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  let adj := Classical.choose (exists_tensorPullbackAdjunction g)
  have he : adj.homEquiv _ _ (tensorPullbackObjUnitToUnit g) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    (adj.homEquiv _ _).apply_symm_apply _
  refine ⟨?_, ?_⟩
  · rw [isIso_iff_coyoneda_map_bijective]
    intro M
    rw [← (adj.homEquiv _ _).bijective.of_comp_iff',
      ← (SheafOfModules.unitHomEquiv _).bijective.of_comp_iff']
    convert! (SheafOfModules.bijective_pushforwardSections g.toRingCatSheafHom M).comp
      (SheafOfModules.unitHomEquiv _).bijective
    ext f : 1
    dsimp
    rw [SheafOfModules.pushforwardSections_unitHomEquiv]
    apply congrArg (SheafOfModules.unitHomEquiv ((pushforward g).obj M))
    rw [Adjunction.homEquiv_naturality_right, he]
    rfl
  · exact (adj.homEquiv_unit _ _ _).symm.trans he

end
end AlgebraicGeometry.Scheme.Modules
