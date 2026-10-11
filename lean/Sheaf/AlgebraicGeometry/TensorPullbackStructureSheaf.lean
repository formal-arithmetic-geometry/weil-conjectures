/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Tensor pullback of the structure sheaf

Source: Stacks Project, Modules, pullback and tensor product, Tags 0096 and 01CA
(blueprint: lem-weil-pbc-module-pullback-structure-sheaf).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- The structure-sheaf map adjoint to `g♯` under the tensor pullback adjunction.
Source: Stacks Project, Modules, Tag 0096
(blueprint: lem-weil-pbc-module-pullback-structure-sheaf). -/
def tensorPullbackObjUnitToUnit {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (tensorPullback g).obj (SheafOfModules.unit Y.ringCatSheaf) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  ((Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _).symm
    (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)

/-- The adjoint structure-sheaf map is an isomorphism, and its composite with the unit
is the original structure-sheaf map. Source: Stacks Project, Modules, Tags 0096 and 01CA
(blueprint: lem-weil-pbc-module-pullback-structure-sheaf).
Proof: on the inverse-image tensor formula, multiplication identifies
`O_X ⊗_{g⁻¹ O_Y} g⁻¹ O_Y` with `O_X`, with inverse `b ↦ b ⊗ 1`.
The balanced relation verifies that these maps are inverse. Under the adjunction,
this multiplication sends the unit section `1 ⊗ a` to `g♯(a)`, giving the stated
characterization and its uniqueness by the adjunction's Hom bijection. -/
theorem tensorPullbackObjUnitToUnit_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    IsIso (tensorPullbackObjUnitToUnit g) ∧
      (Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
          (SheafOfModules.unit Y.ringCatSheaf) ≫
        (pushforward g).map (tensorPullbackObjUnitToUnit g) =
          SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
