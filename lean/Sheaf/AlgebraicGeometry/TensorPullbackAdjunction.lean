/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsAdjunction
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TopologicalPullback

/-!
# The tensor-formula pullback of modules is left adjoint to pushforward

Source: Stacks Project, Tags 008X, 0095, 0096
(blueprint: lem-pc-module-pullback-adjunction).
-/

@[expose] public section

universe w

open CategoryTheory TopologicalSpace Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{w}} (g : X ⟶ Y)

/-- The canonical Hom bijection `Hom(P_g G, F) ≃ Hom(G, g_* F)` of Stacks 0096 is an
adjunction `tensorPullback g ⊣ pushforward g`. The adjunction is pinned to the canonical
composite by its unit: on a section `m` of `G` over `V` it is `θ(1 ⊗ η_G(m))`, where `η` is the
unit of the inverse-image/direct-image adjunction of abelian sheaves and `θ` is the
sheafification of the sectionwise tensor product.
Source: Stacks, Tag 0096 (blueprint: lem-pc-module-pullback-adjunction).
Proof: by the change-of-rings adjunction (Tag 008A), `Hom_{O_X}(P_g G, F)` is
`Hom_{g⁻¹O_Y}(g⁻¹G, F)` via `u ↦ (m ↦ u(1 ⊗ m))`. By the inverse-image/direct-image module
adjunction (Tag 008Y) this is `Hom_{O_Y}(G, g_* F)`, where `O_Y` acts on `g_* F` through
`ρ ∘ η_{O_Y}`. Since `ρ` is adjoint to `g^♯`, `ρ_{g⁻¹V} ∘ η_{O_Y,V} = g^♯_V`, so this is the
pushforward module. The composite bijection is natural in both modules, and its unit is
the stated sectionwise formula. -/
theorem exists_tensorPullbackAdjunction :
    ∃ adj : tensorPullback g ⊣ pushforward g,
      ∀ (G : Y.Modules) (V : (Opens Y)ᵒᵖ) (m : G.val.obj V),
        (adj.unit.app G).val.app V m =
          ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
            (SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap g)
              (TopCat.Sheaf.inverseImageModule g.base Y.sheaf G))).app
            ((Opens.map g.base).op.obj V)
            ((1 : X.sheaf.obj.obj ((Opens.map g.base).op.obj V)) ⊗ₜ[
              (TopCat.Sheaf.inverseImageRing g.base Y.sheaf).obj.obj ((Opens.map g.base).op.obj V),
              ((tensorPullbackRingMap g).hom.app ((Opens.map g.base).op.obj V)).hom]
              (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
                (Opens.map g.base) AddCommGrpCat.{w}
                (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app
                  ((SheafOfModules.toSheaf _).obj G)).hom.app V m)) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
