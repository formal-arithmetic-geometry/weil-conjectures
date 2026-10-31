/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Prescribed.PrescribedPointSystemData
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.Modules.HomSection

/-!
# Transporting a generating linear system to an open subscheme

Source: Stacks Project, Constructions, Tags 01NE and 01NF; Schemes, Tag 02V0.
(blueprint: lem-zl-generating-system-open-transport).
-/

@[expose] public section

universe u

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules MonoidalCategory

noncomputable section

attribute [local irreducible] tensorPullback prescribedPointRestrictedFamily

private noncomputable def tensorComparison {A B : Scheme.{u}} (g : A ⟶ B) :
    tensorPullback g ≅ Scheme.Modules.pullback g :=
  (Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
    (pullbackPushforwardAdjunction g)

private theorem tensorUnit_eq {A B : Scheme.{u}} (g : A ⟶ B) (M : B.Modules) :
    tensorSectionsUnit g M =
      (show Γ(M, ⊤) ⟶ Γ((tensorPullback g).obj M, ⊤) from
        ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app M).app ⊤) := by
  unfold tensorSectionsUnit
  have hi : (homOfLE g.preimage_top.ge).op = 𝟙 (op (⊤ : A.Opens)) := rfl
  erw [hi, ((tensorPullback g).obj M).presheaf.map_id, Category.comp_id]

private theorem comparison_unit {A B : Scheme.{u}} (g : A ⟶ B) (M : B.Modules)
    (v : Γ(M, ⊤)) :
    ((tensorComparison g).app M).hom.app ⊤ (tensorSectionsUnit g M v) = pullbackΓ g M v := by
  rw [tensorUnit_eq, pullbackΓ_def]
  exact congrArg (fun h ↦ h.app ⊤ v)
    ((Classical.choose (exists_tensorPullbackAdjunction g)).unit_leftAdjointUniq_hom_app
      (pullbackPushforwardAdjunction g) M)

end

end AlgebraicGeometry
