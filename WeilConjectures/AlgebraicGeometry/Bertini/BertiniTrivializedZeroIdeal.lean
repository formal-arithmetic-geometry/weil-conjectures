/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Bertini.BertiniUniversalFamily
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.AlgebraicGeometry.Modules.HomSection

/-!
# The equation of a trivialized Bertini zero scheme

Source: Stacks Project, More on Morphisms, Tag 0G4F, affine incidence charts.
-/

@[expose] public section

universe u

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry

open Scheme.Modules

private noncomputable def tensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorPullback f ≅ Scheme.Modules.pullback f :=
  (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)

attribute [local irreducible] tensorPullback tensorPullbackObj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorUnit_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    tensorSectionsUnit f M =
      (show Γ(M, ⊤) ⟶ Γ((tensorPullback f).obj M, ⊤) from
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).app ⊤) := by
  unfold tensorSectionsUnit
  have hi : (homOfLE f.preimage_top.ge).op = 𝟙 (op (⊤ : X.Opens)) := rfl
  erw [hi, ((tensorPullback f).obj M).presheaf.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry
