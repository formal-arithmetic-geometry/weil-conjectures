/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCounitShifts
import WeilConjectures.AlgebraicGeometry.OpenPinnedTensorCounitTransport

/-! # Pinned counit restriction on homotopy complexes
Source: Stacks Project, Tags 08DW, 08HY and 0D5S.
(blueprint: lem-pc-open-pinned-counit-homotopy-restriction). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

private theorem counit_path_glue {C : Type*} [Category C]
    {A B C₀ D E I J H K : C}
    (s : A ⟶ B) (c : B ⟶ C₀) (e : C₀ ⟶ D) (a : E ≅ D)
    (v : E ⟶ I) (ε : D ⟶ J) (b : J ⟶ H) (z : H ⟶ I)
    (δ : C₀ ⟶ K) (l : K ⟶ I) (out : A ⟶ I)
    (ht : v = a.hom ≫ ε ≫ b ≫ z)
    (hc : e ≫ ε ≫ b ≫ z = δ ≫ l)
    (hs : s ≫ c ≫ δ ≫ l = out) :
    s ≫ c ≫ e ≫ a.inv ≫ v = out := by
  rw [ht]
  simp only [Iso.inv_hom_id_assoc]
  rw [hc]
  exact hs

end AlgebraicGeometry
