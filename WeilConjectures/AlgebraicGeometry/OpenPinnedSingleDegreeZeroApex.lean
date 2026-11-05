/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PinnedSingleBaseChangeShift
import WeilConjectures.AlgebraicGeometry.IsomorphicSingleTensorCounit
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangePasting

/-! # Invariance of the pinned single comparison under an isomorphic apex
Source: Stacks Project, Tags 08HY and 08IB.
(blueprint: lem-pc-open-pinned-single-degree-zero-apex). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

private theorem assemble_apex
    {C : Type*} [Category C] {A B B' D E F G H : C}
    (b : A ⟶ B) (x : B ⟶ D) (k₁ : B ⟶ B') (k₂ : D ⟶ E)
    (d : B' ⟶ F) (c : F ⟶ B') (y : B' ⟶ E) (t : E ⟶ H)
    (b₀ : A ⟶ G) (u : G ⟶ F) (z : G ⟶ H)
    (hn : x ≫ k₂ = k₁ ≫ y) (hp : b ≫ k₁ ≫ d = b₀ ≫ u)
    (hd : d ≫ c = 𝟙 B') (hc : u ≫ c ≫ y ≫ t = z) :
    b ≫ x ≫ k₂ ≫ t = b₀ ≫ z := by
  calc
    _ = b ≫ k₁ ≫ y ≫ t := by rw [← Category.assoc x k₂, hn, Category.assoc]
    _ = b ≫ k₁ ≫ d ≫ c ≫ y ≫ t := by rw [← Category.assoc d c, hd, Category.id_comp]
    _ = b₀ ≫ u ≫ c ≫ y ≫ t := by rw [reassoc_of% hp]
    _ = _ := by rw [hc]

end AlgebraicGeometry
