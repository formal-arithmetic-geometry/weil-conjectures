/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Pro-zero middle terms in a tower of distinguished triangles

Source: Stacks Project, Derived Categories, Tag 0G3A, zero-valued specialization.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

/-- In an inverse system of distinguished triangles, simultaneous eventual vanishing of the
first and third transition maps implies eventual vanishing of the middle transition maps.
Index `n : ℕ` denotes level `n + 1` of the positive-integer tower.
Source: Stacks Project, Derived Categories, Tag 0G3A, zero-valued specialization. -/
theorem proZero_middle_of_distinguished_tower
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ i : ℤ, (shiftFunctor D i).Additive] [Pretriangulated D] [IsTriangulated D]
    (T : ℕᵒᵖ ⥤ Triangle D)
    (hT : ∀ n : ℕ, T.obj (Opposite.op n) ∈ distTriang D)
    (hAC : ∀ n : ℕ, ∃ (k : ℕ) (hnk : n ≤ k),
      (T.map (homOfLE hnk).op).hom₁ = 0 ∧
      (T.map (homOfLE hnk).op).hom₃ = 0) :
    ∀ n : ℕ, ∃ (k : ℕ) (hnk : n ≤ k), (T.map (homOfLE hnk).op).hom₂ = 0 := by
  intro n
  obtain ⟨m, hnm, ha, _⟩ := hAC n
  obtain ⟨h, hh⟩ := Triangle.yoneda_exact₂ _ (hT m)
    (T.map (homOfLE hnm).op).hom₂ (by
      rw [(T.map (homOfLE hnm).op).comm₁, ha, zero_comp])
  obtain ⟨k, hmk, _, hc⟩ := hAC m
  refine ⟨k, hnm.trans hmk, ?_⟩
  have hcomp : (homOfLE (hnm.trans hmk)).op =
      (homOfLE hmk).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
  rw [hcomp, T.map_comp, comp_hom₂, hh, ← Category.assoc,
    ← (T.map (homOfLE hmk).op).comm₂, hc, comp_zero, zero_comp]

end CategoryTheory.Pretriangulated
