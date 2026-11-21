/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge

import WeilConjectures.CategoryTheory.HypercohomologyLeftEdgeCanonical

/-! # The cocycle equation for the hypercohomology left edge

Source: Stacks Project, derived.tex, Tag 015J, the second spectral sequence.
-/

@[expose] public section

universe uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- The derived unit and the left edge send a cocycle to its quotient after `G`.
Source: Stacks Project, Tag 015J. -/
theorem cochainHypercohomologyLeftEdge_cocycle
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]
    (K : CochainComplex B ℕ) (n : ℕ)
    (c : G.obj (K.cycles n) ⟶
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).cycles n)
    (hc : c ≫ ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles n =
      G.map (K.iCycles n)) :
    c ≫ ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ n ≫
        G.cochainHypercohomologyLeftEdge K n = G.map (K.homologyπ n) := by
  let T := ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
  let c₀ := T.liftCycles (G.map (K.iCycles n)) (n + 1) (by simp)
    (by
      change G.map (K.iCycles n) ≫ G.map (K.d n (n + 1)) = 0
      rw [← G.map_comp, K.iCycles_d, G.map_zero])
  have hc₀ : c₀ ≫ T.iCycles n = G.map (K.iCycles n) := by
    dsimp [c₀]
    exact T.liftCycles_i _ _ _ _
  have hcc₀ : c = c₀ := by
    apply (cancel_mono (T.iCycles n)).1
    exact hc.trans hc₀.symm
  rw [hcc₀]
  exact cochainHypercohomologyLeftEdge_canonical G K n

end CategoryTheory.Functor
