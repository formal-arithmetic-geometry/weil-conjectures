/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor

/-!
# The full long exact sequence of right derived functors

Source: Stacks Project, Derived Categories, Tag 015B, parts (1) and (2), specialized to
objects in degree zero.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory.Limits

namespace CategoryTheory.ShortComplex.ShortExact

/-- A short exact sequence gives a full long exact sequence of right derived functors,
including the initial monomorphism. Source: Stacks Project, Tag 015B (1)-(2). -/
theorem exists_rightDerived_full_long_exact
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [EnoughInjectives A] [Abelian B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex A} (hS : S.ShortExact) :
    ∃ δ : ∀ n : ℕ, (F.rightDerived n).obj S.X₃ ⟶ (F.rightDerived (n + 1)).obj S.X₁,
      Mono ((F.rightDerived 0).map S.f) ∧
      ∀ n : ℕ, (S.map (F.rightDerived n)).Exact ∧
        ∃ (w₁ : (F.rightDerived n).map S.g ≫ δ n = 0)
          (w₂ : δ n ≫ (F.rightDerived (n + 1)).map S.f = 0),
          (ShortComplex.mk _ _ w₁).Exact ∧ (ShortComplex.mk _ _ w₂).Exact := by
  obtain ⟨G, hG, _⟩ := exists_horseshoe_rightDerived_deltaFunctor F
  let P : (ℕ → A ⥤ B) → Prop := fun K ↦
    ∃ δ : ∀ n : ℕ, (K n).obj S.X₃ ⟶ (K (n + 1)).obj S.X₁,
      Mono ((K 0).map S.f) ∧
      ∀ n : ℕ, (∃ h : (K n).map S.f ≫ (K n).map S.g = 0,
          (ShortComplex.mk _ _ h).Exact) ∧
        ∃ (w₁ : (K n).map S.g ≫ δ n = 0)
          (w₂ : δ n ≫ (K (n + 1)).map S.f = 0),
          (ShortComplex.mk _ _ w₁).Exact ∧ (ShortComplex.mk _ _ w₂).Exact
  have hP : P G.F := by
    refine ⟨G.delta S hS, G.mono_zero S hS, ?_⟩
    intro n
    refine ⟨⟨(G.exact_middle S hS n).choose, (G.exact_middle S hS n).choose_spec⟩, ?_⟩
    exact ⟨(G.exact_right S hS n).choose, (G.exact_left S hS n).choose,
      (G.exact_right S hS n).choose_spec, (G.exact_left S hS n).choose_spec⟩
  have hP' : P (fun n : ℕ ↦ F.rightDerived n) := hG ▸ hP
  rcases hP' with ⟨δ, hm, hall⟩
  refine ⟨δ, hm, ?_⟩
  intro n
  rcases hall n with ⟨hmn, hrest⟩
  rcases hrest with ⟨w1, w2, hr, hl⟩
  refine ⟨?_, w1, w2, hr, hl⟩
  simpa only [ShortComplex.map] using hmn.choose_spec

end CategoryTheory.ShortComplex.ShortExact
