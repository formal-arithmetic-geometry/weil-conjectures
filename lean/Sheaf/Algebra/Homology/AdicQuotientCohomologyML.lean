/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: SHEAF group V4
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem

/-! # Finite comparison transfer for Mittag--Leffler towers

Source: Stacks Project, Tag 09C5.
(blueprint: lem-sfb-finite-triple-ml-transfer).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

/-- A finite comparison of two towers, allowing the comparison at each level to depend
on the finite triple of indices under consideration. -/
def FiniteTripleComparison (T : ℕᵒᵖ ⥤ Type u) (U : ℕᵒᵖ ⥤ Type v) : Prop :=
  ∀ {n m t : ℕᵒᵖ} (f : m ⟶ n) (g : t ⟶ m),
    ∃ (en : U.obj n ≃ T.obj n) (em : U.obj m ≃ T.obj m)
      (et : U.obj t ≃ T.obj t),
      (∀ x, en (U.map f x) = T.map f (em x)) ∧
      (∀ x, en (U.map (g ≫ f) x) = T.map (g ≫ f) (et x))

/-- A finite-triple comparison transfers the Mittag--Leffler condition. -/
theorem isMittagLeffler_of_finiteTripleComparison
    {T : ℕᵒᵖ ⥤ Type u} {U : ℕᵒᵖ ⥤ Type v}
    (h : FiniteTripleComparison T U) (hU : U.IsMittagLeffler) : T.IsMittagLeffler := by
  apply (isMittagLeffler_iff_subset_range_comp T).mpr
  intro n
  obtain ⟨m, f, hm⟩ := (isMittagLeffler_iff_subset_range_comp U).mp hU n
  refine ⟨m, f, fun {t} g ↦ ?_⟩
  obtain ⟨en, em, et, hem, het⟩ := h f g
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hm g (Set.mem_range_self (em.symm x))
  refine ⟨et y, ?_⟩
  calc
    T.map (g ≫ f) (et y) = en (U.map (g ≫ f) y) := (het y).symm
    _ = en (U.map f (em.symm x)) := congrArg en hy
    _ = T.map f (em (em.symm x)) := hem (em.symm x)
    _ = T.map f x := by rw [em.apply_symm_apply]

end CategoryTheory.Functor
