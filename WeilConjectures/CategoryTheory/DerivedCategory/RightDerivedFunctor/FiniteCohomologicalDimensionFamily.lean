/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FiniteCohomologicalDimension

/-!
# Pointwise finite cohomological dimension, measured in varying categories

This is a variant of `HomologicalComplex.Acyclic.map_of_rightAcyclic_of_forall_isZero` in which
the jointly conservative family of functors `r i : D ⥤ E i` measuring the pointwise
cohomological dimension takes values in categories `E i` depending on `i`: for instance the
pullbacks of étale sheaves to the geometric points `Spec Ω ⟶ Y`, whose targets depend on the
point.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [HasInjectiveResolutions C]
  [Abelian D]

/-- A left exact additive functor `F : C ⥤ D` of *pointwise* finite cohomological dimension sends
an exact cochain complex `K` whose terms are all `F`-acyclic to an exact complex `F(K)`, with no
boundedness assumption on `K`. Pointwise finite cohomological dimension is measured by a jointly
conservative family of functors `r i : D ⥤ E i` preserving monomorphisms, with values in
categories `E i` which may depend on `i`: `r i (R^q F X) = 0` for every `X` and every `q > d i`.
This generalises `HomologicalComplex.Acyclic.map_of_rightAcyclic_of_forall_isZero`, with the
same dimension shifting proof. -/
theorem Acyclic.map_of_rightAcyclic_of_forall_isZero_of_family {K : CochainComplex C ℤ}
    (hK : K.Acyclic) (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {ι : Type*} {E : ι → Type*} [∀ i, Category* (E i)] [∀ i, HasZeroMorphisms (E i)]
    (r : ∀ i, D ⥤ E i) [∀ i, (r i).PreservesMonomorphisms]
    (hr : ∀ M : D, (∀ i, IsZero ((r i).obj M)) → IsZero M)
    (d : ι → ℕ) (hF : ∀ i (X : C) (q : ℕ), d i < q → IsZero ((r i).obj ((F.rightDerived q).obj X)))
    (hK' : ∀ n, F.rightAcyclic (K.X n)) :
    ((F.mapHomologicalComplex _).obj K).Acyclic := by
  have hS (n : ℤ) := (hK (n + 1)).shortExact_cyclesShortComplex (i := n) (by simp)
  -- dimension shifting: `r i (R^{q+1} F(Zⁿ)) = 0` as soon as `d i ≤ q + k`, by induction on `k`
  have hZ' (i : ι) (k : ℕ) : ∀ (n : ℤ) (q : ℕ), d i ≤ q + k →
      IsZero ((r i).obj ((F.rightDerived (q + 1)).obj (K.cycles n))) := by
    induction k with
    | zero => exact fun n q hq ↦ hF i _ _ (by lia)
    | succ k ih =>
      intro n q hq
      obtain ⟨δ, w₁, w₂, h, -⟩ := (hS (n - 1)).exists_rightDerived_δ_exact F (q + 1)
      have : Mono δ := h.mono_g ((hK' (n - 1) q).eq_of_src _ _)
      have h' : IsZero ((r i).obj ((F.rightDerived (q + 1)).obj (K.cycles (n - 1 + 1)))) :=
        IsZero.of_mono ((r i).map δ) (ih (n - 1) (q + 1) (by lia))
      rwa [sub_add_cancel] at h'
  have hZ (n : ℤ) : F.rightAcyclic (K.cycles n) := fun q ↦
    hr _ fun i ↦ hZ' i (d i) n q (by lia)
  intro m
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by lia⟩
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp; lia)]
  let T := ShortComplex.mk (F.map (K.iCycles (n + 1))) (F.map (K.d (n + 1) (n + 2)))
    (by rw [← F.map_comp, iCycles_d, F.map_zero])
  have hT : IsLimit (KernelFork.ofι T.f T.zero) :=
    isLimitForkMapOfIsLimit' F _ (K.cyclesIsKernel (n + 1) (n + 2) (by simp; lia))
  have : Epi (F.map (K.toCycles n (n + 1))) :=
    ((hS n).map_of_rightAcyclic (hZ n)).epi_g
  let φ : ((F.mapHomologicalComplex _).obj K).sc' n (n + 1) (n + 2) ⟶ T :=
    { τ₁ := F.map (K.toCycles n (n + 1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [T, ← F.map_comp] }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ hT

end HomologicalComplex
