/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Projective


/-! # Schanuel's lemma
## References

* Stacks Project, Algebra, Tag 00O3
-/

@[expose] public section

namespace Module

universe u v₁ v₂ v₃ v₄ v₅

/-- Schanuel's lemma for two projective presentations. -/
theorem schanuel (R : Type u) [CommRing R]
    (K : Type v₁) (L : Type v₂) (P₁ : Type v₃) (P₂ : Type v₄) (M : Type v₅)
    [AddCommGroup K] [AddCommGroup L] [AddCommGroup P₁]
    [AddCommGroup P₂] [AddCommGroup M]
    [Module R K] [Module R L] [Module R P₁] [Module R P₂] [Module R M]
    (c₁ : K →ₗ[R] P₁) (p₁ : P₁ →ₗ[R] M)
    (c₂ : L →ₗ[R] P₂) (p₂ : P₂ →ₗ[R] M)
    (hc₁ : Function.Injective c₁) (h₁ : Function.Exact c₁ p₁)
    (hp₁ : Function.Surjective p₁)
    (hc₂ : Function.Injective c₂) (h₂ : Function.Exact c₂ p₂)
    (hp₂ : Function.Surjective p₂)
    [Module.Projective R P₁] [Module.Projective R P₂] :
    Nonempty ((K × P₂) ≃ₗ[R] (L × P₁)) := by
  classical
  let N := LinearMap.ker (p₁.coprod p₂)
  let q₁ : N →ₗ[R] P₁ := (LinearMap.fst R P₁ P₂).comp N.subtype
  let q₂ : N →ₗ[R] P₂ := (LinearMap.snd R P₁ P₂).comp N.subtype
  let i₁ : K →ₗ[R] N := ((LinearMap.inl R P₁ P₂).comp c₁).codRestrict N (by
    intro k
    change p₁ (c₁ k) + p₂ 0 = 0
    simp [h₁.apply_apply_eq_zero])
  let i₂ : L →ₗ[R] N := ((LinearMap.inr R P₁ P₂).comp c₂).codRestrict N (by
    intro l
    change p₁ 0 + p₂ (c₂ l) = 0
    simp [h₂.apply_apply_eq_zero])
  have hi₁ : Function.Injective i₁ := by
    intro k k' h
    apply hc₁
    exact congrArg (fun n : N ↦ n.val.1) h
  have hi₂ : Function.Injective i₂ := by
    intro l l' h
    apply hc₂
    exact congrArg (fun n : N ↦ n.val.2) h
  have he₁ : Function.Exact i₁ q₂ := by
    intro n
    constructor
    · intro hn
      have hn₂ : n.val.2 = 0 := hn
      have hn₁ : p₁ n.val.1 = 0 := by
        have h := n.property
        change p₁ n.val.1 + p₂ n.val.2 = 0 at h
        simpa [hn₂] using h
      obtain ⟨k, hk⟩ := (h₁ n.val.1).mp hn₁
      refine ⟨k, ?_⟩
      apply Subtype.ext
      exact Prod.ext hk hn₂.symm
    · rintro ⟨k, rfl⟩
      rfl
  have he₂ : Function.Exact i₂ q₁ := by
    intro n
    constructor
    · intro hn
      have hn₁ : n.val.1 = 0 := hn
      have hn₂ : p₂ n.val.2 = 0 := by
        have h := n.property
        change p₁ n.val.1 + p₂ n.val.2 = 0 at h
        simpa [hn₁] using h
      obtain ⟨l, hl⟩ := (h₂ n.val.2).mp hn₂
      refine ⟨l, ?_⟩
      apply Subtype.ext
      exact Prod.ext hn₁.symm hl
    · rintro ⟨l, rfl⟩
      rfl
  have hq₁ : Function.Surjective q₁ := by
    intro u
    obtain ⟨v, hv⟩ := hp₂ (-p₁ u)
    refine ⟨⟨(u, v), ?_⟩, rfl⟩
    change p₁ u + p₂ v = 0
    rw [hv, add_neg_cancel]
  have hq₂ : Function.Surjective q₂ := by
    intro v
    obtain ⟨u, hu⟩ := hp₁ (-p₂ v)
    refine ⟨⟨(u, v), ?_⟩, rfl⟩
    change p₁ u + p₂ v = 0
    rw [hu, neg_add_cancel]
  obtain ⟨s₁, hs₁⟩ := q₁.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hq₁)
  obtain ⟨s₂, hs₂⟩ := q₂.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hq₂)
  let e₁ := (he₁.splitSurjectiveEquiv hi₁ ⟨s₂, hs₂⟩).val
  let e₂ := (he₂.splitSurjectiveEquiv hi₂ ⟨s₁, hs₁⟩).val
  exact ⟨e₁.symm.trans e₂⟩

end Module
