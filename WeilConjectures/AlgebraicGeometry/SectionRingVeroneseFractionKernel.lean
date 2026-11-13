/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractionMap
public import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation
import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseNumeratorTransition

/-! # The kernel of the explicit map on Veronese numerator sections

## References

* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01Q1](https://stacks.math.columbia.edu/tag/01Q1)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

private def rel (R : Type*) [CommRing R] (M : ℕ → Type*)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (tr : ∀ n b : ℕ, M n →ₗ[R] M (n + b)) : Submodule R (⨁ n, M n) :=
  Submodule.span R {z | ∃ n b t, z = of M n t - of M (n + b) (tr n b t)}

private theorem rel_normal (R : Type*) [CommRing R] (M : ℕ → Type*)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (tr : ∀ n b : ℕ, M n →ₗ[R] M (n + b)) (z : ⨁ n, M n) :
    ∃ n t, z - of M n t ∈ rel R M tr := by
  classical
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | of n t => exact ⟨n, t, by simp⟩
  | add x y hx hy =>
    obtain ⟨n, t, ht⟩ := hx
    obtain ⟨m, u, hu⟩ := hy
    have htn : of M n t - of M (n + m) (tr n m t) ∈ rel R M tr :=
      Submodule.subset_span ⟨n, m, t, rfl⟩
    have hun : of M m u - of M (m + n) (tr m n u) ∈ rel R M tr :=
      Submodule.subset_span ⟨m, n, u, rfl⟩
    have hy' : ∃ u' : M (m + n), y - of M (m + n) u' ∈ rel R M tr :=
      ⟨tr m n u, by simpa only [sub_add_sub_cancel] using Submodule.add_mem _ hu hun⟩
    rw [Nat.add_comm m n] at hy'
    obtain ⟨u', hu'⟩ := hy'
    refine ⟨n + m, tr n m t + u', ?_⟩
    have hx' : x - of M (n + m) (tr n m t) ∈ rel R M tr := by
      simpa only [sub_add_sub_cancel] using Submodule.add_mem _ ht htn
    simpa only [map_add, add_sub_add_comm] using Submodule.add_mem _ hx' hu'

private theorem kernel_rel (R : Type*) [CommRing R] (M : ℕ → Type*)
    [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
    (tr : ∀ n b : ℕ, M n →ₗ[R] M (n + b)) {G : Type*} [AddCommGroup G] (f : (⨁ n, M n) →+ G)
    (htr : ∀ n b t, f (of M n t) = f (of M (n + b) (tr n b t)))
    (hkill : ∀ n t, f (of M n t) = 0 → ∃ b, tr n b t = 0) :
    (rel R M tr).toAddSubgroup = f.ker := by
  have hforward : (rel R M tr).toAddSubgroup ≤ f.ker := by
    intro z hz
    change z ∈ Submodule.span R _ at hz
    have hz' : ∀ r : R, f (r • z) = 0 := by
      induction hz using Submodule.span_induction with
      | mem x hx =>
        rintro r
        obtain ⟨n, b, t, rfl⟩ := hx
        rw [smul_sub, ← DirectSum.of_smul, ← DirectSum.of_smul,
          ← LinearMap.map_smul, map_sub, htr, sub_self]
      | zero => intro r; simp
      | add x y hx hy ihx ihy =>
        intro r
        rw [smul_add, map_add, ihx, ihy, zero_add]
      | smul a x hx ih =>
        intro r
        rw [smul_smul]
        exact ih (r * a)
    change f z = 0
    simpa only [one_smul] using hz' 1
  apply le_antisymm hforward
  intro z hz
  obtain ⟨n, t, ht⟩ := rel_normal R M tr z
  have hft : f (of M n t) = 0 := by
    have h := hforward ht
    change f (z - of M n t) = 0 at h
    change f z = 0 at hz
    rw [map_sub, hz, zero_sub, neg_eq_zero] at h
    exact h
  obtain ⟨b, hb⟩ := hkill n t hft
  have hmem : of M n t ∈ rel R M tr := by
    have h : of M n t - of M (n + b) (tr n b t) ∈ rel R M tr :=
      Submodule.subset_span ⟨n, b, t, rfl⟩
    simpa only [hb, map_zero, sub_zero] using h
  change z ∈ rel R M tr
  simpa only [sub_add_cancel] using Submodule.add_mem _ ht hmem

private theorem loc_transition {A : Type*} [CommRing A] (s a : A) (n b : ℕ) :
    Localization.mk a (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s) =
      (Localization.mk (a * s ^ b) ⟨s ^ (n + b), ⟨n + b, rfl⟩⟩ :
        Localization (Submonoid.powers s)) := by
  apply Localization.mk_eq_mk_iff.mpr
  apply Localization.r_of_eq
  simp only [pow_add]
  ring

private theorem loc_kill {A : Type*} [CommRing A] (s a : A) (n : ℕ)
    (h : Localization.mk a (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s) =
      (0 : Localization (Submonoid.powers s))) : ∃ b, a * s ^ b = 0 := by
  rw [Localization.mk_eq_mk'] at h
  obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff _ _).mp h
  obtain ⟨b, hb⟩ := c.property
  refine ⟨b, ?_⟩
  simpa only [← hb, mul_comm] using hc

/-- The transition relations are exactly the kernel of the explicitly constructed fraction map.
-/
theorem sectionRingVeroneseFractionMap_kernel
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    (sectionFractionRelations (L.tensorPow d) (𝟙_ X.Modules) (s.val d)).toAddSubgroup =
      (sectionRingVeroneseFractionMap X L d s).ker := by
  let M : ℕ → Type u := fun n ↦ Γ((𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow n, ⊤)
  let tr : ∀ n b : ℕ, M n →ₗ[Γ(X, ⊤)] M (n + b) := fun n b ↦
    { toAddHom := ((mulTensorPowSection
        (homOfGlobalSection (L.tensorPow d) (s.val d)) (𝟙_ X.Modules) n b).app ⊤).hom
      map_smul' := fun r t ↦ Hom.app_smul _ r t }
  let f := sectionRingVeroneseFractionMap X L d s
  have hval (n : ℕ) (t : M n) :
      (f (DirectSum.of M n t)).val =
        Localization.mk (sectionRingVeroneseNumerator X L d n t).val
          (⟨s.val ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s.val) := by
    simp only [f, sectionRingVeroneseFractionMap]
    change Localization.mk _ _ = _
    have ht : (DirectSum.of M n t) n = t := by
      apply DirectSum.of_eq_same
    rw [ht]
    simp
  have htr (n b : ℕ) (t : M n) :
      f (DirectSum.of M n t) = f (DirectSum.of M (n + b) (tr n b t)) := by
    apply HomogeneousLocalization.val_injective
    rw [hval, hval]
    change _ = Localization.mk
      (sectionRingVeroneseNumerator X L d (n + b)
        ((mulTensorPowSection (homOfGlobalSection (L.tensorPow d) (s.val d))
          (𝟙_ X.Modules) n b).app ⊤ t)).val _
    rw [sectionRingVeroneseNumerator_transition]
    exact loc_transition s.val _ n b
  have hkill (n : ℕ) (t : M n) (ht : f (DirectSum.of M n t) = 0) :
      ∃ b, tr n b t = 0 := by
    have ht' := congrArg HomogeneousLocalization.val ht
    rw [hval, HomogeneousLocalization.val_zero] at ht'
    obtain ⟨b, hb⟩ := loc_kill s.val _ n ht'
    refine ⟨b, ?_⟩
    have hinj : Function.Injective (sectionRingVeroneseNumerator X L d (n + b)) := by
      classical
      intro a c hac
      have hac' := congrArg Subtype.val hac
      change DirectSum.of (SectionRingComponent L) ((n + b) • d)
        ((sectionRingVeroneseNumeratorIso X L d (n + b)).inv.app ⊤ a) =
          DirectSum.of (SectionRingComponent L) ((n + b) • d)
            ((sectionRingVeroneseNumeratorIso X L d (n + b)).inv.app ⊤ c) at hac'
      have hi := DirectSum.of_injective (β := SectionRingComponent L) ((n + b) • d) hac'
      exact (ConcreteCategory.bijective_of_isIso
        ((sectionRingVeroneseNumeratorIso X L d (n + b)).inv.app ⊤)).1 hi
    apply hinj
    apply Subtype.ext
    change (sectionRingVeroneseNumerator X L d (n + b)
      ((mulTensorPowSection (homOfGlobalSection (L.tensorPow d) (s.val d))
        (𝟙_ X.Modules) n b).app ⊤ t)).val =
          (sectionRingVeroneseNumerator X L d (n + b) 0).val
    rw [sectionRingVeroneseNumerator_transition, hb, map_zero]
    rfl
  classical
  exact kernel_rel Γ(X, ⊤) M tr f htr hkill

end AlgebraicGeometry.Scheme.Modules
