/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# Annihilators of finite modules localized away from an element

Source: Stacks Project, Algebra, Lemma 07T8, second assertion specialized to localization
(blueprint: lem-weil-pbc-annihilator-localization-finite).
-/

@[expose] public section

universe u v

namespace Module

/-- The annihilator of a finite module commutes with localization away from an element.
Source: Stacks Project, Algebra, Lemma 07T8, second assertion, for the flat map `A → A_f`.
(blueprint: lem-weil-pbc-annihilator-localization-finite)

Proof (the node's direct fraction argument):
1. Every `a` in `Ann_A(M)` kills each fraction `m/f^e`, since its product is `am/f^e = 0`.
   Thus the ideal extended along `A → A_f` is contained in `Ann_{A_f}(M_f)`.
   This uses def-weil-ring-localization-away and def-weil-pbc-module-localization-away.
2. Choose finite generators `m_1, …, m_r` of `M` (def-weil-finitely-generated-module).
   An element kills `M` exactly when it kills every generator. The `m_k/1` generate `M_f`,
   since `m/f^e = (1/f^e)(m/1)` and localization is linear, so the same criterion holds there
   (def-weil-pbc-module-localization-away).
3. Write an element of `Ann_{A_f}(M_f)` as `a/f^e`. For each generator its product is zero,
   so the localization equality criterion gives `f^{n_k} a m_k = 0` for some `n_k`.
   Take the maximum `n` of these finitely many exponents, or `n = 0` for no generators.
   Then `f^n a` kills all generators and hence `M`, while
   `a/f^e = (1/f^{n+e})(f^n a/1)` belongs to the extended annihilator ideal.
   This uses def-weil-ring-localization-away and def-weil-pbc-module-localization-away.
4. The two ideal inclusions give the asserted equality. -/
theorem annihilator_localization_away_of_finite
    (A : Type u) [CommRing A] (f : A) (M : Type v)
    [AddCommGroup M] [Module A M] [Module.Finite A M] :
    Module.annihilator (Localization.Away f) (LocalizedModule.Away f M) =
      Ideal.map (algebraMap A (Localization.Away f)) (Module.annihilator A M) := by
  classical
  let S := Submonoid.powers f
  apply le_antisymm
  · intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
    have hkill : ∀ m : M, ∃ t : S, (t : A) • (a • m) = 0 := by
      intro m
      have h := Module.mem_annihilator.mp hx (LocalizedModule.mk m (1 : S))
      rw [← Localization.mk_eq_mk', LocalizedModule.mk_smul_mk] at h
      have heq : LocalizedModule.mk (a • m) (s * 1) =
          LocalizedModule.mk (0 : M) (1 : S) := by simpa using h
      obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.mp heq
      exact ⟨t, by simpa [Submonoid.smul_def] using ht⟩
    obtain ⟨g, hg⟩ := Module.Finite.fg_top (R := A) (M := M)
    have huniform : ∀ g : Finset M, ∃ t : S, ∀ m ∈ g, (t : A) • (a • m) = 0 := by
      intro g
      induction g using Finset.induction_on with
      | empty => exact ⟨1, by simp⟩
      | @insert m g hmg ih =>
        obtain ⟨t, ht⟩ := hkill m
        obtain ⟨u, hu⟩ := ih
        refine ⟨t * u, ?_⟩
        intro n hn
        rcases Finset.mem_insert.mp hn with rfl | hn
        · simp only [Submonoid.coe_mul, mul_smul]
          rw [smul_comm, ht, smul_zero]
        · simp only [Submonoid.coe_mul, mul_smul]
          rw [hu n hn, smul_zero]
    obtain ⟨t, ht⟩ := huniform g
    have ha : (t : A) * a ∈ Module.annihilator A M := by
      rw [← Submodule.annihilator_top, ← hg, Submodule.mem_annihilator_span]
      intro m
      simpa only [mul_smul] using ht m.val m.property
    exact (IsLocalization.mk'_mem_map_algebraMap_iff S
      (Localization.Away f) (Module.annihilator A M) a s).mpr ⟨t, t.property, ha⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    apply Module.mem_annihilator.mpr
    intro z
    induction z using LocalizedModule.induction_on with
    | h m s =>
      rw [← Localization.mk_one_eq_algebraMap, LocalizedModule.mk_smul_mk]
      rw [Module.mem_annihilator.mp ha m, LocalizedModule.zero_mk]


end Module
