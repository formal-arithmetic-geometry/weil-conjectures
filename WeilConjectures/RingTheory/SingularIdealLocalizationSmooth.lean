/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.RingTheory.SingularIdeal
import WeilConjectures.RingTheory.SmoothOfLocalizationSpanUniverses
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Smoothness of principal localizations at elements of the singular ideal

## References

* [Stacks, Tag 07EU]
* [Stacks, Tag 00TC]
-/

@[expose] public section
universe u v
namespace Algebra

/-- If a power of `f` lies in the span of the elements with smooth principal localizations,
then the principal localization at `f` is smooth. -/
theorem smooth_localization_span_from_radical
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (f : A) (n : ℕ) (hn : f ^ n ∈ Ideal.span (smoothElements R A)) :
    Smooth R (Localization.Away f) := by
  let B := Localization.Away f
  let s : Set B := algebraMap A B '' smoothElements R A
  have hs : Ideal.span s = ⊤ := by
    have hmem : algebraMap A B (f ^ n) ∈ Ideal.span s := by
      rw [← Ideal.map_span]
      exact Ideal.mem_map_of_mem _ hn
    exact (Ideal.span s).eq_top_of_isUnit_mem hmem
      (by simpa only [map_pow] using
        (IsLocalization.Away.algebraMap_isUnit (S := B) f).pow n)
  apply smooth_of_localization_span_universes R B s hs
  rintro ⟨b, hb⟩
  obtain ⟨g, hg, rfl⟩ := hb
  have : Smooth R (Localization.Away g) := hg
  let C : Type v := Localization.Away (algebraMap A (Localization.Away g) f)
  let D : Type v := Localization.Away (algebraMap A B g)
  have : Smooth (Localization.Away g) C :=
    Smooth.of_isLocalization_Away (algebraMap A (Localization.Away g) f)
  have : Smooth R C := Smooth.comp R (Localization.Away g) C
  have : IsLocalization.Away (f * g) C := inferInstance
  have : IsLocalization.Away (f * g) D := inferInstance
  exact Smooth.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (f * g)) C D).restrictScalars R)

/-- If an element belongs to the singular ideal, its principal localization is smooth. -/
theorem smooth_localization_of_mem_singularIdeal
    (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (f : A) (hf : f ∈ singularIdeal R A) : Smooth R (Localization.Away f) := by
  have hpow : ∃ n : ℕ, f ^ n ∈ Ideal.span (smoothElements R A) :=
    Ideal.mem_radical_iff.mp hf
  obtain ⟨n, hn⟩ := hpow
  exact smooth_localization_span_from_radical R A f n hn

end Algebra
