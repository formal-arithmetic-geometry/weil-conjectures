/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q127 and R3
-/
module

public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

import WeilConjectures.Mathlib.RingTheory.Valuation.LocalSubring
import Sheaf.RingTheory.ValuationIntegralMultiplicationCertificate

/-!
# Normalization of a valuation ring and its prolongations

Source: Temkin, Stable modification of relative curves, Proposition 2.2.1, converse proof,
printed p. 11, and the background discussion in Section 2.1; Bourbaki, Commutative Algebra,
VI Section 8.6, Proposition 6 (blueprint: lem-trf-valuation-normalization-localizations).

The maximal localizations are Mathlib's `Localization.subalgebra.ofField`, with their
canonical embeddings into the fraction field, rather than abstractly isomorphic rings.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace ValuationSubring

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

private theorem inverse_mem_of_unit {S : Subring L} (a : S) (ha : IsUnit a) :
    (a : L)⁻¹ ∈ S := by
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
  have hab : (a : L) * (b : L) = 1 := congrArg Subtype.val hb
  simpa only [inv_eq_of_mul_eq_one_right hab] using b.property

private theorem localization_dichotomy (V : ValuationSubring K)
    (n : MaximalSpectrum (integralClosure V L))
    (D : Subalgebra (integralClosure V L) L)
    [IsLocalization.AtPrime D n.asIdeal] :
    ∀ x : L, x ∈ D ∨ x⁻¹ ∈ D := by
  have : IsLocalRing D := IsLocalization.AtPrime.isLocalRing D n.asIdeal
  intro x
  obtain ⟨a, b, c, d, hb, hd, had⟩ := integralClosure_mul_certificate K L V x
  let a' : D := algebraMap _ D a
  let b' : D := algebraMap _ D b
  let c' : D := algebraMap _ D c
  let d' : D := algebraMap _ D d
  have heq : a' + -d' = 1 := by
    simpa only [map_sub, map_add, map_neg, map_one, sub_eq_add_neg] using
      congrArg (algebraMap (integralClosure V L) D) had
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one heq with ha | hd'
  · left
    have ha0 : (a : L) ≠ 0 := by
      exact (ha.map D.val).ne_zero
    have hm := D.toSubring.mul_mem b'.property (inverse_mem_of_unit a' ha)
    change (b : L) * (a : L)⁻¹ ∈ D at hm
    simpa only [hb, mul_inv_cancel_right₀ ha0] using hm
  · right
    have hdunit : IsUnit d' := (IsUnit.neg_iff _).mp hd'
    have hd0 : (d : L) ≠ 0 := (hdunit.map D.val).ne_zero
    have hx0 : x ≠ 0 := by
      intro hx
      exact hd0 (by simp [hd, hx])
    have hm := D.toSubring.mul_mem c'.property (inverse_mem_of_unit d' hdunit)
    change (c : L) * (d : L)⁻¹ ∈ D at hm
    have hc : (c : L) = x⁻¹ * (d : L) := by rw [hd, inv_mul_cancel_left₀ hx0]
    simpa only [hc, mul_inv_cancel_right₀ hd0] using hm

omit [FiniteDimensional K L] in
private theorem localization_comap (V : ValuationSubring K)
    (n : MaximalSpectrum (integralClosure V L))
    (D : Subalgebra (integralClosure V L) L)
    [IsLocalization.AtPrime D n.asIdeal]
    (hD : ∀ x : L, x ∈ D ∨ x⁻¹ ∈ D) :
    (⟨D.toSubring, hD⟩ : ValuationSubring L).comap (algebraMap K L) = V := by
  let W : ValuationSubring L := ⟨D.toSubring, hD⟩
  have hn : n.asIdeal.comap (algebraMap V (integralClosure V L)) =
      IsLocalRing.maximalIdeal V :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal n.asIdeal)
  have hVD : ∀ a : V, algebraMap V L a ∈ D := fun a =>
    D.algebraMap_mem (algebraMap V (integralClosure V L) a)
  apply comap_eq_of_toLocalSubring_le
  refine ⟨fun x hx => hVD ⟨x, hx⟩, ⟨?_⟩⟩
  intro a ha
  by_contra hna
  have ham : a ∈ IsLocalRing.maximalIdeal V := hna
  have han : algebraMap V (integralClosure V L) a ∈ n.asIdeal := by
    change a ∈ n.asIdeal.comap (algebraMap V (integralClosure V L))
    rwa [hn]
  have hnot : ¬ IsUnit (algebraMap (integralClosure V L) D
      (algebraMap V (integralClosure V L) a)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff D n.asIdeal]
    exact fun h => h han
  let g : (W.comap (algebraMap K L)) →+* D :=
    (algebraMap K L).restrict _ D.toSubring (fun _ hx => hx)
  exact hnot (ha.map g)

omit [FiniteDimensional K L] in
private theorem center_maximal (V : ValuationSubring K) (W : ValuationSubring L)
    (hW : W.comap (algebraMap K L) = V)
    (hCW : (integralClosure V L).toSubring ≤ W.toSubring) :
    ((IsLocalRing.maximalIdeal W).comap (Subring.inclusion hCW)).IsMaximal := by
  let f : integralClosure V L →+* W := Subring.inclusion hCW
  let q := (IsLocalRing.maximalIdeal W).comap f
  have hq : q.comap (algebraMap V (integralClosure V L)) =
      IsLocalRing.maximalIdeal V := by
    ext a
    change f (algebraMap V (integralClosure V L) a) ∈
      IsLocalRing.maximalIdeal W ↔ a ∈ IsLocalRing.maximalIdeal V
    rw [← W.coe_mem_nonunits_iff, ← V.coe_mem_nonunits_iff]
    change algebraMap K L (a : K) ∈ W.nonunits ↔ (a : K) ∈ V.nonunits
    rw [W.mem_nonunits_iff_or, V.mem_nonunits_iff_or]
    simp only [map_eq_zero, ← map_inv₀, ← mem_comap, hW]
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q
    (hq.symm ▸ IsLocalRing.maximalIdeal.isMaximal V)

omit [FiniteDimensional K L] in
private theorem valuation_eq_of_center (V : ValuationSubring K)
    (W : ValuationSubring L)
    (hCW : (integralClosure V L).toSubring ≤ W.toSubring)
    (n : MaximalSpectrum (integralClosure V L))
    (hn : n.asIdeal = (IsLocalRing.maximalIdeal W).comap (Subring.inclusion hCW))
    (D : Subalgebra (integralClosure V L) L)
    [IsLocalization.AtPrime D n.asIdeal]
    (hD : ∀ x : L, x ∈ D ∨ x⁻¹ ∈ D) : W.toSubring = D.toSubring := by
  let f : integralClosure V L →+* W := Subring.inclusion hCW
  have hunit (s : n.asIdeal.primeCompl) : IsUnit (f s) := by
    by_contra hs
    have hmem : (s : integralClosure V L) ∈
        (IsLocalRing.maximalIdeal W).comap (Subring.inclusion hCW) := hs
    exact s.property (hn.ge hmem)
  have hDW : D.toSubring ≤ W.toSubring := by
    intro x hx
    obtain ⟨r, s, he⟩ := IsLocalization.exists_mk'_eq n.asIdeal.primeCompl (⟨x, hx⟩ : D)
    have hs0 : (s : L) ≠ 0 := by
      intro hs
      apply s.property
      have heq : (s : integralClosure V L) = 0 := Subtype.ext hs
      rw [heq]
      exact n.asIdeal.zero_mem
    have hspec := congrArg (fun y : D => (y : L)) (IsLocalization.mk'_spec D r s)
    rw [he] at hspec
    have hxrep : x = (r : L) * (s : L)⁻¹ := (eq_mul_inv_iff_mul_eq₀ hs0).mpr hspec
    rw [hxrep]
    exact W.toSubring.mul_mem (hCW r.property) (inverse_mem_of_unit (f s) (hunit s))
  let U : ValuationSubring L := ⟨D.toSubring, hD⟩
  have hdom : U.toLocalSubring ≤ W.toLocalSubring := by
    refine ⟨hDW, ⟨?_⟩⟩
    intro x hx
    change D at x
    change IsUnit (Subring.inclusion hDW x) at hx
    change IsUnit x
    obtain ⟨r, s, he⟩ := IsLocalization.exists_mk'_eq n.asIdeal.primeCompl x
    rw [← he, IsLocalization.AtPrime.isUnit_mk'_iff D n.asIdeal]
    have hru : IsUnit (f r) := by
      have hs := (hunit s)
      have e := congrArg (Subring.inclusion hDW) (IsLocalization.mk'_spec D r s)
      have hx' : IsUnit (Subring.inclusion hDW (IsLocalization.mk' D r s)) := by
        rwa [he]
      exact (show Subring.inclusion hDW (IsLocalization.mk' D r s) * f s = f r
        from e) ▸ (hx'.mul hs)
    intro hr
    have hqr : f r ∈ IsLocalRing.maximalIdeal W := by
      change r ∈ (IsLocalRing.maximalIdeal W).comap f
      rwa [← hn]
    exact hqr hru
  exact congrArg LocalSubring.toSubring (le_antisymm (U.isMax_toLocalSubring hdom) hdom)

omit [FiniteDimensional K L] in
private theorem localization_ideal_injective (V : ValuationSubring K)
    (n m : MaximalSpectrum (integralClosure V L))
    (D E : Subalgebra (integralClosure V L) L)
    [IsLocalization.AtPrime D n.asIdeal] [IsLocalization.AtPrime E m.asIdeal]
    (h : D.toSubring = E.toSubring) : n = m := by
  let e : D ≃+* E := RingEquiv.subringCongr h
  apply MaximalSpectrum.ext
  ext a
  have he : e (algebraMap (integralClosure V L) D a) =
      algebraMap (integralClosure V L) E a := Subtype.ext rfl
  have hu : IsUnit (algebraMap (integralClosure V L) D a) ↔
      IsUnit (algebraMap (integralClosure V L) E a) := by
    rw [← he]
    exact (MulEquiv.isUnit_map e).symm
  rw [IsLocalization.AtPrime.isUnit_to_map_iff D n.asIdeal,
    IsLocalization.AtPrime.isUnit_to_map_iff E m.asIdeal] at hu
  exact not_iff_not.mp hu

/-- The integral closure in a finite field extension is a nonzero integral domain integral
 over the valuation ring, with the extension field as its fraction field. Its maximal
 localizations are precisely the extending valuation subrings, each occurring uniquely.

Source: Temkin, Stable modification of relative curves, Proposition 2.2.1, converse proof,
printed p. 11; Bourbaki, Commutative Algebra, VI Section 8.6, Proposition 6
(blueprint: lem-trf-valuation-normalization-localizations).

Proof:
1. Mathlib supplies the domain, integrality, fraction-field, and maximal-spectrum
   instances for the integral closure `C`.
2. The integral multiplication certificate supplies `a,b,c,d` in `C` with
   `b=x*a`, `d=x*c`, and `a-d=1`. In a maximal localization `D`, one of `a,d` is
   a unit, giving respectively `x=b/a` or `x^-1=c/d` in `D`.
3. The maximal ideal of `C` contracts to the unique maximal ideal of `V`, by
   integrality. The localization unit criterion therefore makes `V` map locally
   into the restriction of `D` to `K`. Maximality in the domination order gives
   that this restriction is exactly `V`.
4. For an extending valuation subring `W`, Mathlib's proved normality instance
   puts `C` inside `W`. Its maximal ideal contracts to an ideal `q` of `C` whose
   contraction to `V` is maximal: use the inverse criterion for valuation nonunits
   and the equality of restrictions. Hence `q` is maximal by integrality.
5. Fractions embed `C_q` into `W`. If a fraction becomes a unit in `W`, its
   numerator is outside `q`, so it was already a unit in `C_q`. Thus `W` dominates
   `C_q`; valuation maximality forces equality.
6. The localization unit criterion recovers each maximal ideal from its localized
   subring inside `L`, proving uniqueness. No rank, separability, henselianity,
   Noetherianity or module finiteness is used. -/
theorem integralClosure_maximal_localizations
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (V : ValuationSubring K) :
    Nontrivial (integralClosure V L) ∧
    IsDomain (integralClosure V L) ∧
    Algebra.IsIntegral V (integralClosure V L) ∧
    IsFractionRing (integralClosure V L) L ∧
    Nonempty (MaximalSpectrum (integralClosure V L)) ∧
    (∀ n : MaximalSpectrum (integralClosure V L),
      ∃ W : ValuationSubring L,
        W.toSubring =
          (@Localization.subalgebra.ofField (integralClosure V L) L _ n.asIdeal.primeCompl
            n.asIdeal.primeCompl_le_nonZeroDivisors _ _
            (integralClosure.isFractionRing_of_finite_extension K L)).toSubring ∧
        W.comap (algebraMap K L) = V) ∧
    (∀ W : ValuationSubring L, W.comap (algebraMap K L) = V →
      ∃! n : MaximalSpectrum (integralClosure V L),
        W.toSubring =
          (@Localization.subalgebra.ofField (integralClosure V L) L _ n.asIdeal.primeCompl
            n.asIdeal.primeCompl_le_nonZeroDivisors _ _
            (integralClosure.isFractionRing_of_finite_extension K L)).toSubring) := by
  have : IsFractionRing (integralClosure V L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  let D (n : MaximalSpectrum (integralClosure V L)) :=
    Localization.subalgebra.ofField L n.asIdeal.primeCompl
      n.asIdeal.primeCompl_le_nonZeroDivisors
  have hD (n : MaximalSpectrum (integralClosure V L)) :
      ∀ x : L, x ∈ D n ∨ x⁻¹ ∈ D n := localization_dichotomy V n (D n)
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · intro n
    exact ⟨⟨(D n).toSubring, hD n⟩, rfl, localization_comap V n (D n) (hD n)⟩
  · intro W hW
    have : IsIntegrallyClosedIn W.toSubring L :=
      inferInstanceAs (IsIntegrallyClosedIn W L)
    have hCW : (integralClosure V L).toSubring ≤ W.toSubring := by
      apply Subring.integralClosure_le_iff.mpr
      intro a
      change algebraMap K L (a : K) ∈ W
      rw [← mem_comap, hW]
      exact a.property
    let q := (IsLocalRing.maximalIdeal W).comap (Subring.inclusion hCW)
    let n : MaximalSpectrum (integralClosure V L) := ⟨q, center_maximal V W hW hCW⟩
    have hn : W.toSubring = (D n).toSubring :=
      valuation_eq_of_center V W hCW n rfl (D n) (hD n)
    refine ⟨n, hn, ?_⟩
    intro m hm
    exact localization_ideal_injective V m n (D m) (D n) (hm.symm.trans hn)

end ValuationSubring
