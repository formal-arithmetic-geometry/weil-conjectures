/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# The rank of an étale integral closure

Let `R₀` be a domain, `B` a flat `R₀`-algebra, `B_K` the localization of `B` at the nonzero
elements of `R₀` and `L` a finite flat `B_K`-algebra of rank at most `k`. If the base change
`B_h ⊗_B T₀` of the integral closure `T₀` of `B` in `L` to a localization `B_h` is étale, then it
is finite of rank at most `k` (`RingTheory.DepthTwo.finite_rankAtStalk_le_of_etale`): it is
integral and of finite type, and by going down its rank at a prime equals its rank at a prime
over `0 ⊆ R₀`, where it is the rank of `L`. This is used in the depth-two step of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

open TensorProduct

namespace RingTheory.DepthTwo

variable {R₀ B Bk L : Type*} [CommRing R₀] [IsDomain R₀]
  [CommRing B] [Algebra R₀ B] [Module.Flat R₀ B]
  [CommRing Bk] [Algebra B Bk]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) Bk]
  [CommRing L] [Algebra Bk L] [Algebra B L] [IsScalarTower B Bk L]
  [Module.Finite Bk L] [Module.Flat Bk L]

include R₀ in
/-- The base change of the integral closure `T₀` of `B` in `L` to `B_K` is `L`. -/
noncomputable def tensorIntegralClosureEquiv :
    Bk ⊗[B] integralClosure B L ≃ₐ[Bk] L :=
  have hint : integralClosure Bk (Bk ⊗[B] L) = ⊤ := by
    let e := IsLocalization.algebraLid (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) Bk L
    refine eq_top_iff.2 fun x _ ↦ ?_
    have := (Algebra.IsIntegral.isIntegral (R := Bk) (e x)).map e.symm.toAlgHom
    exact (by simpa using this : IsIntegral Bk x)
  (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure B Bk L)
    (TensorProduct.toIntegralClosure_bijective_of_isLocalization
      (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)))).trans <|
    ((Subalgebra.equivOfEq _ ⊤ hint).trans Subalgebra.topEquiv).trans <|
      IsLocalization.algebraLid (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) Bk L

include R₀ in
/-- **The rank of an étale integral closure.** If `B_h ⊗_B T₀` is étale over `B_h`, where `T₀` is
the integral closure of `B` in `L`, then it is finite of rank at most `k`. -/
theorem finite_rankAtStalk_le_of_etale (h : B) {k : ℕ}
    (hrank : ∀ p, Module.rankAtStalk (R := Bk) L p ≤ k)
    [Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B L)] :
    Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B L) ∧
      ∀ p, Module.rankAtStalk (R := Localization.Away h)
        (Localization.Away h ⊗[B] integralClosure B L) p ≤ k := by
  set Bh := Localization.Away h
  set T₀ := integralClosure B L
  have hF : Module.Finite Bh (Bh ⊗[B] T₀) := Algebra.IsIntegral.finite
  refine ⟨hF, fun Q ↦ ?_⟩
  -- going down to a prime over `0`
  have : Module.Flat R₀ Bh := Module.Flat.trans R₀ B Bh
  obtain ⟨Q₀, hQ₀Q, hQ₀, hlies⟩ := Ideal.exists_ideal_le_liesOver_of_le (R := R₀) (p := ⊥)
    (q := Q.asIdeal.under R₀) Q.asIdeal bot_le
  rw [← Module.rankAtStalk_eq_of_le_of_finite_of_flat (Bh ⊗[B] T₀)
    (show (⟨Q₀, hQ₀⟩ : PrimeSpectrum Bh) ≤ Q from hQ₀Q)]
  -- the localization `Y = B_h ⊗_B B_K` of `B_h` at the nonzero elements of `R₀`
  let Y := Bh ⊗[B] Bk
  let : Algebra Bk Y := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower B Bk Y := .of_algebraMap_eq fun b ↦ by
    change algebraMap B Bh b ⊗ₜ[B] (1 : Bk) = (1 : Bh) ⊗ₜ[B] algebraMap B Bk b
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one]
  obtain ⟨Q₀', hQ₀'⟩ : (⟨Q₀, hQ₀⟩ : PrimeSpectrum Bh) ∈
      Set.range (PrimeSpectrum.comap (algebraMap Bh Y)) := by
    rw [PrimeSpectrum.localization_comap_range Y
      (Algebra.algebraMapSubmonoid Bh (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)))]
    rw [Set.mem_ofPred_eq, Set.disjoint_left]
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩ hmem
    have : r ∈ Q₀.under R₀ := by
      rw [Ideal.mem_under, IsScalarTower.algebraMap_apply R₀ B Bh]
      exact hmem
    rw [← hlies.over, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hr this
  rw [← hQ₀', ← Module.rankAtStalk_baseChange]
  let e : Y ⊗[Bh] (Bh ⊗[B] T₀) ≃ₐ[Y] Y ⊗[Bk] L :=
    (Algebra.TensorProduct.cancelBaseChange B Bh Y Y T₀).trans <|
      (Algebra.TensorProduct.cancelBaseChange B Bk Y Y T₀).symm.trans <|
        Algebra.TensorProduct.congr AlgEquiv.refl (tensorIntegralClosureEquiv (R₀ := R₀))
  rw [Module.rankAtStalk_eq_of_equiv e.toLinearEquiv, Module.rankAtStalk_baseChange]
  exact hrank _

end RingTheory.DepthTwo
