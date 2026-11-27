/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.GenericFormalFiberPurelyInseparableRegularAux
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Generic formal fibres after purely inseparable base change

Every finite purely inseparable base change of the generic formal fibre of a regular
power-series model is regular.

## References

* [Stacks, Tag 07PS]
-/

@[expose] public section

universe u

/-- Every finite purely inseparable base change of the generic formal fibre is regular. -/
theorem isRegular_genericFormalFiber_after_finite_purelyInseparable
    (A : Type u) [CommRing A] [IsDomain A] [IsRegularLocalRing A]
    (hmodel :
      (∃ (k : Type u), ∃ h : Field k, ∃ d : ℕ,
        let _ := h
        Nonempty (A ≃+* MvPowerSeries (Fin d) k)) ∨
      (∃ (Λ : Type u), ∃ h : CommRing Λ, ∃ d : ℕ,
        let _ := h
        ∃ p : ℕ, IsCohenRing p Λ ∧
          Nonempty (A ≃+* MvPowerSeries (Fin d) Λ)))
    (P : Ideal A) [P.IsPrime] :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P)
    ∀ (k' : Type (max u u)) [Field k']
      [Algebra ((⊥ : Ideal A).ResidueField) k'] [Module.Finite ((⊥ : Ideal A).ResidueField) k']
      [IsPurelyInseparable ((⊥ : Ideal A).ResidueField) k'],
      IsRegularRing
        (TensorProduct ((⊥ : Ideal A).ResidueField) k' ((⊥ : Ideal A).Fiber C)) := by
  dsimp
  intro k' instField instAlg instFinite instPI
  let := instField
  let := instAlg
  have := instFinite
  have := instPI
  rcases hmodel with h | h
  · rcases h with ⟨k, hk, d, e⟩
    let := hk
    exact isRegular_genericFormalFiber_fieldModel A k d e P k'
  · rcases h with ⟨Λ, hΛ, d, p, hc, e⟩
    let := hΛ
    exact isRegular_genericFormalFiber_cohenModel A Λ d p hc e P k' 

end
