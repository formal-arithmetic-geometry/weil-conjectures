/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.RingTheory.FiniteFreeMapResidueLocalizationStrong

/-!
# Residue-field rank criterion for maps of finite free modules

A map of finite free modules that is injective (resp. bijective) on the residue field at a
prime `p` becomes injective with finite free cokernel (resp. bijective) after inverting an
element outside `p`.

## Implementation details

Represent `u` by a matrix. In the injective case a maximal minor has determinant `f ∉ p`, and
after localizing at `f` row and column operations bring the matrix to the block form `[I_m; 0]`.
In the bijective case the determinant becomes a unit and the adjugate gives an inverse.

## References

* [Stacks, Tag 00O0] (1), (3)
-/

@[expose] public section

namespace Module

/-- Let `u : R^m → R^n` and let `p` be a prime of `R`. If `u` is injective on the residue field
of `p`, then after inverting some `f ∉ p` it is injective with finite free cokernel; if it is
bijective on the residue field, then it is bijective after inverting some `f ∉ p`. -/
theorem finiteFreeMap_residue_localization
    {R : Type*} [CommRing R] (m n : ℕ) (u : (Fin m → R) →ₗ[R] (Fin n → R))
    (p : Ideal R) [p.IsPrime] :
    (Function.Injective (u.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧
        Function.Injective (u.baseChange (Localization.Away f)) ∧
        Module.Finite (Localization.Away f)
          (TensorProduct R (Localization.Away f) (Fin n → R) ⧸
            LinearMap.range (u.baseChange (Localization.Away f))) ∧
        Module.Free (Localization.Away f)
          (TensorProduct R (Localization.Away f) (Fin n → R) ⧸
            LinearMap.range (u.baseChange (Localization.Away f)))) ∧
    (Function.Bijective (u.baseChange p.ResidueField) →
      ∃ f : R, f ∉ p ∧ Function.Bijective (u.baseChange (Localization.Away f))) := by
  have h := finiteFreeMap_residue_localization_strong m n u p
  constructor
  · intro hu
    obtain ⟨f, hf, v, hv, hfin, hfree⟩ := h.1 hu
    refine ⟨f, hf, ?_, hfin, hfree⟩
    exact Function.HasLeftInverse.injective ⟨v, LinearMap.congr_fun hv⟩
  · intro hu
    obtain ⟨f, hf, v, hv, hw⟩ := h.2 hu
    refine ⟨f, hf, ?_⟩
    constructor
    · exact Function.HasLeftInverse.injective ⟨v, LinearMap.congr_fun hv⟩
    · exact Function.HasRightInverse.surjective ⟨v, LinearMap.congr_fun hw⟩

end Module
