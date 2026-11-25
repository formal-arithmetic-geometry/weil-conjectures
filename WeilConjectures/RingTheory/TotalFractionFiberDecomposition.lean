/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Mathlib.RingTheory.TensorProduct.Pi

/-! # The total-fraction localization as a product of residue-field fibres

## References

* [Stacks Project, Tag 02LX](https://stacks.math.columbia.edu/tag/02LX)
* [Stacks Project, Tag 07F5](https://stacks.math.columbia.edu/tag/07F5), third paragraph of
  the proof
-/

@[expose] public section

open scoped nonZeroDivisors TensorProduct
universe u v

/-- The localization of an algebra over a reduced Noetherian ring decomposes over its
minimal-prime residue fields, compatibly with the decomposition of the base ring. -/
theorem total_fraction_fiber_decomposition
    (R : Type u) (A : Type (max u v)) [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsReduced R] :
    ∃ (n : ℕ) (q : Fin n ≃ {p : PrimeSpectrum R // p.asIdeal ∈ minimalPrimes R})
      (e : Localization R⁰ ≃+* ∀ i, (q i).val.asIdeal.ResidueField)
      (f : Localization (Algebra.algebraMapSubmonoid A R⁰) ≃+*
        ∀ i, (q i).val.asIdeal.Fiber A),
      ∀ r i, f (algebraMap (Localization R⁰)
          (Localization (Algebra.algebraMapSubmonoid A R⁰)) r) i =
        algebraMap ((q i).val.asIdeal.ResidueField) ((q i).val.asIdeal.Fiber A) (e r i) := by
  classical
  obtain ⟨n, q, _, _, hbij, _, hex, hpi⟩ :=
    reduced_noetherian_total_ring_fractions (R := R)
  choose φ hφ using fun i ↦ (hex i).exists
  let φA : Localization R⁰ →ₐ[R] ∀ i, Localization.AtPrime (q i).val.asIdeal :=
    { __ := RingHom.pi φ
      commutes' := fun r ↦ funext fun i ↦ DFunLike.congr_fun (hφ i) r }
  let e : Localization R⁰ ≃ₐ[R] ∀ i, (q i).val.asIdeal.ResidueField :=
    (AlgEquiv.ofBijective φA (hpi φ hφ)).trans
      (AlgEquiv.piCongrRight fun i ↦ AlgEquiv.ofBijective
        (IsScalarTower.toAlgHom R (Localization.AtPrime (q i).val.asIdeal)
          (q i).val.asIdeal.ResidueField) (hbij i))
  let f : Localization (Algebra.algebraMapSubmonoid A R⁰) ≃+*
      ∀ i, (q i).val.asIdeal.Fiber A :=
    (Localization.tensorRightAlgEquiv R⁰ A).symm.toRingEquiv.trans
      ((Algebra.TensorProduct.comm R (Localization R⁰) A).toRingEquiv.trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[R] A) e).toRingEquiv.trans
          ((Algebra.TensorProduct.piRight R R A
            (fun i ↦ (q i).val.asIdeal.ResidueField)).toRingEquiv.trans
            (AlgEquiv.piCongrRight fun i ↦
              Algebra.TensorProduct.comm R A (q i).val.asIdeal.ResidueField).toRingEquiv)))
  refine ⟨n, q, e.toRingEquiv, f, ?_⟩
  intro r i
  simp [f, Algebra.TensorProduct.algebraMap_apply]
