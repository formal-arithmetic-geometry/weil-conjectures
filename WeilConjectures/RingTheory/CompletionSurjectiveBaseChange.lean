/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.SurjectiveOnStalks
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.RingTheory.LocalCompletionQuotient

/-!
# Completion of a prime localization under a surjective base change

For a surjection `R → B` with `R` Noetherian and a prime `q` of `B` over `Q`, the completion of
`B_q` is `B ⊗[R] R_Q^∧`.

## Implementation details

The induced map `R_Q → B_q` is surjective with kernel extended from the kernel of `R → B`, so
the completion of `B_q` is a quotient of the completion of `R_Q`, which is identified with the
tensor product.

## References

* [Stacks, Tag 00CT]
* [Stacks, Tag 00MA], parts (2) and (3)
-/

@[expose] public section

universe u v

namespace AdicCompletion

/-- Completion of a prime localization commutes with a surjective change of base. -/
theorem nonempty_surjective_baseChange
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [IsNoetherianRing R] (hf : Function.Surjective (algebraMap R B))
    (Q : Ideal R) [Q.IsPrime] (q : Ideal B) [q.IsPrime]
    (hc : Q = q.comap (algebraMap R B)) :
    let A := Localization.AtPrime Q
    let D := Localization.AtPrime q
    let Cp := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let C := AdicCompletion (IsLocalRing.maximalIdeal D) D
    Nonempty (C ≃ₐ[B] TensorProduct R B Cp) := by
  dsimp only
  let A := Localization.AtPrime Q
  let D := Localization.AtPrime q
  let f := algebraMap R B
  let φ := Localization.localRingHom Q q f hc
  have hφ : Function.Surjective φ :=
    (RingHom.surjectiveOnStalks_of_surjective hf).localRingHom_surjective Q q hc
  have hφker : RingHom.ker φ = (RingHom.ker f).map (algebraMap R A) := by
    have hcompl : Submonoid.map f Q.primeCompl = q.primeCompl := by
      simpa only [hc] using Ideal.map_primeCompl_comap_of_surjective f hf q
    exact IsLocalization.ker_map (S := A) D f hcompl
  have hmax : (IsLocalRing.maximalIdeal A).map φ = IsLocalRing.maximalIdeal D :=
    IsLocalRing.map_maximalIdeal_of_surjective φ hφ
  have H := exists_local_completion_quotient A D φ hφ
  dsimp only at H
  rw [hmax, hφker, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at H
  obtain ⟨_, θ, _, hθ, _, _, e, he⟩ := H
  let Cp := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let C := AdicCompletion (IsLocalRing.maximalIdeal D) D
  let J := RingHom.ker f
  let P := Cp ⧸ J.map (algebraMap R Cp)
  let eR : P ≃ₐ[R] C :=
    { e with
      commutes' := fun x ↦ by
        change e (Ideal.Quotient.mk _ (algebraMap R Cp x)) = algebraMap R C x
        rw [he, IsScalarTower.algebraMap_apply R A Cp]
        rw [show θ (algebraMap A Cp (algebraMap R A x)) =
          algebraMap D C (φ (algebraMap R A x)) from RingHom.congr_fun hθ _]
        rw [Localization.localRingHom_to_map]
        exact (IsScalarTower.algebraMap_apply R B C x).symm }
  let eT := (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Cp J).restrictScalars R
  let fE : (R ⧸ J) ≃ₐ[R] B :=
    { f.quotientKerEquivOfSurjective hf with
      commutes' := fun x ↦ RingHom.quotientKerEquivOfSurjective_apply_mk hf x }
  let eB : P ≃ₐ[R] TensorProduct R B Cp :=
    eT.trans (Algebra.TensorProduct.congr fE (AlgEquiv.refl : Cp ≃ₐ[R] Cp))
  exact ⟨AlgEquiv.extendScalarsOfSurjective hf (eR.symm.trans eB)⟩

end AdicCompletion
