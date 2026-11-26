/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# Quotient projections separate a completed finite tensor

For a finite algebra `S` over a Noetherian ring `R` and a prime `p`, an element of
`R_p^∧ ⊗_R S` vanishing under all maps to `R_p/m^n ⊗_R S` is zero.

## Implementation details

`C = R_p^∧` is Noetherian local with maximal ideal `mC` (Tags 0316, 05GG, 05GI), so the
finite `C`-module `C ⊗_R S` is `mC`-adically separated (Krull intersection, Tag 00IQ). The
kernel of `C ⊗_R S → A/m^n ⊗_R S` is `(mC)^n (C ⊗_R S)` by Tag 05GG and right exactness of
the tensor product (Tag 00DF).

## References

* [Stacks, Tag 07N9]
* [Stacks, Tag 0316]
* [Stacks, Tag 05GG]
* [Stacks, Tag 05GI]
* [Stacks, Tag 00DF]
* [Stacks, Tag 00IQ]
-/

@[expose] public section

universe u v
open scoped TensorProduct
namespace AdicCompletion

/-- The quotient projections `R_p^∧ ⊗_R S → R_p/m^n ⊗_R S` jointly detect zero: an element
mapping to zero for every `n` is zero. -/
theorem completion_tensor_quotient_separated
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let C := AdicCompletion m A
    ∀ x : C ⊗[R] S,
      (∀ n : ℕ, Algebra.TensorProduct.map ((evalₐ m n).restrictScalars R)
        (AlgHom.id R S) x = 0) → x = 0 := by
  dsimp only
  let A := Localization.AtPrime p
  let m := IsLocalRing.maximalIdeal A
  let C := AdicCompletion m A
  let T := C ⊗[R] S
  have : IsNoetherianRing A := inferInstance
  have : IsNoetherianRing C := isNoetherianRing m
  have : IsLocalRing C := inferInstance
  have : Module.Finite C T := inferInstance
  intro x hx
  apply IsHausdorff.haus (inferInstance : IsHausdorff (IsLocalRing.maximalIdeal C) T) x
  intro n
  have hker : RingHom.ker (evalₐ m n).toRingHom =
      (m ^ n).map (algebraMap A C) := by
    rw [← Submodule.restrictScalars_inj A]
    rw [← Ideal.smul_top_eq_map, pow_smul_top_eq_ker_eval m.fg_of_isNoetherianRing]
    ext a
    change evalₐ m n a = 0 ↔ eval m A n a = 0
    have h := factor_evalₐ_eq_eval m (n := n) a (by simp)
    have he := factor_eval_eq_evalₐ m (n := n) a (by simp)
    constructor
    · intro ha
      rw [ha, _root_.map_zero] at h
      exact h.symm
    · intro ha
      rw [ha, _root_.map_zero] at he
      exact he.symm
  have hmem : x ∈ ((IsLocalRing.maximalIdeal C) ^ n).map (algebraMap C T) := by
    have hz : x ∈ RingHom.ker
        (Algebra.TensorProduct.map ((evalₐ m n).restrictScalars R) (AlgHom.id R S)) :=
      hx n
    rw [Algebra.TensorProduct.rTensor_ker ((evalₐ m n).restrictScalars R)
      (surjective_evalₐ m n)] at hz
    change x ∈ (RingHom.ker (evalₐ m n).toRingHom).map
      (Algebra.TensorProduct.includeLeft : C →ₐ[R] T) at hz
    rw [hker] at hz
    rw [show IsLocalRing.maximalIdeal C = m.map (algebraMap A C) from
      maximalIdeal_eq_map]
    change x ∈ ((m.map (algebraMap A C)) ^ n).map
      (Algebra.TensorProduct.includeLeft : C →ₐ[R] T)
    simpa only [Ideal.map_pow] using hz
  rw [SModEq.zero, Ideal.smul_top_eq_map]
  exact hmem

end AdicCompletion
