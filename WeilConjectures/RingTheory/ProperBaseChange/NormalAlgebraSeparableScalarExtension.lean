/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.ProperBaseChange.GeometricallyNormalTensorNormal
import WeilConjectures.RingTheory.ProperBaseChange.SeparableFieldGeometricallyNormal

/-!
# Normal algebras under separable scalar extension

A normal algebra over a field `k` remains normal after a separable field extension `K/k`.

## Implementation details

A separable `K/k` is geometrically normal, so `K ⊗[k] B` is normal by the tensor normality
theorem for geometrically normal and normal algebras; swapping the tensor factors transports
normality to `B ⊗[k] K`.

## References

* [Stacks, Tag 0C3M]
* [Stacks, Tags 0C30, 06DF]
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- A normal commutative `k`-algebra remains normal after a separable field extension `K/k`.
Separability means that every finitely generated intermediate field is separably generated.
Normality means that every prime localization is an integrally closed domain.
There is no algebraicity, finite-generation, domain or nonzero assumption on the algebra. -/
theorem isNormal_tensorProduct_of_separableExtension
    (k : Type u) (B : Type v) (K : Type w)
    [Field k] [CommRing B] [Field K] [Algebra k B] [Algebra k K]
    (hK : IsSeparableExtension k K)
    (hB : ∀ (p : Ideal B) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    ∀ (q : Ideal (B ⊗[k] K)) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let hA : ∀ (E : Type (max u v w)) [Field E] [Algebra k E],
      ∀ (p : Ideal (K ⊗[k] E)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
    fun E _ _ ↦ normal_tensorProduct_of_isSeparableExtension k K E hK
  let hnormal := isNormal_tensorProduct_of_geometricallyNormal k K B hA hB
  intro q hq
  have := hq
  let e : (K ⊗[k] B) ≃+* (B ⊗[k] K) :=
    (Algebra.TensorProduct.comm k K B).toRingEquiv
  let p : Ideal (K ⊗[k] B) := Ideal.comap e q
  have : p.IsPrime := Ideal.IsPrime.comap e
  have hp := hnormal p
  let f := Localization.localRingEquiv p q e rfl
  have : IsDomain (Localization.AtPrime p) := hp.1
  have : IsIntegrallyClosed (Localization.AtPrime p) := hp.2
  exact ⟨f.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv f⟩

end Algebra
