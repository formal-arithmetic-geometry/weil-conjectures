/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Differential-fibre dimension under scalar extension

The dimension of the fibre of the module of differentials of a finite type `k`-algebra `S` at
a prime `q` is unchanged at any prime of `K ⊗[k] S` above `q`.

## Implementation details

The maximality and algebraic closedness hypotheses are not used by the proof; they are
present only to match the intended application. Finrank base change holds without a
finite-dimensionality hypothesis, so the statement also covers infinite-dimensional fibres.

## References

* Stacks Project, Algebra, Tag 00RV.
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- Let `S` be a finite type `k`-algebra, `q` a prime of `S`, `K` an algebraically closed
field over `k` and `qK` a maximal ideal of `K ⊗[k] S` lying over `q`. Then the fibre of
`Ω[(K ⊗[k] S)/K]` at `qK` has the same dimension over `κ(qK)` as the fibre of `Ω[S/k]` at `q`
over `κ(q)`. -/
theorem algClosed_prime_over_finrank_differentials_eq
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S] [FiniteType k S]
    (q : PrimeSpectrum S)
    (K : Type (max u v)) (_hK : Field K) (_hAk : Algebra k K) (_hCK : IsAlgClosed K)
    (qK : PrimeSpectrum (K ⊗[k] S))
    (_hmax : qK.asIdeal.IsMaximal)
    (hq : PrimeSpectrum.comap
      (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK = q) :
    Module.finrank qK.asIdeal.ResidueField
        (qK.asIdeal.ResidueField ⊗[K ⊗[k] S] KaehlerDifferential K (K ⊗[k] S)) =
      Module.finrank q.asIdeal.ResidueField
        (q.asIdeal.ResidueField ⊗[S] KaehlerDifferential k S) := by
  let B := K ⊗[k] S
  let L := qK.asIdeal.ResidueField
  let κ := q.asIdeal.ResidueField
  let : Algebra S B := TensorProduct.rightAlgebra
  have hp : q.asIdeal = qK.asIdeal.comap (algebraMap S B) :=
    (congrArg PrimeSpectrum.asIdeal hq).symm
  let f : κ →ₐ[S] L := Ideal.ResidueField.mapₐ q.asIdeal qK.asIdeal
    (Algebra.ofId S B) hp
  let : Algebra κ L := f.toAlgebra
  have : IsScalarTower S κ L := IsScalarTower.of_algHom f
  let e : (L ⊗[B] KaehlerDifferential K B) ≃ₗ[L]
      (L ⊗[κ] (κ ⊗[S] KaehlerDifferential k S)) :=
    LinearEquiv.baseChange B L _ _ (KaehlerDifferential.tensorKaehlerEquiv k K S B).symm
      ≪≫ₗ TensorProduct.AlgebraTensorModule.cancelBaseChange S B L L _
      ≪≫ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange S κ L L _).symm
  exact e.finrank_eq.trans (Module.finrank_baseChange (R := L) (S := κ))

end Algebra
