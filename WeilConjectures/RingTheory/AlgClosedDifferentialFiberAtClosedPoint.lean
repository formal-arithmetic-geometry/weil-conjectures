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
import WeilConjectures.RingTheory.AlgClosedPrimeOver
import WeilConjectures.RingTheory.AlgClosedDifferentialFiberFinrank

/-!
# Closed points over a prime after algebraically closed base change

For a prime `q` of a finite type `k`-algebra `S`, we find an algebraically closed field `K`
over `k` and a closed point of `Spec (K ⊗[k] S)` above `q` with the same differential-fibre
dimension. No smoothness or dimension bound is assumed.

## Implementation details

The field `K` is taken to be an algebraic closure of `κ(q)`, so it lives in
`Type (max u v)`.

## References

* Stacks Project, Algebra, proof of Tag 00TT, and Tag 00RV (differentials and base change).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

set_option linter.unusedVariables false in
/-- Let `S` be a finite type algebra over a field `k` and `q` a prime of `S`. There is an
algebraically closed field `K` over `k` and a maximal ideal `qK` of `K ⊗[k] S` lying over `q`
such that the fibres of the modules of differentials at `qK` and at `q` have the same
dimension over the respective residue fields. -/
theorem exists_algClosed_prime_over_finrank_differentials_eq
    {k : Type u} [Field k] {S : Type v} [CommRing S] [Algebra k S] [FiniteType k S]
    (q : PrimeSpectrum S) :
    ∃ (K : Type (max u v)) (hK : Field K) (hAk : Algebra k K) (hCK : IsAlgClosed K)
      (qK : PrimeSpectrum (K ⊗[k] S)),
      qK.asIdeal.IsMaximal ∧
        PrimeSpectrum.comap
          (TensorProduct.includeRight : S →ₐ[k] K ⊗[k] S).toRingHom qK = q ∧
        Module.finrank qK.asIdeal.ResidueField
          (qK.asIdeal.ResidueField ⊗[K ⊗[k] S] KaehlerDifferential K (K ⊗[k] S)) =
          Module.finrank q.asIdeal.ResidueField
            (q.asIdeal.ResidueField ⊗[S] KaehlerDifferential k S) := by
  obtain ⟨K, _hK, _hAk, _hCK, qK, hmax, hq⟩ := exists_algClosed_prime_over (k := k) q
  exact ⟨K, _hK, _hAk, _hCK, qK, hmax, hq,
    algClosed_prime_over_finrank_differentials_eq (k := k) (S := S) q K _hK _hAk _hCK qK
      hmax hq⟩

end Algebra
