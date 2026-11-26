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
public import Mathlib.RingTheory.TensorProduct.Basic
import WeilConjectures.RingTheory.FiniteAfterCompletion
import WeilConjectures.RingTheory.CompletionFiniteExtensionDecomposition
import WeilConjectures.RingTheory.CompletionFiniteExtensionTensor
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso

/-!
# Completion of a finite algebra over a prime

The completion of a finite algebra `S` over a Noetherian ring `R` at a prime `p` decomposes as
the product of the completions of `S_q` over the primes `q` above `p`.

## Implementation details

The factors are indexed by all primes lying over `p`, with finiteness a conclusion. The maps
`g q` are specified modulo every power of the maximal ideals, so they are exactly the completion
maps induced by `Localization.localRingHom`. The equation on `a ⊗ₜ 1` expresses compatibility
with the completed-base algebra structures.

The proof localizes at `p`, decomposes each quotient `B ⧸ p^n B` (which has finitely many
maximal ideals and nil Jacobson radical) as a product of localizations, and passes to the limit;
the tensor description comes from completion of finite modules.

## References

* [Stacks, Tag 07N9]
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace AdicCompletion

/-- For a finite algebra `S` over a Noetherian ring `R` and a prime `p`, there are finitely
many primes `q` over `p`, and `R_p^∧ ⊗[R] S` is isomorphic to the product of the completions
of the `S_q`, compatibly with the maps `g q` induced by the local maps `R_p → S_q`. It is also
isomorphic to the `p`-adic completion of `R_p ⊗[R] S`. -/
theorem completion_finite_extension
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.Finite R S] (p : Ideal R) [p.IsPrime] :
    let A := Localization.AtPrime p
    let m := IsLocalRing.maximalIdeal A
    let C := AdicCompletion m A
    let B := A ⊗[R] S
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := A) (B := S)
    let J := p.map (algebraMap R B)
    let Q := p.primesOver S
    let D := fun q : Q ↦
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.1))
        (Localization.AtPrime q.1)
    letI := Algebra.TensorProduct.rightAlgebra (R := R) (A := C) (B := S)
    Finite Q ∧
      ∃ (e : (C ⊗[R] S) ≃ₐ[S] (∀ q : Q, D q))
        (g : ∀ q : Q, C →+* D q),
        (∀ (q : Q) (n : ℕ) (a : C) (r : A),
          AdicCompletion.evalₐ m n a = Ideal.Quotient.mk (m ^ n) r →
          AdicCompletion.evalₐ
              (IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) n (g q a) =
            Ideal.Quotient.mk
              ((IsLocalRing.maximalIdeal (Localization.AtPrime q.1)) ^ n)
              (Localization.localRingHom p q.1 (algebraMap R S)
                (Ideal.LiesOver.over (P := q.1) (p := p)) r)) ∧
        (∀ (a : C) (q : Q), e (a ⊗ₜ[R] (1 : S)) q = g q a) ∧
        Nonempty ((C ⊗[R] S) ≃ₐ[S] AdicCompletion J B) := by
  have hd := completion_finite_extension_decomposition R S p
  have ht := completion_finite_extension_tensor R S p
  rcases hd with ⟨hfin, ⟨e, g, hlevel, hcompat⟩⟩
  exact ⟨hfin, ⟨e, g, hlevel, hcompat, ht⟩⟩

end AdicCompletion
