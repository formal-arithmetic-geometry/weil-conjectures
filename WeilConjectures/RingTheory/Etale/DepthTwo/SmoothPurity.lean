/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Diagonal
public import WeilConjectures.RingTheory.Etale.DepthTwo.Global

/-!
# Purity for normal covers of a smooth algebra over a normal base

Let `R₀` be a Noetherian integrally closed domain, `q ≠ 0` a prime of `R₀`, `B` a smooth
`R₀`-algebra, `M` a `B`-algebra in which the nonzero elements of `R₀` are invertible
(geometrically: a cover of the generic fibre) and `T` the integral closure of `B` in `M`. Let `P`
be a prime of `B` over `q`. If `T` is finite étale near every prime `Q ⊆ P` of `B` which does not
lie over `q`, and near the minimal primes of `qB` contained in `P` (the generic points of the
components of the fibre), then `T` is finite étale near `P`
(`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`).

The proof is an induction on the primes between the minimal primes of `qB` and `P`. At `P`, with
`O = B_P` (a normal domain, being smooth over the normal `(R₀)_q`), `T_P` is finite over `O` and
étale over `D(a) ∪ D(β)` for `0 ≠ a ∈ q` and a suitable `β ∈ P` such that `(a, β)` is a regular
pair on `T_P`; the diagonal local ring `R = (B ⊗_{R₀} B)_{Δ(P)}` with its two projections and the
swap involution satisfies the hypotheses of `RingTheory.DepthTwo.etale_of_diagonal`, whose prime
`Q` comes from the generic point of the fibre of the second projection through `Δ(P)`.

This is the commutative algebra of purity for normal covers of a scheme smooth over a normal
Noetherian base (`AlgebraicGeometry.Scheme.Hom.mem_etaleLocus_fromNormalization_of_smooth`,
[Stacks 0EYE] and [Stacks 0EYB] in the form used in [Stacks 0EYJ]), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

universe u

open TensorProduct

namespace RingTheory.DepthTwo

variable {R₀ B M : Type u} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]
  [IsNoetherianRing R₀] [CommRing B] [Algebra R₀ B] [Algebra.Smooth R₀ B]
  [CommRing M] [Algebra B M] [Algebra R₀ M] [IsScalarTower R₀ B M]

/-- **Purity for normal covers of a smooth algebra over a normal base.** See the module
docstring. -/
theorem exists_etale_integralClosure_of_smooth (q : Ideal R₀) [q.IsPrime] (hq : q ≠ ⊥)
    (hunit : ∀ r : R₀, r ≠ 0 → IsUnit (algebraMap R₀ M r)) (P : Ideal B) [P.IsPrime]
    (hP : P.comap (algebraMap R₀ B) = q)
    (H : ∀ Q : Ideal B, Q.IsPrime → Q ≤ P →
      (Q.comap (algebraMap R₀ B) ≠ q ∨ Q ∈ (q.map (algebraMap R₀ B)).minimalPrimes) →
      ∃ h ∉ Q, Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M) ∧
        Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M)) :
    ∃ h ∉ P, Algebra.Etale (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M) ∧
      Module.Finite (Localization.Away h) (Localization.Away h ⊗[B] integralClosure B M) := by
  sorry

end RingTheory.DepthTwo
