/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.Splitting
public import WeilConjectures.RingTheory.Smooth.SectionTruncation

/-!
# Étaleness through the diagonal

Let `O` be a Noetherian local ring and `R` a Noetherian local ring which is formally smooth and
flat over `O` (through `p₂ = algebraMap O R`) with a section `μ : R → O`, and let `τ` be an
involution of `R` with `μ ∘ τ = μ`; put `p₁ = τ ∘ p₂`. Geometrically, `R` is the local ring of
`X ×_S X` at a diagonal point `Δ(x)`, `p₁, p₂` are the two projections, `μ` is the diagonal and
`τ` swaps the factors; `O = 𝒪_{X,x}`.

Let `T` be a finite `O`-algebra and `a, b ∈ O` such that `(a, b)` is a regular pair on `T`,
`p₁ a = p₂ a` (`a` comes from the base `S`), and `T` is étale over `D(a)` and over `D(b)`. If there
is a prime `Q` of the completion `R^` of `R` along `ker μ` lying over the maximal ideal of `O`
(through `p₂`) with `p₁ b ∉ Q`, then `T` is étale over `O`
(`RingTheory.DepthTwo.etale_of_diagonal`).

Proof. The two pullbacks `T' = R ⊗_{p₁} T` and `T'' = R ⊗_{p₂} T` agree along the diagonal. Since
`T'` is étale over `D(a) ∪ D(p₁ b)` and `(a, p₁ b)` is a regular pair on every `T'' / Iⁿ T''`,
the identification `T' / I T' = T = T'' / I T''` lifts uniquely to `T' → T''^`
(as in `RingTheory.DepthTwo.exists_liftAlgHom`); symmetrically (exchanging the roles through `τ`)
it lifts to `T'' → T'^`, and by uniqueness of lifts the two lifts are inverse isomorphisms
`R^ ⊗ T' ≅ R^ ⊗ T''`. At `Q` the left side is étale (as `p₁ b` is invertible), hence so is
`R^_Q ⊗_O T`, and `T` is étale over `O` by faithfully flat descent along `O → R^_Q`.

This is the key step of purity for normal covers of a scheme smooth over a normal base
(`AlgebraicGeometry.Scheme.Hom.mem_etaleLocus_fromNormalization_of_smooth`), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

open TensorProduct IsLocalRing

namespace RingTheory.DepthTwo

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R] [Algebra R O]
  [IsScalarTower O R O] [IsLocalRing O] [IsNoetherianRing O] [IsLocalRing R] [IsNoetherianRing R]
  [Algebra.FormallySmooth O R] [Module.Flat O R]

/-- **Étaleness through the diagonal.** See the module docstring. Here `p₂ = algebraMap O R`, the
section is `algebraMap R O` and `p₁ = τ ∘ p₂`. -/
theorem etale_of_diagonal (τ : R ≃+* R) (hτ : ∀ r, τ (τ r) = r)
    (hτμ : ∀ r, algebraMap R O (τ r) = algebraMap R O r)
    {T : Type*} [CommRing T] [Algebra O T] [Module.Finite O T] {a b : O}
    (ha : τ (algebraMap O R a) = algebraMap O R a) (hT : IsRegularPair a b T)
    [Algebra.Etale (Localization.Away a) (Localization.Away a ⊗[O] T)]
    [Algebra.Etale (Localization.Away b) (Localization.Away b ⊗[O] T)]
    (Q : Ideal (AdicCompletion (RingHom.ker (algebraMap R O)) R)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap O (AdicCompletion (RingHom.ker (algebraMap R O)) R)) =
      maximalIdeal O)
    (hQb : algebraMap R (AdicCompletion (RingHom.ker (algebraMap R O)) R)
      (τ (algebraMap O R b)) ∉ Q) :
    Algebra.Etale O T := by
  sorry

end RingTheory.DepthTwo
