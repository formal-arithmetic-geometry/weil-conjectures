/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorPurityFiniteReduction
import WeilConjectures.AlgebraicGeometry.NormalizedVectorPurityBundle
import WeilConjectures.AlgebraicGeometry.NormalizedVectorPurityScalarLineWitness
import WeilConjectures.AlgebraicGeometry.NormalizedVectorPurityScalarCompatibility

/-! # Scalar reduction of independently integration-normalized vector purity. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The specified compatibility law for independently integration-normalized purity.
Source: current blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.

Proof: Map the annihilator equation through phi. Use the uniquely pure-root-normalized finite Tate
balancing and its ordered shifted tensor powers. Its source maps are invertible, including nonflat
coefficient extensions. Compact-support scalar coherence makes the actual compact comparison
invertible. Scalar trace descent and projection coherence identify the integration counits.
Transpose their equality, using the inverse of this compact comparison; its adjunct is the
published scalar mate. Since both purity families and the source comparison are invertible, so is
the scalar mate. The same equation at the coefficient unit gives the required unit compatibility.
Rank zero uses the unit maps; empty schemes have unique maps.
(blueprint: lem-pur-normalized-vector-purity-scalar-reduction). -/
theorem vectorIntegrationCounit_scalarReduction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (γ : VectorPurityGamma A N hA B d F)
    (hn : VectorPurityGammaNormalized A N hN hA B hB d F γ)
    (hi : ∀ K : Etale.DerivedCategoryModule A B, IsIso (γ.app K))
    (A' : Type (u + 1)) [CommRing A'] [Finite A'] (φ : A →+* A') :
    PurityScalarReductionEquation φ N hN hA B hB d F γ := by
  obtain ⟨hA', c, hc⟩ := exists_purityScalarLineNormalization
    A N hN hA B hB A' φ
  have hnorm := vectorBundleNormalized A' N hN hA' B hB d F
  obtain ⟨_, γm, hnm, hγm⟩ := hnorm
  have hcompat := scalarReduction_compatibility_of_witnesses
    A N hN hA B hB d F γ hn hi A' φ hA' c γm hnm hγm hc
  exact ⟨hA', c, γm, hnm, hc, hcompat⟩

end WeilConjectures.PurityFiniteSetting
