/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityDirectSum

/-! # Ordered direct sums of independently integration-normalized vector purity maps. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The specified compatibility law for independently integration-normalized purity.
Source: current blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.

Proof: Use the finite locally free rank of the biproduct to form the sum bundle. Independently
normalize the family for the second factor and for the sum. The ordered geometric trace identity,
compact-support composition and base change identify the counit of the two-factor construction
with integration for the sum. Adjunction injectivity identifies this construction with the
independently normalized sum family. Even shifts give sign one. Independence of compactification
supplies the displayed actual compactification triangle. Rank zero uses the unit maps; empty
schemes have unique maps.
(blueprint: lem-pur-normalized-vector-purity-direct-sum). -/
theorem vectorIntegrationCounit_directSum
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (γ : VectorPurityGamma A N hA B d F)
    (hn : VectorPurityGammaNormalized A N hN hA B hB d F γ) :
    PurityDirectSumEquation A N hN hA B hB d F γ := by sorry

end WeilConjectures.PurityFiniteSetting
