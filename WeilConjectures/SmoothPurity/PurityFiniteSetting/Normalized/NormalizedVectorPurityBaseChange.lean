/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityBaseChange
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityBundle
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityBaseChangeComponent

/-! # Base change of the independently integration-normalized vector purity family. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

/-- The specified compatibility law for independently integration-normalized purity.
Source: current blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.

Proof: Construct the independently normalized family on the Cartesian bundle. Compact-support
projection exchange and geometric trace descent identify the integration counits. Transpose that
equality under the two Brown adjunctions. It is exactly the canonical exceptional base-change
mate, by the mate counit identity. The source associator and both normalized families are
invertible, hence the exceptional exchange is invertible on every tested input. For an arbitrary
Cartesian bundle presentation first identify it with the canonical pullback; the normalized
fundamental class is invariant under this isomorphism. Rank zero uses the unit maps; empty schemes
have unique maps.
(blueprint: lem-pur-normalized-vector-purity-base-change). -/
theorem vectorIntegrationCounit_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (γ : VectorPurityGamma A N hA B d F)
    (hn : VectorPurityGammaNormalized A N hN hA B hB d F γ)
    (hi : ∀ K : Etale.DerivedCategoryModule A B, IsIso (γ.app K)) :
    PurityBaseChangeEquation A N hN hA B hB d F γ := by
  intro B' _ g hB' F' _ _ _ g' sq
  obtain ⟨γ', hn', hi'⟩ := (vectorBundleNormalized A N hN hA B' hB' d F').2
  refine ⟨γ', hn', fun K ↦ ?_⟩
  exact vectorIntegrationCounit_baseChange_component A N hN hA hB hB' d F F' sq
    γ γ' hn hn' hi hi' K.obj

end WeilConjectures.PurityFiniteSetting
