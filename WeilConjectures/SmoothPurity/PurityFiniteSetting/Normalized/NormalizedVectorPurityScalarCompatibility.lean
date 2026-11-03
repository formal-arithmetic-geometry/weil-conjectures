/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityFiniteReduction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Normalized.NormalizedVectorPurityScalarCore

/-! # Fixed-witness scalar compatibility for normalized vector purity.

This module isolates the per-input scalar compatibility calculation from the existential
assembly in `NormalizedVectorPurityScalarReduction`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The scalar reduction equation for fixed normalized witnesses, on each tested input.

Source: current blueprint `sec-smooth-purity/sk-prop-an`,
`cor-pur-vector-bundle-purity.proof.md`, paragraph 2, normalized transpose and assembly step 5.

Proof: expand the prescribed source map and compact-support coefficient map.  The scalar
trace descent identity identifies the scalar extension of the vector integration counit
with the target counit.  The compact-support scalar coherence square is invertible on all
inputs and identifies the source comparison.  Transposing the counit equality under the
actual Brown adjunction gives the displayed `mateMap` equation; invertibility of the two
purity families and of the source comparison then gives invertibility of the mate.  The
coefficient-unit input is the same calculation with the monoidal unit, and the
constructible-finite-Tor disjunction is preserved throughout.  This is strictly the
compatibility part after the line comparison and target normalized family have already
been chosen.
(blueprint: lem-pur-normalized-vector-purity-scalar-compatibility). -/
theorem scalarReduction_compatibility_of_witnesses
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B]
    (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d]
    [HasCompactification (VectorBundleZeroSection.π B d F)]
    (γ : VectorPurityGamma A N hA B d F)
    (hn : VectorPurityGammaNormalized A N hN hA B hB d F γ)
    (hγ : ∀ K : Etale.DerivedCategoryModule A B, IsIso (γ.app K))
    (A' : Type (u + 1)) [CommRing A'] [Finite A'] (φ : A →+* A')
    (hA' : (N : A') = 0)
    (c : (Etale.purityScalarSheaf φ B).obj
        (Scheme.finiteEtaleTateLine B N A hA) ≅
      Scheme.finiteEtaleTateLine B N A' hA')
    (γm : VectorPurityGamma A' N hA' B d F)
    (hnm : VectorPurityGammaNormalized A' N hN hA' B hB d F γm)
    (hγm : ∀ K : Etale.DerivedCategoryModule A' B, IsIso (γm.app K))
    (hc : PurityScalarLineNormalization φ N hA hA' B c) :
    ∀ K : Etale.DerivedCategoryModule A B,
      (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) B K ∨
        K = 𝟙_ _) →
      IsIso (purityScalarSourceMap φ N hA hA' B d F c K) ∧
      IsIso (Etale.ExceptionalCoefficients.compactSupportMap φ
        (HasCompactification.compactification (VectorBundleZeroSection.π B d F))
        ((RfUpper A (VectorBundleZeroSection.π B d F)).obj K)) ∧
      IsIso (Etale.ExceptionalCoefficients.mateMap φ (VectorBundleZeroSection.π B d F) K) ∧
      (Etale.purityScalarExtension φ (VectorBundleZeroSection.scheme B d F)).map
          (γ.app K) ≫
          Etale.ExceptionalCoefficients.mateMap φ (VectorBundleZeroSection.π B d F) K =
        purityScalarSourceMap φ N hA hA' B d F c K ≫
          γm.app ((Etale.purityScalarExtension φ B).obj K) := by
  letI := (Etale.vectorIntegration_geometry B d F).1
  letI := (Etale.vectorIntegration_geometry B d F).2.1
  letI := (Etale.vectorIntegration_geometry B d F).2.2
  intro K hK
  have hcore := scalar_source_compatibility_core A N hN hA B hB d F γ hn hγ
    A' φ hA' c γm hnm hγm hc K hK
  letI : IsIso (purityScalarSourceMap φ N hA hA' B d F c K) := hcore.1
  refine ⟨hcore.1, ?_, ?_, hcore.2⟩
  · have hgeom := Etale.etaleCompactScalarCoherence φ
      (VectorBundleZeroSection.π B d F)
      (HasCompactification.compactification (VectorBundleZeroSection.π B d F))
    exact hgeom.1 ((RfUpper A (VectorBundleZeroSection.π B d F)).obj K)
  · have hgeom := Etale.etaleCompactScalarCoherence φ
      (VectorBundleZeroSection.π B d F)
      (HasCompactification.compactification (VectorBundleZeroSection.π B d F))
    have hq := hgeom.1 ((RfUpper A (VectorBundleZeroSection.π B d F)).obj K)
    letI : IsIso (Etale.ExceptionalCoefficients.compactSupportMap φ
        (HasCompactification.compactification (VectorBundleZeroSection.π B d F))
        ((RfUpper A (VectorBundleZeroSection.π B d F)).obj K)) := hq
    letI : IsIso ((Etale.purityScalarExtension φ
        (VectorBundleZeroSection.scheme B d F)).map (γ.app K)) := by
      infer_instance
    letI : IsIso (γm.app ((Etale.purityScalarExtension φ B).obj K)) := hγm _
    have hi : IsIso (purityScalarSourceMap φ N hA hA' B d F c K ≫
        γm.app ((Etale.purityScalarExtension φ B).obj K)) := by
      infer_instance
    have hleft : IsIso ((Etale.purityScalarExtension φ
        (VectorBundleZeroSection.scheme B d F)).map (γ.app K) ≫
        Etale.ExceptionalCoefficients.mateMap φ (VectorBundleZeroSection.π B d F) K) := by
      rw [hcore.2]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((Etale.purityScalarExtension φ (VectorBundleZeroSection.scheme B d F)).map
        (γ.app K))
      (Etale.ExceptionalCoefficients.mateMap φ (VectorBundleZeroSection.π B d F) K)

end WeilConjectures.PurityFiniteSetting
