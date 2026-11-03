/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityFiniteReduction

/-! # Core source-map compatibility for normalized vector purity.

This is the source-map and mate equation portion of fixed-witness scalar compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The prescribed scalar source map is invertible and intertwines normalized purity families.

Source: current blueprint `sec-smooth-purity/sk-prop-an`,
`cor-pur-vector-bundle-purity.proof.md`, paragraph 2, normalized transpose and assembly step 5.

Proof: identify the ordered scalar tensor and pullback comparison with the normalized source map
using the pure-root generator equations.  The finite Tate balancing, scalar tensorator, and
pullback comparison are invertible, so the source map is invertible.  Apply the scalar trace
descent equation to the vector integration counit, then transpose it under the Brown adjunction.
The normalized counit equations for both witnesses identify the resulting transpose with the
specified `mateMap`; injectivity of the adjunction hom equivalence gives the displayed equation.
The argument is componentwise and includes the coefficient-unit input and the constructible
finite-Tor disjunction.
(blueprint: lem-pur-normalized-vector-purity-scalar-source-core). -/
theorem scalar_source_compatibility_core
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
      (Etale.purityScalarExtension φ (VectorBundleZeroSection.scheme B d F)).map
          (γ.app K) ≫
          Etale.ExceptionalCoefficients.mateMap φ (VectorBundleZeroSection.π B d F) K =
        purityScalarSourceMap φ N hA hA' B d F c K ≫
          γm.app ((Etale.purityScalarExtension φ B).obj K) := by
  sorry

end WeilConjectures.PurityFiniteSetting
