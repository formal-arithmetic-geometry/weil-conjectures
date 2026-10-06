/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex

/-!
# The first spectral sequence of a first quadrant double complex

Let `K : HomologicalComplex₂ C (up ℕ) (up ℕ)` be a first quadrant double complex in an abelian
category, so that `K.X p` is the complex `K^{p, •}` and `K.d p (p + 1)` is the horizontal
differential `d_I`. Filtering the total complex `Tot K` by the columns `p' ≥ p` gives a first
quadrant cohomological spectral sequence with
`E₁^{p, q} = H^q(K^{p, •})`, the differential `d₁` being induced by `d_I`, hence
`E₂^{p, q} = H^p_I H^q_{II}(K)`, abutting to `H^{p + q}(Tot K)` with the image filtration.

## Main statements

- `HomologicalComplex₂.exists_spectralSequence`: the first spectral sequence of a first quadrant
  double complex.
-/

@[expose] public section

namespace HomologicalComplex₂

open CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

/-- **The first spectral sequence of a first quadrant double complex.** For a first quadrant
double complex `K` in an abelian category, the filtration of the total complex by the columns
gives a first quadrant cohomological spectral sequence with
`E₂^{p, q} ≅ H^p_I H^q_{II}(K)` — the `p`-th cohomology of the complex
`p ↦ H^q(K^{p, •})` whose differential is induced by the horizontal differential of `K` —
abutting to the cohomology `H^{p + q}(Tot K)` of the total complex.

This is the first of the two spectral sequences of a double complex.

(blueprint: `thm-sp-double-complex-spectral-sequences`) -/
theorem exists_spectralSequence
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    ∃ E : E₂CohomologicalSpectralSequenceNat C,
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology p)) ∧
      E.AbutsTo fun n ↦ (K.total (ComplexShape.up ℕ)).homology n :=
  sorry

end HomologicalComplex₂
