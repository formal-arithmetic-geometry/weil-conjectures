/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic

/-!
# Total complexes of first quadrant double complexes

A double complex `K : HomologicalComplex₂ C (up ℕ) (up ℕ)` in a category with finite coproducts
has a total complex: the objects `K.X p q` with `p + q = n` form a finite family.

When `C` is abelian, filtering the total complex `Tot K` by the columns `p' ≥ p` gives a first
quadrant cohomological spectral sequence with `E₁^{p, q} = H^q(K^{p, •})`, the differential `d₁`
being induced by the horizontal differential `d_I`, hence `E₂^{p, q} = H^p_I H^q_{II}(K)`,
abutting to `H^{p + q}(Tot K)` with the image filtration.

## Main statements

- `HomologicalComplex₂.exists_spectralSequence`: the first spectral sequence of a first quadrant
  double complex.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C]

instance hasTotal_up_nat (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    K.HasTotal (ComplexShape.up ℕ) := fun n ↦ by
  have : Finite ((ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ)) ⁻¹' {n}) := by
    refine Set.Finite.to_subtype ((Set.finite_Iic (n, n)).subset ?_)
    rintro ⟨p, q⟩ (h : p + q = n)
    simp only [Set.mem_Iic, Prod.mk_le_mk]
    omega
  infer_instance

/-- **The first spectral sequence of a first quadrant double complex.** For a first quadrant
double complex `K` in an abelian category, the filtration of the total complex by the columns
gives a first quadrant cohomological spectral sequence with
`E₂^{p, q} ≅ H^p_I H^q_{II}(K)` — the `p`-th cohomology of the complex
`p ↦ H^q(K^{p, •})` whose differential is induced by the horizontal differential of `K` —
abutting to the cohomology `H^{p + q}(Tot K)` of the total complex.

This is the first of the two spectral sequences of a double complex.

(blueprint: `thm-sp-double-complex-spectral-sequences`) -/
theorem exists_spectralSequence {C : Type*} [Category* C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    ∃ E : E₂CohomologicalSpectralSequenceNat C,
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology p)) ∧
      E.AbutsTo fun n ↦ (K.total (ComplexShape.up ℕ)).homology n :=
  sorry

end HomologicalComplex₂
