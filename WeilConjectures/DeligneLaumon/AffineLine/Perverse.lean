/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Setup

/-!
# The curve perverse t-structure and Fourier exactness

On a smooth curve the two classes of the perverse t-structure are described purely in terms of
the ordinary cohomology sheaves of a complex: the *upper* class consists of the complexes `K`
with `𝓗ᵃK = 0` for `a > 0` and `𝓗⁰K` of finite support, the *lower* class of those with
`𝓗ᵃK = 0` for `a < -1` and `𝓗⁻¹K` without a nonzero finite-support subsheaf. Their
intersection is the perverse heart. The Fourier–Deligne transform of the affine line is an
exact equivalence between the perverse hearts of the two dual lines.

## Main declarations

- `AlgebraicGeometry.WeilComplex.IsPerverseUpper`,
  `AlgebraicGeometry.WeilComplex.IsPerverseLower`,
  `AlgebraicGeometry.WeilComplex.IsPerverse`: the two truncation classes on a curve and the
  perverse heart.
- `AlgebraicGeometry.fourierTransform_isEquivalence_and_isPerverse_iff`: `FT_ψ` is an
  equivalence preserving and reflecting perversity.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] {l : ℕ} [Fact l.Prime]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- Blueprint `sk-p-dl-a1-perverse`: Fourier exactness on a curve. The upper truncation class
of the perverse t-structure on a smooth curve: `𝓗ᵃK = 0` for `a > 0`, and `𝓗⁰K` has finite
support. -/
def IsPerverseUpper (K : WeilComplex k₀ l X) : Prop :=
  (∀ a : ℤ, 0 < a → IsZero ((homologySheaf a).obj K)) ∧
    (WeilSheaf.support ((homologySheaf (0 : ℤ)).obj K)).Finite

/-- Blueprint `sk-p-dl-a1-perverse`: Fourier exactness on a curve. The lower truncation class
of the perverse t-structure on a smooth curve: `𝓗ᵃK = 0` for `a < -1`, and `𝓗⁻¹K` has no
nonzero subsheaf of finite support. -/
def IsPerverseLower (K : WeilComplex k₀ l X) : Prop :=
  (∀ a : ℤ, a < -1 → IsZero ((homologySheaf a).obj K)) ∧
    ∀ (G : WeilSheaf k₀ l X) (i : G ⟶ (homologySheaf (-1 : ℤ)).obj K), Mono i →
      (WeilSheaf.support G).Finite → IsZero G

/-- Blueprint `sk-p-dl-a1-perverse`: Fourier exactness on a curve. A Weil complex on a smooth
curve is *perverse* if it lies in both truncation classes. -/
def IsPerverse (K : WeilComplex k₀ l X) : Prop := K.IsPerverseUpper ∧ K.IsPerverseLower

end WeilComplex

variable {k₀ : Type u} [Field k₀] {l : ℕ} [Fact l.Prime]

/-- Blueprint `sk-p-dl-a1-perverse`: Fourier exactness on a curve. The Fourier–Deligne
transform `FT_ψ` is an exact equivalence of the perverse categories of the two dual affine
lines: it is an equivalence of the bounded derived categories, and a Weil complex is perverse
exactly when its transform is. -/
theorem fourierTransform_isEquivalence_and_isPerverse_iff (ψ : AddChar k₀ (PadicAlgCl l)) :
    (fourierTransform (l := l) ψ).IsEquivalence ∧
      ∀ K : WeilComplex k₀ l (affineLine k₀),
        K.IsPerverse ↔ ((fourierTransform ψ).obj K).IsPerverse := by
  sorry

end AlgebraicGeometry
