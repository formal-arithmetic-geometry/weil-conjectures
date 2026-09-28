/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.AffineLine.Defs

/-!
# The curve perverse t-structure and Fourier exactness

On a smooth curve the two classes of the perverse t-structure are described purely in terms of
the ordinary cohomology sheaves of a complex: the *upper* class consists of the complexes `K`
with `𝓗ᵃK = 0` for `a > 0` and `𝓗⁰K` of finite support, the *lower* class of those with
`𝓗ᵃK = 0` for `a < -1` and `𝓗⁻¹K` without a nonzero finite-support subsheaf. Their
intersection is the perverse heart. The Fourier–Deligne transform of the affine line is an
exact equivalence between the perverse hearts of the two dual lines.

The three classes below are stated for an arbitrary `k₀`-scheme, but they agree with the
perverse t-structure only on a smooth curve — whence the names. On a scheme of dimension at
least two the perverse t-structure is not described by these two conditions, and the names
`IsCurvePerverse*` keep the description distinct from the genuine t-structure that
`sec-six-functors` will build.

That the Fourier transform is an equivalence at all is Fourier inversion, which belongs to the
block `sec-fourier-transform`: it is `AlgebraicGeometry.isEquivalence_fourierTransform`. What
this subsection adds is that the equivalence is exact for the perverse t-structures.

## Main declarations

- `AlgebraicGeometry.WeilComplex.IsCurvePerverseUpper`,
  `AlgebraicGeometry.WeilComplex.IsCurvePerverseLower`,
  `AlgebraicGeometry.WeilComplex.IsCurvePerverse`: the two truncation classes on a curve and
  the perverse heart.
- `AlgebraicGeometry.isCurvePerverse_fourierTransform_obj_iff`: `FT_ψ` preserves and reflects
  perversity.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The upper truncation class of the perverse t-structure on a smooth curve: `𝓗ᵃK = 0` for
`a > 0`, and `𝓗⁰K` has finite support. (blueprint: `sk-p-dl-a1-perverse`) -/
def IsCurvePerverseUpper (K : WeilComplex k₀ l X) : Prop :=
  (∀ a : ℤ, 0 < a → IsZero ((homologySheaf a).obj K)) ∧
    (WeilSheaf.support ((homologySheaf (0 : ℤ)).obj K)).Finite

/-- The lower truncation class of the perverse t-structure on a smooth curve: `𝓗ᵃK = 0` for
`a < -1`, and `𝓗⁻¹K` has no nonzero subsheaf of finite support.
(blueprint: `sk-p-dl-a1-perverse`) -/
def IsCurvePerverseLower (K : WeilComplex k₀ l X) : Prop :=
  (∀ a : ℤ, a < -1 → IsZero ((homologySheaf a).obj K)) ∧
    ∀ (G : WeilSheaf k₀ l X) (i : G ⟶ (homologySheaf (-1 : ℤ)).obj K), Mono i →
      (WeilSheaf.support G).Finite → IsZero G

/-- A Weil complex on a smooth curve is *curve perverse* if it lies in both truncation classes.
(blueprint: `sk-p-dl-a1-perverse`) -/
def IsCurvePerverse (K : WeilComplex k₀ l X) : Prop :=
  K.IsCurvePerverseUpper ∧ K.IsCurvePerverseLower

end WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/--
The Fourier–Deligne transform along a nontrivial additive character is exact for the curve
perverse t-structures of the two dual affine lines: a Weil complex is curve perverse exactly
when its transform is.

```
  Dᵇ(A₀) ──────FT_ψ──────▶ Dᵇ(A'₀)
     ∪                        ∪
  Perv(A₀) ────≃ exact───▶ Perv(A'₀)
```
(blueprint: `sk-p-dl-a1-perverse`)
-/
theorem isCurvePerverse_fourierTransform_obj_iff (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    (K : WeilComplex k₀ l (affineLine k₀)) :
    ((fourierTransform ψ).obj K).IsCurvePerverse ↔ K.IsCurvePerverse := by
  sorry

end AlgebraicGeometry
