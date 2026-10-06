/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
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
- `AlgebraicGeometry.WeilComplex.CurvePerverseHeart`: the full subcategory of curve perverse
  Weil complexes.
- `AlgebraicGeometry.isCurvePerverse_fourierTransform_obj_iff`: `FT_ψ` preserves and reflects
  perversity.
- `AlgebraicGeometry.simple_fourierTransform_obj`: `FT_ψ` preserves simple perverse objects.
- `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.simple_middleExtension` and
  `AlgebraicGeometry.exists_of_simple_curvePerverseHeart`: the simple perverse objects of the
  affine line are the punctual ones and the middle extensions of irreducible lisse sheaves.
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

/-- Curve perversity is invariant under isomorphism: the cohomology sheaves of isomorphic
complexes are isomorphic, hence have the same support. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms
    (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X)) where
  of_iso {K K'} e h := by
    refine ⟨⟨fun a ha ↦ (h.1.1 a ha).of_iso ((homologySheaf a).mapIso e).symm, ?_⟩,
      ⟨fun a ha ↦ (h.2.1 a ha).of_iso ((homologySheaf a).mapIso e).symm,
        fun G i _ hG ↦ h.2.2 G (i ≫ (homologySheaf (-1 : ℤ)).map e.inv) inferInstance hG⟩⟩
    rw [← WeilSheaf.support_congr ((homologySheaf (0 : ℤ)).mapIso e)]
    exact h.1.2

variable (k₀ l X) in
/-- The *curve perverse heart*: the full subcategory of curve perverse Weil complexes. Its
monomorphisms are those of the heart, so its simple objects are the simple perverse sheaves.
(blueprint: `sk-p-dl-a1-perverse`) -/
abbrev CurvePerverseHeart : Type _ :=
  ObjectProperty.FullSubcategory (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X))

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

/-- `FT_ψ` preserves simple objects of the curve perverse heart: by Fourier inversion
(`AlgebraicGeometry.isEquivalence_fourierTransform`) and perversity
(`AlgebraicGeometry.isCurvePerverse_fourierTransform_obj_iff`) it restricts to an
autoequivalence of the heart, and equivalences preserve simple objects.
(blueprint: `prop-a1-fourier-middle-extension`, Step 1) -/
theorem simple_fourierTransform_obj (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    (K : WeilComplex.CurvePerverseHeart k₀ l (affineLine k₀)) [Simple K] :
    Simple (⟨(fourierTransform ψ).obj K.obj,
      (isCurvePerverse_fourierTransform_obj_iff ψ hψ K.obj).2 K.property⟩ :
        WeilComplex.CurvePerverseHeart k₀ l (affineLine k₀)) := by
  have := isEquivalence_fourierTransform (l := l) ψ hψ
  let P : ObjectProperty (WeilComplex k₀ l (affineLine k₀)) := WeilComplex.IsCurvePerverse
  have hP : P.inverseImage (fourierTransform ψ).asEquivalence.functor = P :=
    funext fun K ↦ propext (isCurvePerverse_fourierTransform_obj_iff ψ hψ K)
  exact simple_obj ((fourierTransform ψ).asEquivalence.congrFullSubcategory hP).functor K

-- TODO(adic): needs the description of the cohomology sheaves of `(j_*M)[1]` and the absence
-- of punctual subsheaves of `j_*M`.
/-- The middle extension `(j_*M)[1]` of a lisse sheaf on a dense open of the affine line is curve
perverse: its only cohomology sheaf is `𝓗⁻¹ = j_*M`, which has no nonzero subsheaf of finite
support. (blueprint: `prop-a1-curve-perverse-simples`) -/
theorem WeilSheaf.LisseOnDenseOpen.isCurvePerverse_middleExtension
    (D : WeilSheaf.LisseOnDenseOpen k₀ l) : D.middleExtension.IsCurvePerverse := by
  sorry

-- TODO(adic): needs the abelian structure of the perverse heart and intermediate extensions.
/-- The middle extension `(j_*M)[1]` of an irreducible lisse sheaf is a simple object of the
curve perverse heart. (blueprint: `prop-a1-curve-perverse-simples`) -/
theorem WeilSheaf.LisseOnDenseOpen.simple_middleExtension (D : WeilSheaf.LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse) :
    Simple (⟨D.middleExtension, D.isCurvePerverse_middleExtension⟩ :
      WeilComplex.CurvePerverseHeart k₀ l (affineLine k₀)) := by
  sorry

-- TODO(adic): needs the abelian structure of the perverse heart and intermediate extensions.
/-- The simple objects of the curve perverse heart of the affine line are punctual sheaves in
degree `0` (in the form: sheaves of finite support) and the middle extensions `(j_*M)[1]` of
irreducible lisse sheaves `M` on dense opens. (blueprint: `prop-a1-curve-perverse-simples`) -/
theorem exists_of_simple_curvePerverseHeart
    (K : WeilComplex.CurvePerverseHeart k₀ l (affineLine k₀)) [Simple K] :
    (∃ G : WeilSheaf k₀ l (affineLine k₀), (WeilSheaf.support G).Finite ∧
      Nonempty (K.obj ≅ WeilSheaf.toComplex.obj G)) ∨
    ∃ D : WeilSheaf.LisseOnDenseOpen k₀ l, D.sheaf.IsIrreducibleLisse ∧
      Nonempty (K.obj ≅ D.middleExtension) := by
  sorry

end AlgebraicGeometry
