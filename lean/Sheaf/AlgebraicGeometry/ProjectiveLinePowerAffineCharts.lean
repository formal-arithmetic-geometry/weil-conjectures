/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
import Sheaf.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Standard affine charts of a fibre power of the projective line

Source: Stacks Project, Constructions, Section 27.13 (Tag 01ND), and Schemes,
Tags 01JR and 01JQ (blueprint: lem-weil-pbc-p1-power-affine-charts).
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProjectiveSpace

/-- The standard charts of an `n`-fold fibre product of projective lines cover it, and their
restrictions over an affine base have polynomial coordinate rings.
Source: Stacks Project, Tags 01ND, 01JR, 01JQ
(blueprint: lem-weil-pbc-p1-power-affine-charts).

`c` is the product cone in `Over S` of `n` copies of `P¹_S = ℙ(ULift (Fin 2); S)`: its point
is `X`, its projections are `prᵢ = (c.proj i).left`, and its structure morphism is
`pₙ = c.pt.hom`. `𝒪(1) = twist _ S 1` is `ρ^* 𝒪_{P¹_ℤ}(1)` along `ρ = toProjInt`, with the
pulled-back coordinate sections `T_k = twistOneSection _ S k`. `Lᵢ` is
`(tensorPullback prᵢ).obj 𝒪(1)` and `xᵢ`, `yᵢ` are the images of `T₀`, `T₁` under the unit
of the chosen adjunction `tensorPullback prᵢ ⊣ pushforward prᵢ`. A subset `A` is encoded
by `a : Fin n → ULift (Fin 2)`, `a i = 1` for `i ∈ A` (denominator `yᵢ`) and `a i = 0`
otherwise (denominator `xᵢ`); `U_A` is the intersection of the non-vanishing loci of the
selected denominators. The variable `X i` is sent to the unique function `zᵢ` resp. `wᵢ`
with `(other section) = (function) • (denominator)` on the chart.

Proof:
1. The two standard opens of each projective line cover it, trivialize `O(1)` by their
   denominator sections, and over `Spec R` have coordinate rings `R[T₀/T₁]` or `R[T₁/T₀]`
   (lem-weil-pbc-projective-space-standard-charts).
2. Nonvanishing loci pull back under the projections; the denominator is a free generator,
   so the pulled-back affine coordinate is the unique quotient function
   (lem-weil-pbc-invertible-pullback-tensor and the standard-charts lemma).
3. At each point choose a nonzero denominator in each factor. These `2^n` choices cover `X`.
4. Over an affine open `V`, the intersection is the fibre product of the selected charts
   over `V`. Induct on the factors, using lem-weil-pbc-open-fibre-product (Tag 01JR).
5. A fibre product of affine spectra is the spectrum of the tensor product of their rings
   (lem-weil-pbc-fibre-product-affine-spectra). The tensor product of these one-variable
   polynomial rings is the polynomial ring on `Fin n` (lem-weil-pbc-polynomial-tensor-product).
   Its variables are the pulled-back chart coordinates. This proves the affine assertion
   and gives the displayed isomorphism with its coefficient and variable equations. -/
theorem projectiveLinePower_affineCharts (S : Scheme.{u}) (n : ℕ) (_hn : 1 ≤ n)
    (c : Fan (fun _ : Fin n ↦ Over.mk (ℙ(ULift.{u} (Fin 2); S) ↘ S)))
    (_hc : IsLimit c) :
    (⋃ a : Fin n → ULift.{u} (Fin 2), ⋂ i : Fin n,
      Scheme.Modules.nonvanishingLocus
        ((Scheme.Modules.tensorPullback (c.proj i).left).obj (twist (ULift.{u} (Fin 2)) S 1))
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
          (c.proj i).left)).unit.app (twist (ULift.{u} (Fin 2)) S 1)).val.app (op ⊤)
            (twistOneSection (ULift.{u} (Fin 2)) S (a i)))) = Set.univ ∧
    ∀ (V : S.Opens) (R : CommRingCat.{u}) (eV : V.toScheme ≅ Spec R)
      (a : Fin n → ULift.{u} (Fin 2)) (U : c.pt.left.Opens),
      (U : Set c.pt.left) = (⋂ i : Fin n,
        Scheme.Modules.nonvanishingLocus
          ((Scheme.Modules.tensorPullback (c.proj i).left).obj (twist (ULift.{u} (Fin 2)) S 1))
          (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
            (c.proj i).left)).unit.app (twist (ULift.{u} (Fin 2)) S 1)).val.app (op ⊤)
              (twistOneSection (ULift.{u} (Fin 2)) S (a i)))) ∩
          c.pt.hom.base ⁻¹' (V : Set S) →
      IsAffineOpen U ∧
      ∃ (h : U.toScheme ⟶ V.toScheme) (E : MvPolynomial (Fin n) R ≃+* Γ(c.pt.left, U)),
        h ≫ V.ι = U.ι ≫ c.pt.hom ∧
        (∀ r : R, E (MvPolynomial.C r) =
          U.topIso.hom ((h ≫ eV.hom).appTop ((Scheme.ΓSpecIso R).inv r))) ∧
        ∀ (i : Fin n) (j : {j : ULift.{u} (Fin 2) // j ≠ a i}),
          ((Scheme.Modules.tensorPullback (c.proj i).left).obj
              (twist (ULift.{u} (Fin 2)) S 1)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
              (c.proj i).left)).unit.app (twist (ULift.{u} (Fin 2)) S 1)).val.app (op ⊤)
                (twistOneSection (ULift.{u} (Fin 2)) S j.1)) =
          E (MvPolynomial.X i) •
            ((Scheme.Modules.tensorPullback (c.proj i).left).obj
                (twist (ULift.{u} (Fin 2)) S 1)).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
              (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
                (c.proj i).left)).unit.app (twist (ULift.{u} (Fin 2)) S 1)).val.app (op ⊤)
                  (twistOneSection (ULift.{u} (Fin 2)) S (a i))) := by
  sorry

end AlgebraicGeometry.ProjectiveSpace
