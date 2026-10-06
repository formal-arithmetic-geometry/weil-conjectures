/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
public import WeilConjectures.AlgebraicGeometry.DensePoints
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Riemann–Roch, Serre duality and the twist lemma for curves

Let `X` be a smooth proper curve over a field `k`. Its genus `g = dim_k H^1(X, 𝒪_X)` is
`AlgebraicGeometry.Scheme.arithmeticGenus`, and the degree `deg ℒ = χ(ℒ) - χ(𝒪_X)` of an
invertible sheaf on it is `AlgebraicGeometry.Scheme.Modules.degree`. We state Riemann–Roch,
Serre duality with the canonical module `Ω¹_{X/k}`, and the two statements about line bundles on
the base change `X_K` of `X` along a field extension `K/k` that the Picard framework needs.

## Implementation notes

Riemann–Roch in the form `χ(𝒪_X) = 1 - g` needs `H⁰(X, 𝒪_X) = k`
(`AlgebraicGeometry.Scheme.GlobalSectionsBijective`): `ℙ¹_ℂ` viewed as a curve over `ℝ` is
smooth and proper of genus `0`, but `χ(𝒪) = dim_ℝ ℂ = 2 ≠ 1 - 0`. Ampleness of line bundles of
positive degree needs it too: on `X = ℙ¹ ⊔ ℙ¹` the line bundle `𝒪(2) ⊔ 𝒪(-1)` has degree `1` but
is not ample. The statements about the degree of divisors and Serre duality do not need it.

The degree of a line bundle is *defined* cohomologically, as `deg ℒ = χ(ℒ) - χ(𝒪_X)`. Its
identification with the divisor degree is stated in three parts. An effective Cartier divisor
`D` is an invertible ideal sheaf `J = 𝒪_X(-D)`, its line bundle is `𝒪_X(D) = J.toModulesᵛ`, and
its degree is `dim_k Γ(D, 𝒪_D) = (J.subschemeι ≫ X ↘ Spec k).finrankΓ`. Then the χ-degree of
`𝒪_X(D)` is the degree of `D`
(`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules`), the χ-degree is
additive (`AlgebraicGeometry.Scheme.Modules.degree_tensorObj`), and every line bundle is
`𝒪_X(D₁) ⊗ 𝒪_X(D₂)⁻¹` (`AlgebraicGeometry.Scheme.Modules.exists_tensorObj_dual_toModules_iso`).
Together they say that `deg ℒ = deg D₁ - deg D₂` is the divisor degree of `ℒ`, so that
`χ(ℒ) = deg D + 1 - g` is a genuine statement about divisors.

The blueprint states Riemann–Roch for *coherent* `ℱ`, with
`deg ℱ = length(torsion) + deg det(ℱ/torsion)`. The statements below assume `ℱ` finite
locally free, which is a genuine narrowing; it will have to be undone once coherence and the
torsion and determinant of a coherent sheaf exist.

The Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerChar` is a `finsum`, so it is
junk unless the cohomology vanishes in large degrees. On a curve that is Grothendieck vanishing,
`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt`, which is what makes
every statement of this file about `χ`, `deg` and the genus meaningful.

Ampleness is `AlgebraicGeometry.IsAmple` of
`WeilConjectures/AlgebraicGeometry/Modules/Ample.lean`, shared with the abelian-variety block.
The dual `ℱᵛ = Hom(ℱ, 𝒪_X)` of a sheaf of modules is the internal hom of
`WeilConjectures/AlgebraicGeometry/Modules/Dual.lean`, and the tensor product is the monoidal
structure on `X.Modules` of `WeilConjectures/AlgebraicGeometry/Modules/Invertible.lean`. The
canonical module is `Ω¹_{X/k} = AlgebraicGeometry.Scheme.Hom.relativeDifferentials` for curves
and `𝒪_X` in dimension `0`.

Serre duality is stated as the existence of a natural isomorphism between two functors on finite
locally free modules. The isomorphism is the one induced by the trace pairing
`H^q(ℱ) ⊗ H^p(ℱᵛ ⊗ ω_X) → H¹(ω_X) → k`, whose last map is the trace `t_X = ∑_x res_x`, the sum
over closed points of Tate's `k`-linear residues (Tate, *Residues of differentials on curves*).
At a point `x` with `κ(x)/k` separable, `res_x` is `Tr_{κ(x)/k}` of the classical residue.
Tate's residues are not available, so the isomorphism is not given explicitly.

## Main statements

- `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules`,
  `AlgebraicGeometry.Scheme.Modules.degree_tensorObj` and
  `AlgebraicGeometry.Scheme.Modules.exists_tensorObj_dual_toModules_iso`: the χ-degree is the
  divisor degree.
- `AlgebraicGeometry.Scheme.isAmple_of_degree_pos`: positive degree implies ample.
- `AlgebraicGeometry.Scheme.isAffine_compl_of_isAmple`: the complement of an effective Cartier
  divisor with ample line bundle is affine.
- `AlgebraicGeometry.Scheme.eulerChar_free_eq`, `AlgebraicGeometry.Scheme.eulerChar_unit_eq`
  and `AlgebraicGeometry.Scheme.finrankH_zero_eq`: Riemann–Roch for curves.
- `AlgebraicGeometry.Scheme.degree_relativeDifferentials`: `deg Ω¹_{X/k} = 2g - 2`.
- `AlgebraicGeometry.Scheme.serreDuality` and `AlgebraicGeometry.Scheme.serreDuality_zero`:
  Serre duality on curves and in dimension `0`.
- `AlgebraicGeometry.Scheme.finrankH_relativeDifferentials_zero_eq_arithmeticGenus` and
  `AlgebraicGeometry.Scheme.genus_eq_arithmeticGenus`: `h⁰(Ω¹) = h¹(𝒪)`.
- `AlgebraicGeometry.Scheme.degree_eq_genus`: a line bundle with `h^0 = 1` and no higher
  cohomology has degree `g`.
- `AlgebraicGeometry.Scheme.exists_isInvertible_twist`: the twist lemma.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

section Sections

/-- **A non-zero `H⁰` has a non-zero global section.** If `H⁰(X, ℳ) ≠ 0`, then there is a
non-zero morphism `s : 𝒪_X ⟶ ℳ`: `H⁰(X, ℳ) = Γ(X, ℳ)` and a global section `m` of `ℳ` is the
image of `1` under a unique `s : 𝒪_X ⟶ ℳ`. -/
theorem Modules.exists_ne_zero_of_nontrivial_H_zero {X : Scheme.{u}} (M : X.Modules)
    [Nontrivial (M.H 0)] : ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨y, hy⟩ := exists_ne (0 : M.H 0)
  let e := Sheaf.H.equiv₀ ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
    (Limits.isTerminalTop (α := X.Opens))
  let m : Γ(M, ⊤) := e y
  have hm : m ≠ 0 := fun h ↦ hy (e.injective (h.trans e.map_zero.symm))
  let σ : M.sections := PresheafOfModules.sectionsMk
    (fun W ↦ M.val.map (homOfLE le_top : W.unop ⟶ ⊤).op m)
    (fun W _ f ↦ (ConcreteCategory.congr_hom (M.val.map_comp
        (homOfLE le_top : W.unop ⟶ ⊤).op f) _).symm)
  refine ⟨M.unitHomEquiv.symm σ, fun h ↦ hm ?_⟩
  have h1 := congrArg (fun s ↦ s.val (op ⊤)) (M.unitHomEquiv.apply_symm_apply σ)
  rw [h] at h1
  erw [SheafOfModules.unitHomEquiv_apply_coe] at h1
  have h2 : SheafOfModules.Hom.val (0 : 𝟙_ X.Modules ⟶ M) = 0 := rfl
  replace h1 : M.val.map (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤).op m = 0 := h1.symm
  rw [show (homOfLE le_top : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from Subsingleton.elim _ _, op_id,
    M.val.map_id] at h1
  exact h1

/-- **A rational point has degree one.** The closed subscheme of a `k`-rational point
`x : Spec k ⟶ X`, cut out by the ideal sheaf `ker x`, has `dim_k Γ(x, 𝒪) = 1`. -/
theorem Hom.finrankΓ_subschemeι_ker_fieldPoints {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : f.fieldPoints k) : (x.1.ker.subschemeι ≫ f).finrankΓ = 1 := by
  have hx : x.1 ≫ f = 𝟙 _ := by
    rw [x.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rw [← Hom.finrankΓ_id (k := k)]
  refine Hom.finrankΓ_eq_of_iso _ _ (asIso x.1.toImage).symm (Iso.refl _) ?_
  rw [Iso.symm_hom, asIso_inv, Iso.refl_hom, Spec.map_id, Category.comp_id, Category.comp_id,
    IsIso.inv_eq_of_hom_inv_id]
  rw [← Category.assoc, Hom.toImage_imageι, hx]

end Sections

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **Riemann–Roch for curves, divisor degree.** Let `D` be an effective Cartier divisor on a
smooth proper curve `X` over `k`, with invertible ideal sheaf `J = 𝒪_X(-D)`. Then the χ-degree
`χ(𝒪_X(D)) - χ(𝒪_X)` of its line bundle `𝒪_X(D) = J.toModulesᵛ` is the degree
`dim_k Γ(D, 𝒪_D) = ∑_x n_x [κ(x) : k]` of `D`. With
`AlgebraicGeometry.Scheme.eulerChar_unit_eq` this is `χ(𝒪_X(D)) = deg D + 1 - g`.

(blueprint: `sk-thm-picard-rr`) -/
theorem IdealSheafData.IsInvertible.degree_dual_toModules {J : X.IdealSheafData}
    (hJ : J.IsInvertible) :
    J.toModulesᵛ.degree k = (J.subschemeι ≫ X ↘ Spec (.of k)).finrankΓ :=
  -- Twist `0 → 𝒪_X(-D) → 𝒪_X → 𝒪_D → 0` by `𝒪_X(D)`; `𝒪_X(D)|_D ≅ 𝒪_D` since `D` is finite over
  -- `k`, hence semi-local, so `χ(𝒪_X(D)) - χ(𝒪_X) = h⁰(𝒪_D)`.
  sorry

/-- **The line bundle of a rational point has degree one.** Let `D` be an effective Cartier
divisor on a smooth proper curve `X` over `k`, with invertible ideal sheaf `J = 𝒪_X(-D)`, which is
a `k`-rational point: `Γ(D, 𝒪_D) = k` is one-dimensional. Then the χ-degree of `𝒪_X(D)` of
blueprint `def-pc-degree-line-bundle` is `1`, the degree of the divisor `[P]` of `def-sc-pic0`.
For an arbitrary effective `D` the agreement of the two degrees is
`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules`.

(blueprint: `lem-pc-degree-agrees-sc`) -/
theorem IdealSheafData.IsInvertible.degree_dual_toModules_eq_one {J : X.IdealSheafData}
    (hJ : J.IsInvertible) (h : (J.subschemeι ≫ X ↘ Spec (.of k)).finrankΓ = 1) :
    J.toModulesᵛ.degree k = 1 := by
  rw [hJ.degree_dual_toModules, h, Nat.cast_one]

/-- **The degree is additive.** `deg (ℒ ⊗ ℳ) = deg ℒ + deg ℳ` for invertible sheaves on a smooth
proper curve.

(blueprint: `sk-thm-picard-rr`) -/
theorem Modules.degree_tensorObj (ℒ ℳ : X.Modules) [ℒ.IsInvertible] [ℳ.IsInvertible] :
    (ℒ ⊗ₘ ℳ).degree k = ℒ.degree k + ℳ.degree k :=
  sorry

/-- **Every line bundle comes from a divisor.** Every invertible sheaf `ℒ` on a smooth proper
curve is `𝒪_X(D₁) ⊗ 𝒪_X(D₂)⁻¹` for effective Cartier divisors `D₁` and `D₂`, given by
invertible ideal sheaves `J₁ = 𝒪_X(-D₁)` and `J₂ = 𝒪_X(-D₂)`: `ℒ ⊗ 𝒪_X(D₂) ≅ 𝒪_X(D₁)`.

With `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules` and
`AlgebraicGeometry.Scheme.Modules.degree_tensorObj` this gives `deg ℒ = deg D₁ - deg D₂`: the
χ-degree of every line bundle is its divisor degree.

(blueprint: `sk-thm-picard-rr`) -/
theorem Modules.exists_tensorObj_dual_toModules_iso (ℒ : X.Modules) [ℒ.IsInvertible] :
    ∃ J₁ J₂ : X.IdealSheafData, J₁.IsInvertible ∧ J₂.IsInvertible ∧
      Nonempty (ℒ ⊗ₘ J₂.toModulesᵛ ≅ J₁.toModulesᵛ) :=
  sorry

/-- **Positive degree implies ample.** An invertible sheaf of positive degree on a smooth
proper curve over `k` with `H⁰(X, 𝒪_X) = k` is ample.

(blueprint: `sk-thm-picard-rr`, part (G)) -/
theorem isAmple_of_degree_pos [GlobalSectionsBijective k X] (ℒ : X.Modules) [ℒ.IsInvertible]
    (hd : 0 < ℒ.degree k) :
    IsAmple (X ↘ Spec (.of k)) ℒ :=
  sorry

/-- **Affine complement.** Let `D` be an effective Cartier divisor on a smooth proper curve `X`,
with invertible ideal sheaf `J = 𝒪_X(-D)`, whose line bundle `𝒪_X(D) = J.toModulesᵛ` is ample.
Then `X \ Supp D` is affine. The open complement of the support of `D` is presented by an open
immersion `j` whose range is the complement of the support of `J`.

(blueprint: `sk-thm-picard-rr`, part (H)) -/
theorem isAffine_compl_of_isAmple {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (hample : IsAmple (X ↘ Spec (.of k)) J.toModulesᵛ) {V : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] (hj : Set.range j.base = (J.support : Set X)ᶜ) :
    IsAffine V :=
  sorry

variable (k) in
include k in
/-- **Vanishing above the dimension of a curve.** On a smooth proper curve `X` over `k`,
`H^q(X, ℱ) = 0` for every sheaf of modules `ℱ` and every `q ≥ 2`: `X` is noetherian of
dimension at most one, so this is Grothendieck vanishing
`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt`.

(blueprint: `lem-pc-vanishing-above-dim`) -/
theorem Modules.subsingleton_H_of_two_le (ℱ : X.Modules) {q : ℕ} (hq : 2 ≤ q) :
    Subsingleton (ℱ.H q) := by
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  refine subsingleton_H_of_topologicalKrullDim_lt ℱ
    ((topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) 1).trans_lt ?_)
  exact_mod_cast hq

/-- On a smooth proper curve, `χ(ℱ) = h⁰(ℱ) - h¹(ℱ)`, by
`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_two_le`. -/
theorem Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (ℱ : X.Modules) :
    ℱ.eulerChar k = (Modules.finrankH k ℱ 0 : ℤ) - Modules.finrankH k ℱ 1 := by
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  rw [Modules.eulerChar_eq_sum_range k ℱ
    (topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) 1)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- **Rational points are Cartier divisors on smooth curves.** The ideal sheaf `ker x` of a
`k`-rational point `x : Spec k ⟶ X` of a smooth curve `X` over `k` is invertible: the local ring
`𝒪_{X,x}` is regular of dimension one, hence a discrete valuation ring, and its maximal ideal,
the stalk of `ker x`, is generated by a uniformizer.

(blueprint: `lem-sc-point-cartier`) -/
theorem Hom.isInvertible_ker_fieldPoints (x : (X ↘ Spec (.of k)).fieldPoints k) :
    x.1.ker.IsInvertible :=
  sorry

/-- **The ideal sheaf of a rational point has degree `-1`.** For a `k`-rational point `x` of a
smooth proper curve, `𝒪_X(-x) = ker x` has degree `-1`: its dual `𝒪_X(x)` has degree
`dim_k Γ(x, 𝒪_x) = 1`, and `𝒪_X(-x) ⊗ 𝒪_X(x) ≅ 𝒪_X`. -/
theorem degree_toModules_ker_fieldPoints (x : (X ↘ Spec (.of k)).fieldPoints k) :
    x.1.ker.toModules.degree k = -1 := by
  have hJ := Hom.isInvertible_ker_fieldPoints x
  have := hJ.isInvertible_toModules
  have := hJ.isInvertible_dual_toModules
  obtain ⟨e⟩ := Modules.nonempty_tensorObj_dual_iso_unit x.1.ker.toModules
  have h := Modules.degree_tensorObj (k := k) x.1.ker.toModules x.1.ker.toModulesᵛ
  rw [Modules.degree_congr k e, hJ.degree_dual_toModules_eq_one
    ((X ↘ Spec (.of k)).finrankΓ_subschemeι_ker_fieldPoints x)] at h
  have h0 : Modules.degree k (𝟙_ X.Modules) = 0 := Modules.degree_unit k
  omega

end Curve

section RiemannRoch

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GlobalSectionsBijective k X]

/-- **Riemann–Roch for curves, free case.** The Euler characteristic of the free sheaf of rank
`r` on a smooth proper curve `X` over `k` with `H⁰(X, 𝒪_X) = k`, of genus `g`, is
`χ(𝒪_X^{⊕ r}) = r (1 - g)`.

Together with `AlgebraicGeometry.Scheme.Modules.degree`, which measures the degree of a
rank-`r` sheaf against `𝒪_X^{⊕ r}`, this is the content of the Riemann–Roch identity
`χ(ℱ) = deg ℱ + r (1 - g)`.

(blueprint: `sk-thm-picard-rr`) -/
theorem eulerChar_free_eq (r : ℕ) :
    Modules.eulerChar (X := X) k (SheafOfModules.free (ULift.{u} (Fin r))) =
      r * (1 - (arithmeticGenus k X : ℤ)) :=
  sorry

/-- **Riemann–Roch for curves, structure sheaf.** `χ(𝒪_X) = 1 - g` on a smooth proper curve `X`
over `k` with `H⁰(X, 𝒪_X) = k`, of genus `g`.

Without the hypothesis `H⁰(X, 𝒪_X) = k` the statement fails, as for `ℙ¹_ℂ` over `ℝ`, where
`χ(𝒪) = 2`.

(blueprint: `sk-thm-picard-rr`) -/
theorem eulerChar_unit_eq :
    Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf) =
      1 - (arithmeticGenus k X : ℤ) :=
  sorry

/-- **The degree of the canonical module.** `deg Ω¹_{X/k} = 2g - 2` on a smooth proper curve
with `H⁰(X, 𝒪_X) = k`, of genus `g`.

(blueprint: `sk-thm-picard-rr`) -/
theorem degree_relativeDifferentials :
    (X ↘ Spec (.of k)).relativeDifferentials.degree k = 2 * (arithmeticGenus k X : ℤ) - 2 :=
  -- Serre duality gives `h⁰(Ω¹) = g` and `h¹(Ω¹) = h⁰(𝒪_X) = 1`.
  sorry

/-- **Riemann–Roch for curves, `h⁰` of a line bundle of large degree.** A line bundle `ℒ` of
degree `d ≥ 2g - 1` on a smooth proper curve with `H⁰(X, 𝒪_X) = k` of genus `g` has
`h^0(ℒ) = d + 1 - g`; equivalently `h^1(ℒ) = 0`.

(blueprint: `sk-thm-picard-rr`) -/
theorem finrankH_zero_eq (ℒ : X.Modules) [ℒ.IsInvertible]
    (hd : 2 * (arithmeticGenus k X : ℤ) - 1 ≤ ℒ.degree k) :
    (Modules.finrankH k ℒ 0 : ℤ) = ℒ.degree k + 1 - arithmeticGenus k X :=
  sorry

end RiemannRoch

section Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **Serre duality for curves.** Let `X` be a smooth proper curve over `k` with canonical module
`ω_X = Ω¹_{X/k}`, and let `p + q = 1`. Then `ℱ ↦ H^q(X, ℱ)^∨` and `ℱ ↦ H^p(X, ℱᵛ ⊗ Ω¹_{X/k})`
are naturally isomorphic as contravariant functors on finite locally free `ℱ`. That is, there are
`k`-linear isomorphisms `e ℱ : H^q(X, ℱ)^∨ ≅ H^p(X, ℱᵛ ⊗ Ω¹_{X/k})` such that for every
morphism `φ : ℱ ⟶ 𝒢` of finite locally free modules the square
```
  H^q(𝒢)^∨ ───── e 𝒢 ─────▶ H^p(𝒢ᵛ ⊗ Ω¹)
     │                           │
 H^q(φ)^∨                   H^p(φᵛ ▷ Ω¹)
     ▼                           ▼
  H^q(ℱ)^∨ ───── e ℱ ─────▶ H^p(ℱᵛ ⊗ Ω¹)
```
commutes. No hypothesis `H⁰(X, 𝒪_X) = k` is needed.

The case `q = 1` is `AlgebraicGeometry.Scheme.nonempty_dual_H_one_iso`, obtained from a finite flat
morphism `X ⟶ ℙ¹_k` and duality on `ℙ¹_k`; the case `q = 0` is
`AlgebraicGeometry.Scheme.nonempty_dual_H_zero_iso`, deduced from it by biduality.

(blueprint: `sk-thm-picard-duality`, `thm-sc-serre-duality-curve`) -/
theorem serreDuality [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (p q : ℕ) (hpq : p + q = 1) :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.cohomologyFunctor k q).op ⋙ ModuleCat.dualFunctor k ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ Modules.dualFunctor X ⋙
        tensorRight (X ↘ Spec (.of k)).relativeDifferentials ⋙ Modules.cohomologyFunctor k p) := by
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : p = 0 ∧ q = 1 ∨ p = 1 ∧ q = 0 := by omega
  · exact nonempty_dual_H_one_iso
  · exact nonempty_dual_H_zero_iso

/-- **Serre duality in dimension `0`.** Let `X` be smooth and proper of relative dimension `0`
over `k`, i.e. `X = Spec A` with `A` finite étale over `k`, so that the canonical module is
`ω_X = 𝒪_X`. Then `ℱ ↦ H^0(X, ℱ)^∨` and `ℱ ↦ H^0(X, ℱᵛ)` are naturally isomorphic as
contravariant functors on finite locally free `ℱ`: there are `k`-linear isomorphisms
`e ℱ : H^0(X, ℱ)^∨ ≅ H^0(X, ℱᵛ)` such that for every morphism `φ : ℱ ⟶ 𝒢` of finite locally
free modules the square
```
  H^0(𝒢)^∨ ───── e 𝒢 ─────▶ H^0(𝒢ᵛ)
     │                         │
 H^0(φ)^∨                   H^0(φᵛ)
     ▼                         ▼
  H^0(ℱ)^∨ ───── e ℱ ─────▶ H^0(ℱᵛ)
```
commutes. The isomorphism is the one induced by the trace pairing
`H^0(ℱ) ⊗ H^0(ℱᵛ) → H^0(𝒪_X) = A → k`, whose last map is the trace `Tr_{A/k}`. In degrees
`q > 0` both sides vanish.

(blueprint: `sk-thm-picard-duality`) -/
theorem serreDuality_zero [SmoothOfRelativeDimension 0 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.cohomologyFunctor k 0).op ⋙ ModuleCat.dualFunctor k ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ Modules.dualFunctor X ⋙
        Modules.cohomologyFunctor k 0) :=
  sorry

/-- **`h⁰(Ω¹) = h¹(𝒪_X)`.** On a smooth proper curve over `k`,
`dim_k H⁰(X, Ω¹_{X/k}) = dim_k H¹(X, 𝒪_X)`. -/
theorem finrankH_relativeDifferentials_zero_eq_arithmeticGenus
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] :
    Modules.finrankH k (X ↘ Spec (.of k)).relativeDifferentials 0 = arithmeticGenus k X := by
  -- Serre duality for `ℱ = 𝒪_X` and `q = 1`, with `𝒪_Xᵛ ⊗ Ω¹ ≅ Ω¹`.
  obtain ⟨e⟩ := serreDuality (k := k) (X := X) 0 1 rfl
  obtain ⟨d⟩ := Modules.nonempty_dual_unit_iso (X := X)
  let 𝒪 : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩
  have h : Module.finrank k (Module.Dual k (Modules.H (X := X) 𝒪.obj 1)) =
      Modules.finrankH k (𝒪.objᵛ ⊗ (X ↘ Spec (.of k)).relativeDifferentials) 0 :=
    (e.app (op 𝒪)).toLinearEquiv.finrank_eq
  rw [Subspace.dual_finrank_eq] at h
  rw [← Modules.finrankH_congr k (whiskerRightIso d _ ≪≫ λ_ _) 0, ← h]
  rfl

/-- **The two genera agree.** On a smooth proper curve over `k`, the genus
`dim_k Γ(X, Ω¹_{X/k})` of `sk-def-curve` is the arithmetic genus `dim_k H¹(X, 𝒪_X)`, the genus
of blueprint `def-pc-genus`.

(blueprint: `sk-thm-picard-duality`, `lem-pc-genus-agrees-sc`) -/
theorem genus_eq_arithmeticGenus [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] :
    (X ↘ Spec (.of k)).genus = arithmeticGenus k X := by
  rw [Hom.genus_eq_finrankH_zero, finrankH_relativeDifferentials_zero_eq_arithmeticGenus]

end Duality

section FieldExtension

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  (K : Type u) [Field K] [Algebra k K]

/-- **Base change of a smooth curve.** The base change `X_K = X ×_{Spec k} Spec K` of a scheme
`X` smooth of relative dimension `n` over `k` along a field extension `K/k` is smooth of relative
dimension `n` over `K`.

(blueprint: `prop-pc-xk-integral`, part (2)) -/
theorem smoothOfRelativeDimension_baseChange (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of k))] :
    SmoothOfRelativeDimension n (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K)) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
    (IsPullback.of_hasPullback _ _) ‹_›

/-- **Base change of a proper scheme.** The base change `X_K` of a proper `k`-scheme `X` along a
field extension `K/k` is proper over `K`.

(blueprint: `prop-pc-xk-integral`, part (2), and `lem-pc-projective-proper`) -/
theorem isProper_baseChange [IsProper (X ↘ Spec (.of k))] :
    IsProper (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K)) :=
  IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›

/-- **Base change of a geometrically reduced scheme.** The base change `X_K` of a geometrically
reduced `k`-scheme `X`, e.g. a smooth one, along a field extension `K/k` is reduced.

(blueprint: `prop-pc-xk-integral`, part (2)) -/
theorem isReduced_baseChange [GeometricallyReduced (X ↘ Spec (.of k))] :
    IsReduced (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
  GeometricallyReduced.geometrically_isReduced (f := X ↘ Spec (.of k)) _ _ _
    (IsPullback.of_hasPullback _ _)

/-- **The degree is invariant under base change.** Let `X` be proper of finite presentation
over `k`, let `K/k` be a field extension and let `ℳ` be an invertible sheaf on `X`. Then
`deg_{X_K}(ℳ_K) = deg_X(ℳ)`, since `h^q(X_K, ℳ_K) = h^q(X, ℳ)` and
`h^q(X_K, 𝒪_{X_K}) = h^q(X, 𝒪_X)` by flat base change.

(blueprint: `lem-pc-degree-base-change`, part (1)) -/
theorem Modules.degree_pullback_fst [IsProper (X ↘ Spec (.of k))]
    [LocallyOfFinitePresentation (X ↘ Spec (.of k))] (M : X.Modules) [M.IsInvertible] :
    ((Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).degree K = M.degree k := by
  have hχ (N : X.Modules) [N.IsInvertible] :
      Modules.eulerChar K ((Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj N) = N.eulerChar k := by
    have := Modules.IsInvertible.sheafOfModules_isInvertible N
    have := SheafOfModules.IsInvertible.isFiniteLocallyFree N
    have : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) N :=
      SheafOfModules.IsFiniteLocallyFree.isFinitePresentation N
    simp only [Modules.eulerChar, Modules.finrankH_pullback_fst]
  have h1 := hχ (𝟙_ X.Modules)
  have h2 := Modules.eulerChar_congr K (Modules.pullbackObjUnitIso (Limits.pullback.fst
    (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))))
  rw [Modules.degree, Modules.degree, hχ M, ← h2]
  exact congrArg _ h1

end FieldExtension

section BaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  (K : Type u) [Field K] [Algebra k K]

/-- **The degree of the dictionary.** Let `X` be a smooth projective curve of genus `g` over
`k` with `H⁰(X, 𝒪_X) = k`, let `K/k` be a field extension and let `ℒ` be a line bundle on the
base change `X_K = X ×_{Spec k} Spec K` with `h^0(X_K, ℒ) = 1` and `H^q(X_K, ℒ) = 0` for
`q > 0`. Then `deg ℒ = χ(ℒ) - χ(𝒪_{X_K}) = 1 - (1 - g) = g`.

Of the hypothesis `H⁰(X, 𝒪_X) = k`, only `h⁰(X, 𝒪_X) = 1` is used, through
`χ(𝒪_{X_K}) = χ(𝒪_X) = h⁰(X, 𝒪_X) - g = 1 - g`. Without it the statement fails: for
`X = ℙ¹_ℂ` over `k = ℝ` and `K = ℂ`, the base change `X_ℂ` is two copies of `ℙ¹_ℂ`, so
`χ(𝒪_{X_ℂ}) = 2` rather than `1 - g = 1`, and the line bundle that is `𝒪(-1)` on one copy and
`𝒪` on the other has `χ(ℒ) = 1`, hence `deg ℒ = 1 - 2 = -1 ≠ g = 0`.

(blueprint: `sk-cor-picard-degree-g`) -/
theorem degree_eq_genus [GlobalSectionsBijective k X]
    (ℒ : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
    [ℒ.IsInvertible] (h0 : Modules.finrankH K ℒ 0 = 1)
    (hq : ∀ q : ℕ, 0 < q → Subsingleton (ℒ.H q)) :
    ℒ.degree K = (arithmeticGenus k X : ℤ) := by
  -- `X_K` is a smooth proper curve over `K` with `H⁰(X_K, 𝒪_{X_K}) = K`
  -- (`AlgebraicGeometry.Scheme.GlobalSectionsBijective.pullback`), so Riemann–Roch applies.
  have : SmoothOfRelativeDimension 1 (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback _ _) ‹_›
  have : IsProper (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) ↘ Spec (.of K)) :=
    IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have hχ : ℒ.eulerChar K = 1 := by
    rw [Modules.eulerChar, finsum_eq_single _ 0 fun q hq0 ↦ ?_]
    · simp [h0]
    · have := hq q (Nat.pos_of_ne_zero hq0)
      simp [Modules.finrankH, Module.finrank_zero_of_subsingleton]
  rw [Modules.degree, hχ, eulerChar_unit_eq, arithmeticGenus_pullback]
  ring

/-- **The degree of a twist.** For an invertible sheaf `ℒ` on `X_K` and an invertible sheaf `ℳ`
on the smooth proper curve `X`, `deg (ℒ ⊗ ℳ_K) = deg ℒ + deg ℳ`, by additivity of the degree on
the smooth proper curve `X_K` and its invariance under base change.

(blueprint: `lem-pc-degree-base-change`) -/
theorem degree_tensorObj_pullback_fst
    (L : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules) [L.IsInvertible]
    (M : X.Modules) [M.IsInvertible] :
    (L ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).degree K =
      L.degree K + M.degree k := by
  have := smoothOfRelativeDimension_baseChange (k := k) (X := X) K 1
  have := isProper_baseChange (k := k) (X := X) K
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  rw [Modules.degree_tensorObj, Modules.degree_pullback_fst]

local notation "𝔭" => Limits.pullback.fst (X ↘ Spec (CommRingCat.of k))
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- **Removing a rational point.** Let `ℒ` be an invertible sheaf on `X_K`, let `s : 𝒪_{X_K} ⟶ ℒ`
be a global section and let `x` be a `k`-rational point of `X` such that `s` does not vanish at
`x_K`. Then twisting by the ideal sheaf `𝒪_X(-x) = ker x` lowers `h⁰` by exactly one:
`h⁰(X_K, ℒ ⊗ 𝒪_X(-x)_K) = h⁰(X_K, ℒ) - 1`.

The pullback of `𝒪_X(-x)` is the ideal sheaf `𝓘` of `x_K`, by flatness of `X_K ⟶ X`, and there
is an exact sequence `0 ⟶ 𝓘 ⊗ ℒ ⟶ ℒ ⟶ i_* i^* ℒ ⟶ 0` for `i : x_K ⟶ X_K`. On global sections,
`H⁰(i_* i^* ℒ) = ℒ(x_K) ≅ K` is one-dimensional and `H⁰(ℒ) ⟶ ℒ(x_K)` is onto, since its image
contains `s(x_K) ≠ 0`; the claim follows from left exactness of `H⁰`.

(blueprint: `lem-pc-twist`, Step 3) -/
theorem finrankH_zero_tensorObj_pullback_toModules_ker_add_one
    (L : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules) [L.IsInvertible]
    (s : 𝟙_ _ ⟶ L) (x : (X ↘ Spec (.of k)).fieldPoints k)
    (hx : ((X ↘ Spec (.of k)).baseChangeFieldPoint K x).1.base default ∉ s.zeroLocus.support) :
    Modules.finrankH K (L ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj x.1.ker.toModules) 0 + 1 =
      Modules.finrankH K L 0 :=
  sorry

/-- **Descending induction on `h⁰`.** Let `ℒ` be an invertible sheaf on `X_K` and `ℳ` an
invertible sheaf on `X` with `h⁰(X_K, ℒ ⊗ ℳ_K) = t + 1` and `h¹(X_K, ℒ ⊗ ℳ_K) = 0`. Then there is
an invertible `ℒ₀ = ℳ(-x₁ - ⋯ - x_t)` on `X` with `h⁰(X_K, ℒ ⊗ ℒ₀_K) = 1` and
`h¹(X_K, ℒ ⊗ ℒ₀_K) = 0`.

At each step a non-zero section `s` of `ℒ ⊗ ℳ_K` does not vanish at some `x_K` with `x` a
`k`-rational point
(`AlgebraicGeometry.Scheme.Hom.exists_baseChangeFieldPoint_notMem_support_zeroLocus`).
Twisting by `𝒪_X(-x)` lowers `h⁰` by one
(`AlgebraicGeometry.Scheme.finrankH_zero_tensorObj_pullback_toModules_ker_add_one`) and lowers
`χ = h⁰ - h¹` by `deg 𝒪_X(-x) = -1`, so `h¹ = 0` is preserved.

(blueprint: `lem-pc-twist`, Step 3) -/
theorem exists_isInvertible_twist_of_finrankH_zero_eq [IsSepClosed k]
    (L : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules) [L.IsInvertible] (t : ℕ) :
    ∀ M : X.Modules, M.IsInvertible →
      Modules.finrankH K (L ⊗ (Modules.pullback 𝔭).obj M) 0 = t + 1 →
      Modules.finrankH K (L ⊗ (Modules.pullback 𝔭).obj M) 1 = 0 →
      ∃ ℒ₀ : X.Modules, ℒ₀.IsInvertible ∧
        Modules.finrankH K (L ⊗ (Modules.pullback 𝔭).obj ℒ₀) 0 = 1 ∧
        Modules.finrankH K (L ⊗ (Modules.pullback 𝔭).obj ℒ₀) 1 = 0 := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have := smoothOfRelativeDimension_baseChange (k := k) (X := X) K 1
  have := isProper_baseChange (k := k) (X := X) K
  have := isReduced_baseChange (k := k) (X := X) K
  induction t with
  | zero => exact fun M hM h0 h1 ↦ ⟨M, hM, h0, h1⟩
  | succ t ih =>
  intro M hM h0 h1
  -- a non-zero global section `s` of `N = ℒ ⊗ M_K` and a rational point `x` at which it does
  -- not vanish
  have : Nontrivial ((L ⊗ (Modules.pullback 𝔭).obj M).H 0) :=
    Module.nontrivial_of_finrank_pos (R := K) (show 0 < Modules.finrankH K _ 0 by omega)
  obtain ⟨s, hs⟩ := Modules.exists_ne_zero_of_nontrivial_H_zero (L ⊗ (Modules.pullback 𝔭).obj M)
  have := Modules.IsInvertible.sheafOfModules_isInvertible (L ⊗ (Modules.pullback 𝔭).obj M)
  have := Modules.IsInvertible.sheafOfModules_isInvertible (𝟙_ (Limits.pullback
    (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
  obtain ⟨y, hy⟩ : ∃ y, y ∉ s.zeroLocus.support := by
    by_contra! H
    refine hs ((Modules.Hom.zeroLocus_eq_bot_iff s).mp ?_)
    rw [← IdealSheafData.support_eq_top_iff]
    exact eq_top_iff.mpr fun y _ ↦ H y
  obtain ⟨x, hx⟩ :=
    (X ↘ Spec (.of k)).exists_baseChangeFieldPoint_notMem_support_zeroLocus K s ⟨y, hy⟩
  have := (Hom.isInvertible_ker_fieldPoints x).isInvertible_toModules
  -- twist by the ideal sheaf `𝒪_X(-x)` of `x`
  obtain ⟨e⟩ := Modules.nonempty_pullback_tensorObj_iso 𝔭 M x.1.ker.toModules
  have h0' := finrankH_zero_tensorObj_pullback_toModules_ker_add_one K _ s x hx
  rw [← Modules.finrankH_congr K (whiskerLeftIso L e ≪≫ (α_ _ _ _).symm)] at h0'
  have hχ := Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (k := K)
    (L ⊗ (Modules.pullback 𝔭).obj (M ⊗ x.1.ker.toModules))
  have hχN := Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (k := K)
    (L ⊗ (Modules.pullback 𝔭).obj M)
  have hd := degree_tensorObj_pullback_fst K L (M ⊗ x.1.ker.toModules)
  have hdN := degree_tensorObj_pullback_fst K L M
  rw [Modules.degree_tensorObj (k := k) M, degree_toModules_ker_fieldPoints] at hd
  simp only [Modules.degree] at hd hdN
  refine ih (M ⊗ x.1.ker.toModules) inferInstance (by omega) ?_
  omega

/-- **The twist lemma.** Let `k` be separably closed, let `X` be a smooth projective connected
curve over `k`, let `K/k` be a field extension and let `ℒ` be a line bundle on the base change
`X_K = X ×_{Spec k} Spec K`. Then there is a line bundle `ℒ₀` on `X` whose restriction to `X_K`
twists `ℒ` into the situation of `AlgebraicGeometry.Scheme.degree_eq_genus`:
`h^0(X_K, ℒ ⊗ ℒ₀|_{X_K}) = 1` and `h^1(X_K, ℒ ⊗ ℒ₀|_{X_K}) = 0`.

The proof has three steps. Step 1: a `k`-rational point `x` gives the line bundle `𝒪_X(x)` of
degree one. Step 2: by Riemann–Roch on the smooth proper curve `X_K`, which has
`H⁰(X_K, 𝒪) = K`, the twist `ℒ ⊗ 𝒪_X(n x)_K` has `h⁰ ≥ 1` and `h¹ = 0` once its degree is at
least `2g`. Step 3: remove `h⁰ - 1` rational points
(`AlgebraicGeometry.Scheme.exists_isInvertible_twist_of_finrankH_zero_eq`).

(blueprint: `sk-thm-picard-twist`, `lem-pc-twist`) -/
theorem exists_isInvertible_twist [IsSepClosed k] [ConnectedSpace X]
    (ℒ : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
    [ℒ.IsInvertible] :
    ∃ ℒ₀ : X.Modules, ℒ₀.IsInvertible ∧
      Modules.finrankH K (ℒ ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj ℒ₀) 0 = 1 ∧
      Modules.finrankH K (ℒ ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj ℒ₀) 1 = 0 := by
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : GlobalSectionsBijective k X := .of_isSepClosed
  have := smoothOfRelativeDimension_baseChange (k := k) (X := X) K 1
  have := isProper_baseChange (k := k) (X := X) K
  -- Step 1: a line bundle `𝒪_X(x)` of degree one, from a rational point `x`
  obtain ⟨x⟩ := (X ↘ Spec (.of k)).nonempty_fieldPoints
  have hx := Hom.isInvertible_ker_fieldPoints x
  have := hx.isInvertible_dual_toModules
  have hdeg : ∀ n : ℕ, ∃ M : X.Modules, M.IsInvertible ∧ M.degree k = n := by
    intro n
    induction n with
    | zero => exact ⟨𝟙_ X.Modules, inferInstance, Modules.degree_unit k⟩
    | succ n ih =>
      obtain ⟨M, hM, hMd⟩ := ih
      refine ⟨x.1.ker.toModulesᵛ ⊗ M, inferInstance, ?_⟩
      rw [Modules.degree_tensorObj, hMd, hx.degree_dual_toModules_eq_one
        ((X ↘ Spec (.of k)).finrankΓ_subschemeι_ker_fieldPoints x)]
      push_cast
      ring
  -- Step 2: twist by `𝒪_X(n x)` for `n ≫ 0` to reach `h⁰ ≥ 1` and `h¹ = 0`, by Riemann–Roch
  set g := arithmeticGenus K (Limits.pullback (X ↘ Spec (.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  obtain ⟨M, hM, hMd⟩ := hdeg (2 * g - ℒ.degree K).toNat
  have hd := degree_tensorObj_pullback_fst K ℒ M
  have hd' : 2 * (g : ℤ) - 1 ≤ (ℒ ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M).degree K := by
    rw [hd, hMd]
    omega
  have h0 := finrankH_zero_eq _ hd'
  have hχ := Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (k := K)
    (ℒ ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M)
  have hχ₀ := eulerChar_unit_eq (k := K) (X := Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  simp only [Modules.degree] at hd hd' h0 hMd
  -- Step 3: remove `h⁰ - 1` rational points
  refine exists_isInvertible_twist_of_finrankH_zero_eq K ℒ
    (Modules.finrankH K (ℒ ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj M) 0 - 1) M hM (by omega) (by omega)

end BaseChange

end AlgebraicGeometry.Scheme
