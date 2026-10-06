/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
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
- `AlgebraicGeometry.Scheme.isAmple_of_degree_pos` and
  `AlgebraicGeometry.Scheme.isAmple_iff_degree_pos`: a line bundle is ample if and only if it
  has positive degree.
- `AlgebraicGeometry.Scheme.isAffine_compl_of_isAmple`: the complement of an effective Cartier
  divisor with ample line bundle is affine.
- `AlgebraicGeometry.Scheme.eulerChar_free_eq`, `AlgebraicGeometry.Scheme.eulerChar_unit_eq`,
  `AlgebraicGeometry.Scheme.Modules.eulerChar_eq_degree_add` and
  `AlgebraicGeometry.Scheme.finrankH_zero_eq`: Riemann–Roch for curves.
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

section Curve

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **`χ = h⁰ - h¹` on a curve.** On a smooth proper curve `X` over `k`, the Euler
characteristic of every `𝒪_X`-module `M` is `χ(M) = h⁰(M) - h¹(M)`, since `H^q(X, M) = 0` for
`q ≥ 2` by Grothendieck vanishing. -/
theorem Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (M : X.Modules) :
    M.eulerChar k = M.finrankH k 0 - M.finrankH k 1 := by
  have := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  rw [Modules.eulerChar_eq_sum_range k M
    (topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) 1)]
  simp [Finset.sum_range_succ]
  ring

/-- **The degree of a line bundle twisted by an effective divisor.** Let `D` be an effective
Cartier divisor on a smooth proper curve `X` over `k`, with invertible ideal sheaf `J = 𝒪_X(-D)`,
and `ℒ` an invertible `𝒪_X`-module. Then `χ(ℒ ⊗ 𝒪_X(D)) = χ(ℒ) + deg D`, where
`deg D = dim_k Γ(D, 𝒪_D)`.

Twisting `0 → 𝒪_X → 𝒪_X(D) → 𝒪_X(D)|_D → 0` by `ℒ` gives
`0 → ℒ → ℒ ⊗ 𝒪_X(D) → ℒ|_D → 0`. The restriction `ℒ|_D` of a line bundle to the finite
scheme `D` is trivial, and `𝒪_D` is a finite sum of skyscraper sheaves, which have no higher
cohomology, so `χ(ℒ|_D) = h⁰(𝒪_D) = deg D`; conclude by additivity of `χ` in short exact
sequences.

(blueprint: `lem-pc-degree-base-change`, part (2)) -/
theorem IdealSheafData.IsInvertible.eulerChar_tensorObj_dual_toModules {J : X.IdealSheafData}
    (hJ : J.IsInvertible) (ℒ : X.Modules) [ℒ.IsInvertible] :
    (ℒ ⊗ J.toModulesᵛ).eulerChar k =
      ℒ.eulerChar k + (J.subschemeι ≫ X ↘ Spec (.of k)).finrankΓ :=
  sorry

/-- **Riemann–Roch for curves, divisor degree.** Let `D` be an effective Cartier divisor on a
smooth proper curve `X` over `k`, with invertible ideal sheaf `J = 𝒪_X(-D)`. Then the χ-degree
`χ(𝒪_X(D)) - χ(𝒪_X)` of its line bundle `𝒪_X(D) = J.toModulesᵛ` is the degree
`dim_k Γ(D, 𝒪_D) = ∑_x n_x [κ(x) : k]` of `D`. With
`AlgebraicGeometry.Scheme.eulerChar_unit_eq` this is `χ(𝒪_X(D)) = deg D + 1 - g`.

(blueprint: `sk-thm-picard-rr`, `lem-pc-degree-base-change`) -/
theorem IdealSheafData.IsInvertible.degree_dual_toModules {J : X.IdealSheafData}
    (hJ : J.IsInvertible) :
    J.toModulesᵛ.degree k = (J.subschemeι ≫ X ↘ Spec (.of k)).finrankΓ := by
  have h := hJ.eulerChar_tensorObj_dual_toModules (k := k) (𝟙_ X.Modules)
  rw [Modules.eulerChar_congr k (λ_ _)] at h
  have hu : Modules.eulerChar k (𝟙_ X.Modules) =
      Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf) := rfl
  rw [Modules.degree, h, hu, add_sub_cancel_left]

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

/-- **Every line bundle comes from a divisor.** Every invertible sheaf `ℒ` on a smooth proper
curve is `𝒪_X(D₁) ⊗ 𝒪_X(D₂)⁻¹` for effective Cartier divisors `D₁` and `D₂`, given by
invertible ideal sheaves `J₁ = 𝒪_X(-D₁)` and `J₂ = 𝒪_X(-D₂)`: `ℒ ⊗ 𝒪_X(D₂) ≅ 𝒪_X(D₁)`.

On a connected component, a nonzero rational section `s` of `ℒ` gives `ℒ ≅ 𝒪_X(div s)`, and
`div s = D₁ - D₂` is the difference of its divisors of zeros and of poles.

With `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules` and
`AlgebraicGeometry.Scheme.Modules.degree_tensorObj` this gives `deg ℒ = deg D₁ - deg D₂`: the
χ-degree of every line bundle is its divisor degree.

(blueprint: `sk-thm-picard-rr`, `lem-sc-line-bundle-rational-section`) -/
theorem Modules.exists_tensorObj_dual_toModules_iso (ℒ : X.Modules) [ℒ.IsInvertible] :
    ∃ J₁ J₂ : X.IdealSheafData, J₁.IsInvertible ∧ J₂.IsInvertible ∧
      Nonempty (ℒ ⊗ₘ J₂.toModulesᵛ ≅ J₁.toModulesᵛ) :=
  sorry

/-- **The degree is additive.** `deg (ℒ ⊗ ℳ) = deg ℒ + deg ℳ` for invertible sheaves on a smooth
proper curve.

Write `ℳ ⊗ 𝒪_X(D₂) ≅ 𝒪_X(D₁)`
(`AlgebraicGeometry.Scheme.Modules.exists_tensorObj_dual_toModules_iso`); twisting by the
effective divisors `D₁` and `D₂`
(`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.eulerChar_tensorObj_dual_toModules`)
adds their degrees to `χ`.

(blueprint: `sk-thm-picard-rr`, `lem-pc-degree-base-change`) -/
theorem Modules.degree_tensorObj (ℒ ℳ : X.Modules) [ℒ.IsInvertible] [ℳ.IsInvertible] :
    (ℒ ⊗ₘ ℳ).degree k = ℒ.degree k + ℳ.degree k := by
  obtain ⟨J₁, J₂, h₁, h₂, ⟨e⟩⟩ := Modules.exists_tensorObj_dual_toModules_iso ℳ
  have := h₁.isInvertible_dual_toModules
  have := h₂.isInvertible_dual_toModules
  have a := h₂.eulerChar_tensorObj_dual_toModules (k := k) (ℒ ⊗ ℳ)
  have b := h₁.eulerChar_tensorObj_dual_toModules (k := k) ℒ
  have c := h₂.eulerChar_tensorObj_dual_toModules (k := k) ℳ
  have d := h₁.degree_dual_toModules (k := k)
  rw [Modules.eulerChar_congr k (α_ _ _ _ ≪≫ whiskerLeftIso ℒ e)] at a
  rw [Modules.eulerChar_congr k e] at c
  simp only [Modules.degree] at d ⊢
  linarith

/-- The degree of the dual: `deg ℒᵛ = -deg ℒ`, since `ℒ ⊗ ℒᵛ ≅ 𝒪_X`. -/
theorem Modules.degree_dual (ℒ : X.Modules) [ℒ.IsInvertible] : ℒᵛ.degree k = -ℒ.degree k := by
  obtain ⟨e⟩ := Modules.nonempty_tensorObj_dual_iso_unit ℒ
  have h := Modules.degree_tensorObj (k := k) ℒ ℒᵛ
  rw [Modules.degree_congr k e] at h
  have hu : Modules.degree k (𝟙_ X.Modules) = 0 := Modules.degree_unit (X := X) k
  linarith

/-- The degree of a tensor power: `deg ℒ^{⊗ n} = n deg ℒ`. -/
theorem Modules.degree_tensorPow (ℒ : X.Modules) [ℒ.IsInvertible] (n : ℕ) :
    (ℒ.tensorPow n).degree k = n * ℒ.degree k := by
  induction n with
  | zero => exact (Modules.degree_unit (X := X) k).trans (by simp)
  | succ n ih =>
    rw [Modules.tensorPow_succ, Modules.degree_tensorObj, ih]
    push_cast
    ring

end Curve

section RiemannRoch

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GlobalSectionsBijective k X]

/-- **Riemann–Roch for curves, structure sheaf.** `χ(𝒪_X) = 1 - g` on a smooth proper curve `X`
over `k` with `H⁰(X, 𝒪_X) = k`, of genus `g`: `χ(𝒪_X) = h⁰(𝒪_X) - h¹(𝒪_X)` with
`h⁰(𝒪_X) = 1`.

Without the hypothesis `H⁰(X, 𝒪_X) = k` the statement fails, as for `ℙ¹_ℂ` over `ℝ`, where
`χ(𝒪) = 2`.

(blueprint: `sk-thm-picard-rr`, `lem-sc-riemann-roch`) -/
theorem eulerChar_unit_eq :
    Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf) =
      1 - (arithmeticGenus k X : ℤ) := by
  refine (Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one
    (SheafOfModules.unit X.ringCatSheaf)).trans ?_
  rw [Modules.finrankH_unit_zero]
  rfl

/-- **Riemann–Roch for curves, free case.** The Euler characteristic of the free sheaf of rank
`r` on a smooth proper curve `X` over `k` with `H⁰(X, 𝒪_X) = k`, of genus `g`, is
`χ(𝒪_X^{⊕ r}) = r (1 - g)`: cohomology commutes with finite direct sums
(`AlgebraicGeometry.Scheme.Modules.finrankH_of_isBilimit`).

Together with `AlgebraicGeometry.Scheme.Modules.degree`, which measures the degree of a
rank-`r` sheaf against `𝒪_X^{⊕ r}`, this is the content of the Riemann–Roch identity
`χ(ℱ) = deg ℱ + r (1 - g)`.

(blueprint: `sk-thm-picard-rr`, `lem-sc-riemann-roch`) -/
theorem eulerChar_free_eq (r : ℕ) :
    Modules.eulerChar (X := X) k (SheafOfModules.free (ULift.{u} (Fin r))) =
      r * (1 - (arithmeticGenus k X : ℤ)) := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hb := biconeIsBilimitOfColimitCoconeOfIsColimit
    (colimit.isColimit (Discrete.functor fun _ : ULift.{u} (Fin r) ↦ O))
  have (q : ℕ) : FiniteDimensional k (O.H q) :=
    Modules.finiteDimensional_H (M := 𝟙_ X.Modules) k q
  have h (q : ℕ) : Modules.finrankH (X := X) k (SheafOfModules.free (ULift.{u} (Fin r))) q =
      r * O.finrankH k q :=
    (Modules.finrankH_of_isBilimit k hb q).trans (by simp)
  refine (Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one _).trans ?_
  have hO := (Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one (k := k) O).symm.trans
    (eulerChar_unit_eq (k := k))
  simp only [h, Nat.cast_mul, ← hO]
  ring

/-- **Riemann–Roch for line bundles.** `χ(ℒ) = deg ℒ + 1 - g` for every invertible `ℒ` on a
smooth proper curve with `H⁰(X, 𝒪_X) = k`, of genus `g`, where by
`AlgebraicGeometry.Scheme.Modules.degree_tensorObj` and
`AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules` the degree is the
divisor degree.

(blueprint: `lem-sc-riemann-roch`, part (1)) -/
theorem Modules.eulerChar_eq_degree_add (ℒ : X.Modules) :
    ℒ.eulerChar k = ℒ.degree k + 1 - arithmeticGenus k X := by
  rw [Modules.degree, eulerChar_unit_eq]
  ring

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

section LargeDegree

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **The degree of the canonical module.** `deg Ω¹_{X/k} = 2g - 2` on a smooth proper curve
with `H⁰(X, 𝒪_X) = k`, of genus `g`: Serre duality gives `h⁰(Ω¹) = g`
(`AlgebraicGeometry.Scheme.finrankH_relativeDifferentials_zero_eq_arithmeticGenus`) and
`h¹(Ω¹) = h⁰(𝒪_X) = 1`, so `χ(Ω¹) - χ(𝒪_X) = (g - 1) - (1 - g)`.

(blueprint: `sk-thm-picard-rr`, `lem-sc-canonical-degree`) -/
theorem degree_relativeDifferentials [GlobalSectionsBijective k X] :
    (X ↘ Spec (.of k)).relativeDifferentials.degree k = 2 * (arithmeticGenus k X : ℤ) - 2 := by
  -- Serre duality for `ℱ = 𝒪_X` and `q = 0`, with `𝒪_Xᵛ ⊗ Ω¹ ≅ Ω¹`.
  obtain ⟨e⟩ := serreDuality (k := k) (X := X) 1 0 rfl
  obtain ⟨d⟩ := Modules.nonempty_dual_unit_iso (X := X)
  let 𝒪 : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory :=
    ⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩
  have h : Module.finrank k (Module.Dual k (Modules.H (X := X) (show X.Modules from 𝒪.obj) 0)) =
      Modules.finrankH k (𝒪.objᵛ ⊗ (X ↘ Spec (.of k)).relativeDifferentials) 1 :=
    (e.app (op 𝒪)).toLinearEquiv.finrank_eq
  rw [Subspace.dual_finrank_eq] at h
  have h1 : Modules.finrankH k (X ↘ Spec (.of k)).relativeDifferentials 1 = 1 := by
    rw [← Modules.finrankH_congr k (whiskerRightIso d _ ≪≫ λ_ _) 1, ← h]
    exact Modules.finrankH_unit_zero
  rw [Modules.degree, Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one,
    finrankH_relativeDifferentials_zero_eq_arithmeticGenus, h1, eulerChar_unit_eq]
  push_cast
  ring

/-- **A line bundle of negative degree has no sections.** On a smooth proper curve with
`H⁰(X, 𝒪_X) = k`, an invertible `ℳ` with `deg ℳ < 0` has `H⁰(X, ℳ) = 0`: a nonzero section `s`
would give `ℳ ≅ 𝒪_X(div s)` with `div s` effective, of degree `≥ 0`.

The hypothesis `H⁰(X, 𝒪_X) = k`, which makes `X` connected, cannot be dropped: on
`X = ℙ¹ ⊔ ℙ¹` the line bundle `𝒪(1) ⊔ 𝒪(-3)` has degree `-2` and nonzero sections.

(blueprint: `lem-sc-negative-degree-no-sections`) -/
theorem Modules.finrankH_zero_eq_zero_of_degree_neg [GlobalSectionsBijective k X]
    (ℳ : X.Modules) [ℳ.IsInvertible] (hd : ℳ.degree k < 0) : ℳ.finrankH k 0 = 0 :=
  sorry

/-- **`h¹` of a line bundle of large degree vanishes.** A line bundle `ℒ` of degree
`d ≥ 2g - 1` on a smooth proper curve with `H⁰(X, 𝒪_X) = k` of genus `g` has `H¹(X, ℒ) = 0`:
by Serre duality `H¹(ℒ)^∨ ≅ H⁰(ℒᵛ ⊗ Ω¹)`, and `ℒᵛ ⊗ Ω¹` has degree `2g - 2 - d < 0`. -/
theorem Modules.finrankH_one_eq_zero_of_degree [GlobalSectionsBijective k X] (ℒ : X.Modules)
    [ℒ.IsInvertible] (hd : 2 * (arithmeticGenus k X : ℤ) - 1 ≤ ℒ.degree k) :
    ℒ.finrankH k 1 = 0 := by
  have := (X ↘ Spec (.of k)).isInvertible_relativeDifferentials
  have := Modules.IsInvertible.of_sheafOfModules (X ↘ Spec (.of k)).relativeDifferentials
  have := Modules.IsInvertible.sheafOfModules_isInvertible ℒ
  obtain ⟨e⟩ := serreDuality (k := k) (X := X) 0 1 rfl
  let ℱ : (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).FullSubcategory :=
    ⟨ℒ, SheafOfModules.IsInvertible.isFiniteLocallyFree ℒ⟩
  have h : Module.finrank k (Module.Dual k (Modules.H (X := X) (show X.Modules from ℱ.obj) 1)) =
      Modules.finrankH k (ℱ.objᵛ ⊗ (X ↘ Spec (.of k)).relativeDifferentials) 0 :=
    (e.app (op ℱ)).toLinearEquiv.finrank_eq
  rw [Subspace.dual_finrank_eq] at h
  refine h.trans (Modules.finrankH_zero_eq_zero_of_degree_neg _ ?_)
  change (ℒᵛ ⊗ₘ (X ↘ Spec (.of k)).relativeDifferentials).degree k < 0
  rw [Modules.degree_tensorObj, Modules.degree_dual, degree_relativeDifferentials]
  linarith

/-- **Riemann–Roch for curves, `h⁰` of a line bundle of large degree.** A line bundle `ℒ` of
degree `d ≥ 2g - 1` on a smooth proper curve with `H⁰(X, 𝒪_X) = k` of genus `g` has
`h^0(ℒ) = d + 1 - g`; equivalently `h^1(ℒ) = 0`
(`AlgebraicGeometry.Scheme.Modules.finrankH_one_eq_zero_of_degree`).

(blueprint: `sk-thm-picard-rr`, `lem-sc-riemann-roch-large-degree`) -/
theorem finrankH_zero_eq [GlobalSectionsBijective k X] (ℒ : X.Modules) [ℒ.IsInvertible]
    (hd : 2 * (arithmeticGenus k X : ℤ) - 1 ≤ ℒ.degree k) :
    (Modules.finrankH k ℒ 0 : ℤ) = ℒ.degree k + 1 - arithmeticGenus k X := by
  rw [Modules.degree, eulerChar_unit_eq, Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one,
    Modules.finrankH_one_eq_zero_of_degree ℒ hd]
  ring

/-- **A line bundle of degree `≥ 2g + 1` is very ample.** Let `k` be algebraically closed and
`ℳ` a line bundle of degree `d ≥ 2g + 1` on a smooth proper curve with `H⁰(X, 𝒪_X) = k` of
genus `g`. For closed points `P, Q`, Riemann–Roch in degree `≥ 2g - 1`
(`AlgebraicGeometry.Scheme.finrankH_zero_eq`) gives `h⁰(ℳ(-P)) = h⁰(ℳ) - 1` and
`h⁰(ℳ(-P-Q)) = h⁰(ℳ) - 2`: the complete linear system `|ℳ|` is base point free and separates
points and tangent vectors, so it defines a closed immersion into projective space.

(blueprint: `lem-sc-degree-2g1-very-ample`) -/
theorem isVeryAmple_of_degree [IsAlgClosed k] [GlobalSectionsBijective k X] (ℳ : X.Modules)
    [ℳ.IsInvertible] (hd : 2 * (arithmeticGenus k X : ℤ) + 1 ≤ ℳ.degree k) :
    IsVeryAmple (X ↘ Spec (.of k)) ℳ :=
  sorry

/-- **Positive degree implies ample, over an algebraically closed field.** If `deg ℒ > 0` then
`deg ℒ^{⊗ m} = m deg ℒ ≥ 2g + 1` for `m = 2g + 1`, so `ℒ^{⊗ m}` is very ample
(`AlgebraicGeometry.Scheme.isVeryAmple_of_degree`).

(blueprint: `lem-sc-positive-degree-ample`) -/
theorem isAmple_of_degree_pos_of_isAlgClosed [IsAlgClosed k] [GlobalSectionsBijective k X]
    (ℒ : X.Modules) [ℒ.IsInvertible] (hd : 0 < ℒ.degree k) :
    IsAmple (X ↘ Spec (.of k)) ℒ := by
  refine ⟨2 * arithmeticGenus k X + 1, Nat.succ_pos _, isVeryAmple_of_degree _ ?_⟩
  rw [Modules.degree_tensorPow]
  push_cast
  nlinarith

/-- **Positive degree implies ample.** An invertible sheaf of positive degree on a smooth
proper curve over `k` with `H⁰(X, 𝒪_X) = k` is ample: after base change to an algebraic closure
`k̄`, where the degree is unchanged (`AlgebraicGeometry.Scheme.Modules.degree_pullback`), some
power `ℒ_{k̄}^{⊗ m}` is very ample
(`AlgebraicGeometry.Scheme.isAmple_of_degree_pos_of_isAlgClosed`), and very ampleness
descends (`AlgebraicGeometry.IsVeryAmple.of_pullback`).

(blueprint: `sk-thm-picard-rr`, part (G)) -/
theorem isAmple_of_degree_pos [GlobalSectionsBijective k X] (ℒ : X.Modules) [ℒ.IsInvertible]
    (hd : 0 < ℒ.degree k) :
    IsAmple (X ↘ Spec (.of k)) ℒ := by
  let K := AlgebraicClosure k
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : SmoothOfRelativeDimension 1 (Limits.pullback (X ↘ Spec (.of k)) g ↘ Spec (.of K)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback _ _) ‹_›
  have : IsProper (Limits.pullback (X ↘ Spec (.of k)) g ↘ Spec (.of K)) :=
    IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  obtain ⟨m, hm, hv⟩ := isAmple_of_degree_pos_of_isAlgClosed
    ((Modules.pullback (pullback.fst (X ↘ Spec (.of k)) g)).obj ℒ)
    ((Modules.degree_pullback k K ℒ).symm ▸ hd)
  exact ⟨m, hm, IsVeryAmple.of_pullback _ K _
    (hv.of_iso (Modules.nonempty_pullback_tensorPow_iso _ ℒ m).some.symm)⟩

/-- **Ample if and only if positive degree.** An invertible sheaf on a smooth proper curve over
`k` with `H⁰(X, 𝒪_X) = k` is ample if and only if it has positive degree. Ampleness and degree
are both invariant under base change to an algebraic closure, where an ample line bundle has
positive degree (`AlgebraicGeometry.Scheme.Hom.degree_pos_of_isAmple`).

(blueprint: `lem-pc-ample-positive-degree`) -/
theorem isAmple_iff_degree_pos [GlobalSectionsBijective k X] (ℒ : X.Modules) [ℒ.IsInvertible] :
    IsAmple (X ↘ Spec (.of k)) ℒ ↔ 0 < ℒ.degree k := by
  refine ⟨fun h ↦ ?_, isAmple_of_degree_pos ℒ⟩
  let K := AlgebraicClosure k
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let XK := Limits.pullback (X ↘ Spec (.of k)) g
  have : SmoothOfRelativeDimension 1 (XK ↘ Spec (.of K)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback _ _) ‹_›
  have : IsProper (XK ↘ Spec (.of K)) :=
    IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) ‹_›
  have := GlobalSectionsBijective.nonempty (k := K) (X := XK)
  have hdim := topologicalKrullDim_eq_of_smoothOfRelativeDimension (XK ↘ Spec (.of K)) 1
  rw [← Modules.degree_pullback k K ℒ]
  have := Scheme.Hom.degree_pos_of_isAmple (XK ↘ Spec (.of K)) (by exact_mod_cast hdim)
    ((Modules.pullback (pullback.fst (X ↘ Spec (.of k)) g)).obj ℒ) (h.pullback_of_field K)
  rwa [Scheme.Hom.degree_eq_degree_of_topologicalKrullDim_eq_one _ (by exact_mod_cast hdim)]
    at this

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] in
/-- **Affine complement.** Let `D` be an effective Cartier divisor on a smooth proper curve `X`,
with invertible ideal sheaf `J = 𝒪_X(-D)`, whose line bundle `𝒪_X(D) = J.toModulesᵛ` is ample.
Then `X \ Supp D` is affine. The open complement of the support of `D` is presented by an open
immersion `j` whose range is the complement of the support of `J`. This is the case of curves of
`AlgebraicGeometry.isAffine_compl_of_isAmple_dual_toModules`.

(blueprint: `sk-thm-picard-rr`, part (H)) -/
theorem isAffine_compl_of_isAmple {J : X.IdealSheafData} (hJ : J.IsInvertible)
    (hample : IsAmple (X ↘ Spec (.of k)) J.toModulesᵛ) {V : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] (hj : Set.range j.base = (J.support : Set X)ᶜ) :
    IsAffine V :=
  isAffine_compl_of_isAmple_dual_toModules _ hJ hample j hj

end LargeDegree

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

/-- **The twist lemma.** Let `k` be separably closed, let `X` be a smooth projective connected
curve over `k`, let `K/k` be a field extension and let `ℒ` be a line bundle on the base change
`X_K = X ×_{Spec k} Spec K`. Then there is a line bundle `ℒ₀` on `X` whose restriction to `X_K`
twists `ℒ` into the situation of `AlgebraicGeometry.Scheme.degree_eq_genus`:
`h^0(X_K, ℒ ⊗ ℒ₀|_{X_K}) = 1` and `h^1(X_K, ℒ ⊗ ℒ₀|_{X_K}) = 0`.

(blueprint: `sk-thm-picard-twist`) -/
theorem exists_isInvertible_twist [IsSepClosed k] [ConnectedSpace X]
    (ℒ : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
    [ℒ.IsInvertible] :
    ∃ ℒ₀ : X.Modules, ℒ₀.IsInvertible ∧
      Modules.finrankH K (ℒ ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj ℒ₀) 0 = 1 ∧
      Modules.finrankH K (ℒ ⊗ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj ℒ₀) 1 = 0 :=
  -- `H⁰(X, 𝒪_X) = k` by `AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_isSepClosed`.
  sorry

end BaseChange

end AlgebraicGeometry.Scheme
