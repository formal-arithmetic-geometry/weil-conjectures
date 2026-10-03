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
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

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

(blueprint: `sk-thm-picard-duality`) -/
theorem serreDuality [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] (p q : ℕ) (hpq : p + q = 1) :
    Nonempty ((SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙
        (Modules.cohomologyFunctor k q).op ⋙ ModuleCat.dualFunctor k ≅
      (SheafOfModules.isFiniteLocallyFree X.ringCatSheaf).ι.op ⋙ Modules.dualFunctor X ⋙
        tensorRight (X ↘ Spec (.of k)).relativeDifferentials ⋙ Modules.cohomologyFunctor k p) :=
  sorry

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
`dim_k Γ(X, Ω¹_{X/k})` of `sk-def-curve` is the arithmetic genus `dim_k H¹(X, 𝒪_X)`.

(blueprint: `sk-thm-picard-duality`) -/
theorem genus_eq_arithmeticGenus [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] :
    (X ↘ Spec (.of k)).genus = arithmeticGenus k X := by
  rw [Hom.genus_eq_finrankH_zero, finrankH_relativeDifferentials_zero_eq_arithmeticGenus]

end Duality

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
    ℒ.degree K = (arithmeticGenus k X : ℤ) :=
  sorry

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
