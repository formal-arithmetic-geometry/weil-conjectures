/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.Dual.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.Degree
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier

/-!
# Riemann–Roch, Serre duality and the twist lemma for curves

Let `X` be a smooth proper curve over a field `k` with `H⁰(X, 𝒪_X) = k`
(`AlgebraicGeometry.Scheme.HasTrivialGlobalSections`). Its genus `g = dim_k H^1(X, 𝒪_X)` is
`AlgebraicGeometry.Scheme.arithmeticGenus`, and the degree `deg ℒ = χ(ℒ) - χ(𝒪_X)` of an
invertible sheaf on it is `AlgebraicGeometry.Scheme.Modules.degree`. We state Riemann–Roch,
Serre duality with the canonical module `Ω¹_{X/k}`, and the two statements about line bundles on
the base change `X_K` of `X` along a field extension `K/k` that the Picard framework needs.

## Implementation notes

The hypothesis `H⁰(X, 𝒪_X) = k` cannot be dropped: `ℙ¹_ℂ` viewed as a curve over `ℝ` is smooth
and proper of genus `0`, but `χ(𝒪) = dim_ℝ ℂ = 2 ≠ 1 - 0`. It holds for geometrically integral
`X` (`AlgebraicGeometry.Scheme.HasTrivialGlobalSections.of_geometricallyIntegral`) and for
smooth proper connected `X` over a separably closed field
(`AlgebraicGeometry.Scheme.HasTrivialGlobalSections.of_isSepClosed`, Stacks 0BUG).

The degree of a line bundle is *defined* cohomologically, as `deg ℒ = χ(ℒ) - χ(𝒪_X)`. Its
identification with the divisor degree is the content of Riemann–Roch for line bundles, and is
stated here in three parts: the χ-degree of `𝒪_X(D)` is the divisor degree
`AlgebraicGeometry.Scheme.effectiveCartierDegree` of `D`
(`AlgebraicGeometry.Scheme.Modules.degree_eq_effectiveCartierDegree`), the χ-degree is additive
(`AlgebraicGeometry.Scheme.Modules.degree_tensorObj`), and every line bundle is
`𝒪_X(D₁) ⊗ 𝒪_X(D₂)⁻¹` (`AlgebraicGeometry.Scheme.Modules.exists_effectiveCartier_tensor_iso`).
Together they say that `deg ℒ = deg D₁ - deg D₂` is the divisor degree of `ℒ`, so that
`χ(ℒ) = deg D + 1 - g` is a genuine statement about divisors. The twist `𝒪_X(D)` is expressed
through `AlgebraicGeometry.Scheme.Modules.IsEffectiveCartierTwist`.

The blueprint states Riemann–Roch for *coherent* `ℱ`, with
`deg ℱ = length(torsion) + deg det(ℱ/torsion)`. The statements below assume `ℱ` finite
locally free, which is a genuine narrowing; it will have to be undone once coherence and the
torsion and determinant of a coherent sheaf exist.

The Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerChar` is a `finsum`, so it is
junk unless the cohomology vanishes in large degrees. On a curve that is
`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_two_le` below, which is what makes every
statement of this file about `χ`, `deg` and the genus meaningful.

Ampleness is `AlgebraicGeometry.IsAmple` of
`WeilConjectures/AlgebraicGeometry/Modules/Ample.lean`, shared with the abelian-variety block.
The dual `ℱᵛ = Hom(ℱ, 𝒪_X)` of a sheaf of modules is the internal hom of
`WeilConjectures/AlgebraicGeometry/Modules/Dual.lean`, and the tensor product is the monoidal
structure on `X.Modules` of `WeilConjectures/AlgebraicGeometry/Modules/Invertible.lean`. The
canonical module is `Ω¹_{X/k} = AlgebraicGeometry.Scheme.Hom.relativeDifferentials` for curves
and `𝒪_X` in dimension `0`. Serre duality is stated as the existence of a family of
isomorphisms natural in `ℱ`: the trace `t_X : H¹(X, Ω¹_{X/k}) → k`, the sum of Tate's residues,
cannot be constructed yet, so the isomorphism is not given explicitly.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_two_le`: Grothendieck vanishing on a
  curve.
- `AlgebraicGeometry.Scheme.eulerChar_free_eq`, `AlgebraicGeometry.Scheme.eulerChar_unit_eq`
  and `AlgebraicGeometry.Scheme.finrankH_zero_eq`: Riemann–Roch for curves.
- `AlgebraicGeometry.Scheme.Modules.degree_eq_effectiveCartierDegree`,
  `AlgebraicGeometry.Scheme.Modules.degree_tensorObj` and
  `AlgebraicGeometry.Scheme.Modules.exists_effectiveCartier_tensor_iso`: the χ-degree is the
  divisor degree.
- `AlgebraicGeometry.Scheme.degree_relativeDifferentials`: `deg Ω¹_{X/k} = 2g - 2`.
- `AlgebraicGeometry.Scheme.isAmple_of_degree_pos`: positive degree implies ample.
- `AlgebraicGeometry.Scheme.isAffine_compl_of_isAmple`: the complement of an effective Cartier
  divisor with ample associated line bundle is affine.
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

open CategoryTheory Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

section GlobalSections

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- A proper geometrically integral `k`-scheme has `H⁰(X, 𝒪_X) = k`. -/
instance HasTrivialGlobalSections.of_geometricallyIntegral [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] : HasTrivialGlobalSections k X :=
  sorry

/-- A smooth proper connected scheme over a separably closed field `k` has `H⁰(X, 𝒪_X) = k`:
`H⁰(X, 𝒪_X)` is a finite separable field extension of `k` (Stacks 0BUG). -/
theorem HasTrivialGlobalSections.of_isSepClosed [IsSepClosed k] [Smooth (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [ConnectedSpace X] : HasTrivialGlobalSections k X :=
  sorry

end GlobalSections

section RiemannRoch

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [HasTrivialGlobalSections k X]

/-- **Grothendieck vanishing on a curve.** On a smooth proper curve with `H⁰(X, 𝒪_X) = k` the
cohomology of a quasi-coherent sheaf of modules vanishes in degrees above the dimension, i.e.
in all degrees `q ≥ 2`.

This is what makes the `finsum` defining `AlgebraicGeometry.Scheme.Modules.eulerChar` a finite
sum, hence makes `χ`, the genus and the degree meaningful on a curve. -/
theorem Modules.subsingleton_H_of_two_le (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (ℱ.H q) :=
  sorry

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
over `k` of genus `g`.

The hypothesis `H⁰(X, 𝒪_X) = k` is what gives `h⁰(𝒪_X) = 1`; without it the statement fails, as
for `ℙ¹_ℂ` over `ℝ`, where `χ(𝒪) = 2`.

(blueprint: `sk-thm-picard-rr`) -/
theorem eulerChar_unit_eq :
    Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf) =
      1 - (arithmeticGenus k X : ℤ) :=
  sorry

/-- **Riemann–Roch for curves, divisor degree.** If `ℒ ≅ 𝒪_X(D)` for an effective Cartier divisor
`z : D ⟶ X`, then `deg ℒ = χ(ℒ) - χ(𝒪_X)` is the degree `dim_k Γ(D, 𝒪_D) = ∑_x n_x [κ(x) : k]`
of `D`. With `AlgebraicGeometry.Scheme.eulerChar_unit_eq` this is `χ(𝒪_X(D)) = deg D + 1 - g`.

The divisor `D` is automatically finite over `k`, being proper of dimension `0`.

(blueprint: `sk-thm-picard-rr`) -/
theorem Modules.degree_eq_effectiveCartierDegree {D : Scheme.{u}} (z : D ⟶ X) (ℒ : X.Modules)
    [ℒ.IsInvertible] (h : ℒ.IsEffectiveCartierTwist z) :
    ℒ.degree k = effectiveCartierDegree k z :=
  sorry

/-- **The degree is additive.** `deg (ℒ ⊗ ℳ) = deg ℒ + deg ℳ` for invertible sheaves on a smooth
proper curve with `H⁰(X, 𝒪_X) = k`.

(blueprint: `sk-thm-picard-rr`) -/
theorem Modules.degree_tensorObj (ℒ ℳ : X.Modules) [ℒ.IsInvertible] [ℳ.IsInvertible] :
    (ℒ ⊗ₘ ℳ).degree k = ℒ.degree k + ℳ.degree k :=
  sorry

/-- **Every line bundle comes from a divisor.** Every invertible sheaf `ℒ` on a smooth proper
curve with `H⁰(X, 𝒪_X) = k` is `𝒪_X(D₁) ⊗ 𝒪_X(D₂)⁻¹` for effective Cartier divisors
`z₁ : D₁ ⟶ X` and `z₂ : D₂ ⟶ X`, i.e. `ℒ ⊗ 𝒪_X(D₂) ≅ 𝒪_X(D₁)`.

With `AlgebraicGeometry.Scheme.Modules.degree_eq_effectiveCartierDegree` and
`AlgebraicGeometry.Scheme.Modules.degree_tensorObj` this gives `deg ℒ = deg D₁ - deg D₂`: the
χ-degree of every line bundle is its divisor degree.

(blueprint: `sk-thm-picard-rr`) -/
theorem Modules.exists_effectiveCartier_tensor_iso (ℒ : X.Modules) [ℒ.IsInvertible] :
    ∃ (D₁ D₂ : Scheme.{u}) (z₁ : D₁ ⟶ X) (z₂ : D₂ ⟶ X) (ℳ₁ ℳ₂ : X.Modules),
      ℳ₁.IsInvertible ∧ ℳ₂.IsInvertible ∧ ℳ₁.IsEffectiveCartierTwist z₁ ∧
        ℳ₂.IsEffectiveCartierTwist z₂ ∧ Nonempty (ℒ ⊗ₘ ℳ₂ ≅ ℳ₁) :=
  sorry

/-- **The degree of the canonical module.** `deg Ω¹_{X/k} = 2g - 2` on a smooth proper curve
with `H⁰(X, 𝒪_X) = k`: Serre duality gives `h⁰(Ω¹) = g` and `h¹(Ω¹) = h⁰(𝒪_X) = 1`.

(blueprint: `sk-thm-picard-rr`) -/
theorem degree_relativeDifferentials :
    (X ↘ Spec (.of k)).relativeDifferentials.degree k = 2 * (arithmeticGenus k X : ℤ) - 2 :=
  sorry

/-- **Riemann–Roch for curves, `h⁰` of a line bundle of large degree.** A line bundle `ℒ` of
degree `d ≥ 2g - 1` on a smooth proper curve with `H⁰(X, 𝒪_X) = k` of genus `g` has
`h^0(ℒ) = d + 1 - g`; equivalently `h^1(ℒ) = 0`.

(blueprint: `sk-thm-picard-rr`) -/
theorem finrankH_zero_eq (ℒ : X.Modules) [ℒ.IsInvertible]
    (hd : 2 * (arithmeticGenus k X : ℤ) - 1 ≤ ℒ.degree k) :
    (Modules.finrankH k ℒ 0 : ℤ) = ℒ.degree k + 1 - arithmeticGenus k X :=
  sorry

/-- **Positive degree implies ample.** An invertible sheaf of positive degree on a smooth
proper curve over `k` with `H⁰(X, 𝒪_X) = k` is ample.

(blueprint: `sk-thm-picard-rr`, part (G)) -/
theorem isAmple_of_degree_pos (ℒ : X.Modules) [ℒ.IsInvertible] (hd : 0 < ℒ.degree k) :
    IsAmple (X ↘ Spec (.of k)) ℒ :=
  sorry

/-- **Affine complement.** If `ℒ` is an ample invertible sheaf on `X` and `z : D ⟶ X` is an
effective Cartier divisor with `ℒ ≅ 𝒪_X(D)`, then `X \ Supp D` is affine.

The hypothesis `ℒ ≅ 𝒪_X(D)` is expressed without the twisting sheaf `𝒪_X(D)`, which does not
exist: it says that the ideal sheaf `𝒪_X(-D)` of `D`, i.e. the kernel of `𝒪_X ⟶ z_* 𝒪_D`,
is the image of a monomorphism from the dual `ℒᵛ`. The open complement of the support of `D` is
presented by an open immersion `j` whose range is the complement of the range of `z`.

(blueprint: `sk-thm-picard-rr`, part (H)) -/
theorem isAffine_compl_of_isAmple {D : Scheme.{u}} (z : D ⟶ X) (hz : IsEffectiveCartierCenter z)
    (ℒ : X.Modules) [ℒ.IsInvertible] (hample : IsAmple (X ↘ Spec (.of k)) ℒ)
    (s : ℒᵛ ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (hs : Mono s)
    (hD : Nonempty (cokernel s ≅
      (Modules.pushforward z).obj (SheafOfModules.unit D.ringCatSheaf)))
    {V : Scheme.{u}} (j : V ⟶ X) (hj : IsOpenImmersion j)
    (hjz : Set.range j.base = (Set.range z.base)ᶜ) :
    IsAffine V :=
  sorry

end RiemannRoch

section Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **Serre duality for curves.** Let `X` be a smooth proper curve over `k` with canonical module
`ω_X = Ω¹_{X/k}`. For every finite locally free `ℱ` (of constant rank) and `q ≤ 1` there is a
`k`-linear isomorphism `H^q(X, ℱ)^∨ ≅ H^{1-q}(X, ℱᵛ ⊗ Ω¹_{X/k})`, natural in `ℱ`: for every
morphism `φ : ℱ ⟶ 𝒢` of finite locally free modules, it carries the transpose of
`H^q(φ) : H^q(X, ℱ) → H^q(X, 𝒢)` to `H^{1-q}(φᵛ ⊗ 𝟙)`.

The isomorphism is the one induced by the trace pairing
`H^q(ℱ) ⊗ H^{1-q}(ℱᵛ ⊗ ω_X) → H¹(ω_X) → k`, whose last map is the trace `t_X = ∑_x res_x`,
the sum over closed points of Tate's `k`-linear residues (Tate, *Residues of differentials on
curves*). At a point `x` with `κ(x)/k` separable, `res_x` is `Tr_{κ(x)/k}` of the classical
residue. Tate's residues are not available, so the isomorphisms are only asserted to exist.

The degree bound `q ≤ 1` is necessary: `1 - q` is truncated subtraction on `ℕ`, so without it
the statement would assert `H^q(X, ℱ)^∨ ≅ H^0(X, ℱᵛ ⊗ ω_X)` for `q > 1`, which is false.
No hypothesis `H⁰(X, 𝒪_X) = k` is needed.

(blueprint: `sk-thm-picard-duality`) -/
theorem serreDuality [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] :
    ∃ e : ∀ (ℱ : X.Modules) (q : ℕ), (∃ r, ℱ.IsFiniteLocallyFreeOfRank r) → q ≤ 1 →
        (Module.Dual k (ℱ.H q) ≃ₗ[k]
          (ℱᵛ ⊗ₘ (X ↘ Spec (.of k)).relativeDifferentials).H (1 - q)),
      ∀ {ℱ 𝒢 : X.Modules} (hℱ : ∃ r, ℱ.IsFiniteLocallyFreeOfRank r)
        (h𝒢 : ∃ r, 𝒢.IsFiniteLocallyFreeOfRank r) (φ : ℱ ⟶ 𝒢) (q : ℕ) (hq : q ≤ 1),
        (e ℱ q hℱ hq).toLinearMap ∘ₗ Module.Dual.transpose (Modules.H.mapLinearMap k φ q) =
          Modules.H.mapLinearMap k
              (Modules.dualMap φ ▷ (X ↘ Spec (.of k)).relativeDifferentials) (1 - q) ∘ₗ
            (e 𝒢 q h𝒢 hq).toLinearMap :=
  sorry

/-- **Serre duality in dimension `0`.** Let `X` be smooth and proper of relative dimension `0`
over `k`, i.e. `X = Spec A` with `A` finite étale over `k`, so that the canonical module is
`ω_X = 𝒪_X`. For every finite locally free `ℱ` (of constant rank) there is a `k`-linear
isomorphism `H^0(X, ℱ)^∨ ≅ H^0(X, ℱᵛ)`, natural in `ℱ`: it carries the transpose of `H^0(φ)` to
`H^0(φᵛ)` for every morphism `φ : ℱ ⟶ 𝒢` of finite locally free modules.

The isomorphism is the one induced by the trace pairing `H^0(ℱ) ⊗ H^0(ℱᵛ) → H^0(𝒪_X) = A → k`,
whose last map is the trace `Tr_{A/k}`. In degrees `q > 0` both sides vanish.

(blueprint: `sk-thm-picard-duality`) -/
theorem serreDuality_zero [SmoothOfRelativeDimension 0 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] :
    ∃ e : ∀ ℱ : X.Modules, (∃ r, ℱ.IsFiniteLocallyFreeOfRank r) →
        (Module.Dual k (ℱ.H 0) ≃ₗ[k] (ℱᵛ).H 0),
      ∀ {ℱ 𝒢 : X.Modules} (hℱ : ∃ r, ℱ.IsFiniteLocallyFreeOfRank r)
        (h𝒢 : ∃ r, 𝒢.IsFiniteLocallyFreeOfRank r) (φ : ℱ ⟶ 𝒢),
        (e ℱ hℱ).toLinearMap ∘ₗ Module.Dual.transpose (Modules.H.mapLinearMap k φ 0) =
          Modules.H.mapLinearMap k (Modules.dualMap φ) 0 ∘ₗ (e 𝒢 h𝒢).toLinearMap :=
  sorry

/-- **The two genera agree.** On a smooth proper curve over `k`, `h⁰(X, Ω¹_{X/k}) = h¹(X, 𝒪_X)`:
this is `AlgebraicGeometry.Scheme.serreDuality` for `ℱ = 𝒪_X` and `q = 1`.

(blueprint: `sk-thm-picard-duality`) -/
theorem finrankH_relativeDifferentials_zero_eq_arithmeticGenus
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))] :
    Modules.finrankH k (X ↘ Spec (.of k)).relativeDifferentials 0 = arithmeticGenus k X :=
  sorry

/-- **The two genera agree.** On a smooth proper curve over `k`, the genus
`dim_k Γ(X, Ω¹_{X/k})` of `sk-def-curve` is the arithmetic genus `dim_k H¹(X, 𝒪_X)`.

(blueprint: `sk-thm-picard-duality`) -/
theorem genus_eq_arithmeticGenus [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] :
    (X ↘ Spec (.of k)).genus = arithmeticGenus k X :=
  sorry

end Duality

section BaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  (K : Type u) [Field K] [Algebra k K]

/-- **The degree of the dictionary.** Let `X` be a smooth projective curve of genus `g` over
`k` with `H⁰(X, 𝒪_X) = k`, let `K/k` be a field extension and let `ℒ` be a line bundle on the
base change `X_K = X ×_{Spec k} Spec K` with `h^0(X_K, ℒ) = 1` and `H^q(X_K, ℒ) = 0` for
`q > 0`. Then `deg ℒ = χ(ℒ) - χ(𝒪_{X_K}) = 1 - (1 - g) = g`.

The hypothesis `H⁰(X, 𝒪_X) = k` holds for geometrically integral `X`, or for connected `X` over
a separably closed `k`. Without it the statement fails: for `X = ℙ¹_ℂ` over `k = ℝ` and
`K = ℂ`, the base change `X_ℂ` is two copies of `ℙ¹_ℂ`.

(blueprint: `sk-cor-picard-degree-g`) -/
theorem degree_eq_genus [HasTrivialGlobalSections k X]
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

Separable closedness of `k` together with connectedness supplies the hypothesis
`H⁰(X, 𝒪_X) = k` of Riemann–Roch, by
`AlgebraicGeometry.Scheme.HasTrivialGlobalSections.of_isSepClosed`.

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
  sorry

end BaseChange

end AlgebraicGeometry.Scheme
