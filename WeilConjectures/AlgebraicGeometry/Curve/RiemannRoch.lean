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
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.Ample
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier

/-!
# Riemann–Roch, Serre duality and the twist lemma for curves

Let `X` be a smooth proper geometrically integral curve over a field `k`. We define its genus
`g = dim_k H^1(X, 𝒪_X)` and the degree `deg ℒ = χ(ℒ) - χ(𝒪_X)` of an invertible sheaf on it,
and state Riemann–Roch, Serre duality, and the two statements about line bundles on the base
change `X_K` of `X` along a field extension `K/k` that the Picard framework needs.

## Implementation notes

There is no divisor-theoretic degree of a line bundle anywhere in Mathlib, and no group of
Cartier or Weil divisors on a scheme. The degree is therefore *defined* cohomologically, as
`deg ℒ = χ(ℒ) - χ(𝒪_X)`; this is the standard alternative definition, it agrees with the
divisor-theoretic one on a smooth proper curve, and it is the only one expressible today. The
price is that the Riemann–Roch identity for a line bundle becomes a tautology, which is why
`riemannRoch` is not stated as a single identity but split into the three assertions that carry
content: the Euler characteristic of the free sheaf of rank `r`, the Euler characteristic of
`𝒪_X`, and the computation of `h^0` of a line bundle of degree at least `2g - 1`.

The blueprint states Riemann–Roch for *coherent* `ℱ`. The statements below assume `ℱ` finite
locally free, which is a genuine narrowing; it will have to be undone once coherence and the
divisor-theoretic degree exist.

The Euler characteristic `AlgebraicGeometry.Scheme.Modules.eulerChar` is a `finsum`, so it is
junk unless the cohomology vanishes in large degrees. On a curve that is
`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_two_le` below, which is what makes every
statement of this file about `χ`, `deg` and the genus meaningful.

Ampleness is `AlgebraicGeometry.IsAmple` of
`WeilConjectures/AlgebraicGeometry/Modules/Ample.lean`, shared with the abelian-variety block.
The dual `ℱᵛ = Hom(ℱ, 𝒪_X)` of a sheaf of modules is the internal hom of
`WeilConjectures/AlgebraicGeometry/Modules/Dual.lean`; only the tensor product is still the
`opaque` placeholder of `WeilConjectures/AlgebraicGeometry/Modules/Invertible.lean`. The canonical module `ω_X = Ω^n_{X/k}`
has no placeholder: Serre duality is stated existentially, as the existence of a dualising
invertible module, which is what is provable before `Ω^n_{X/k}` exists and is strictly stronger
than a statement about a placeholder. Identifying that module with `Ω^n_{X/k}` is separate
work.

## Main definitions

- `AlgebraicGeometry.Scheme.genus`: the genus `dim_k H^1(X, 𝒪_X)` of a curve.
- `AlgebraicGeometry.Scheme.Modules.degree`: the degree `χ(ℒ) - χ(𝒪_X)` of an invertible sheaf.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_two_le`: Grothendieck vanishing on a
  curve.
- `AlgebraicGeometry.Scheme.eulerChar_free_eq`, `AlgebraicGeometry.Scheme.eulerChar_unit_eq`
  and `AlgebraicGeometry.Scheme.finrankH_zero_eq`: Riemann–Roch for curves.
- `AlgebraicGeometry.Scheme.isAmple_of_degree_pos`: positive degree implies ample.
- `AlgebraicGeometry.Scheme.isAffine_compl_of_isAmple`: the complement of an effective Cartier
  divisor with ample associated line bundle is affine.
- `AlgebraicGeometry.Scheme.serreDuality`: existence of a dualising module.
- `AlgebraicGeometry.Scheme.degree_eq_genus`: a line bundle with `h^0 = 1` and no higher
  cohomology has degree `g`.
- `AlgebraicGeometry.Scheme.exists_isInvertible_twist`: the twist lemma.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

section Defs

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The **genus** `g = dim_k H^1(X, 𝒪_X)` of a `k`-scheme `X`.

This is the arithmetic genus, and it is the genus in the usual sense when `X` is a smooth proper
geometrically integral curve over `k`; no hypotheses are imposed on `X` here, so for other `X`
the value carries no meaning. -/
noncomputable def genus : ℕ :=
  Modules.finrankH (X := X) k (SheafOfModules.unit X.ringCatSheaf) 1

end Defs

section Degree

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

-- TODO(unify): sk-def-av-pic
-- This is the same notion as `AlgebraicGeometry.Scheme.Hom.picDegree` of the
-- abelian-variety block, which is an `opaque` placeholder for the divisor-theoretic degree;
-- the two have to be identified once divisors on a scheme exist.
/-- The **degree** `deg ℒ = χ(ℒ) - χ(𝒪_X)` of a sheaf of modules on a `k`-scheme `X`.

On a smooth proper geometrically integral curve this agrees with the degree of the associated
divisor class, and it is the definition used throughout, because there is no divisor-theoretic
degree of a line bundle in Mathlib: neither Cartier nor Weil divisors on a scheme are defined
there.

The formula is the degree in the usual sense only for sheaves of rank one; for a locally free
sheaf of rank `r` the degree is `χ(ℱ) - χ(𝒪_X^r)`. -/
noncomputable def Modules.degree (M : X.Modules) : ℤ :=
  M.eulerChar k - Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf)

end Degree

section RiemannRoch

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **Grothendieck vanishing on a curve.** On a smooth proper geometrically integral curve the
cohomology of a quasi-coherent sheaf of modules vanishes in degrees above the dimension, i.e.
in all degrees `q ≥ 2`.

This is what makes the `finsum` defining `AlgebraicGeometry.Scheme.Modules.eulerChar` a finite
sum, hence makes `χ`, the genus and the degree meaningful on a curve. -/
theorem Modules.subsingleton_H_of_two_le (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (ℱ.H q) :=
  sorry

/-- **Riemann–Roch for curves, free case.** The Euler characteristic of the free sheaf of rank
`r` on a smooth proper geometrically integral curve `X` over `k` of genus `g` is
`χ(𝒪_X^{⊕ r}) = r (1 - g)`.

Together with `AlgebraicGeometry.Scheme.Modules.degree`, which measures the degree of a
rank-`r` sheaf against `𝒪_X^{⊕ r}`, this is the content of the Riemann–Roch identity
`χ(ℱ) = deg ℱ + r (1 - g)`.

(blueprint: `sk-thm-picard-rr`) -/
theorem eulerChar_free_eq (r : ℕ) :
    Modules.eulerChar (X := X) k (SheafOfModules.free (ULift.{u} (Fin r))) =
      r * (1 - (genus k X : ℤ)) :=
  sorry

/-- **Riemann–Roch for curves, structure sheaf.** `χ(𝒪_X) = 1 - g` on a smooth proper
geometrically integral curve `X` over `k` of genus `g`.

(blueprint: `sk-thm-picard-rr`) -/
theorem eulerChar_unit_eq :
    Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf) = 1 - (genus k X : ℤ) :=
  sorry

/-- **Riemann–Roch for curves, `h⁰` of a line bundle of large degree.** A line bundle `ℒ` of
degree `d ≥ 2g - 1` on a smooth proper geometrically integral curve of genus `g` has
`h^0(ℒ) = d + 1 - g`; equivalently `h^1(ℒ) = 0`.

(blueprint: `sk-thm-picard-rr`) -/
theorem finrankH_zero_eq (ℒ : X.Modules) [ℒ.IsInvertible]
    (hd : 2 * (genus k X : ℤ) - 1 ≤ ℒ.degree k) :
    (Modules.finrankH k ℒ 0 : ℤ) = ℒ.degree k + 1 - genus k X :=
  sorry

/-- **Positive degree implies ample.** An invertible sheaf of positive degree on a smooth
proper geometrically integral curve over `k` is ample.

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

/-- **Serre duality.** Let `X` be a smooth proper geometrically integral curve over `k` of pure
relative dimension `n ≤ 1`. Then `X` has a *dualising module*: an invertible `𝒪_X`-module `ω`
such that for every finite locally free `ℱ` of rank `r` and every `q ≤ n` the trace pairing is
perfect, i.e. `H^q(X, ℱ)^∨ ≅ H^{n-q}(X, ℱᵛ ⊗ ω)`.

The degree bound `q ≤ n` is necessary: `n - q` is truncated subtraction on `ℕ`, so without it
the statement would assert `H^q(X, ℱ)^∨ ≅ H^0(X, ℱᵛ ⊗ ω)` for `q > n`, which is false.

Quantifying existentially over `ω` is what makes the statement provable before the sheaf of
relative differentials exists; the identification `ω ≅ Ω^n_{X/k}` is separate work.

(blueprint: `sk-thm-picard-duality`) -/
theorem serreDuality (n : ℕ) (hn : n ≤ 1) [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))] :
    ∃ ω : X.Modules, ω.IsInvertible ∧
      ∀ (ℱ : X.Modules) (r : ℕ), ℱ.IsFiniteLocallyFreeOfRank r → ∀ q ≤ n,
        Nonempty (Module.Dual k (ℱ.H q) ≃ₗ[k] (ℱᵛ ⊗ₘ ω).H (n - q)) :=
  sorry

end Duality

section BaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))] (K : Type u) [Field K] [Algebra k K]

/-- **The degree of the dictionary.** Let `X` be a smooth projective curve of genus `g` over
`k`, let `K/k` be a field extension and let `ℒ` be a line bundle on the base change
`X_K = X ×_{Spec k} Spec K` with `h^0(X_K, ℒ) = 1` and `H^q(X_K, ℒ) = 0` for `q > 0`. Then
`deg ℒ = χ(ℒ) - χ(𝒪_{X_K}) = 1 - (1 - g) = g`.

(blueprint: `sk-cor-picard-degree-g`) -/
theorem degree_eq_genus
    (ℒ : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
    [ℒ.IsInvertible] (h0 : Modules.finrankH K ℒ 0 = 1)
    (hq : ∀ q : ℕ, 0 < q → Subsingleton (ℒ.H q)) :
    ℒ.degree K = (genus k X : ℤ) :=
  sorry

/-- **The twist lemma.** Let `k` be separably closed, let `X` be a smooth projective curve over
`k`, let `K/k` be a field extension and let `ℒ` be a line bundle on the base change
`X_K = X ×_{Spec k} Spec K`. Then there is a line bundle `ℒ₀` on `X` whose restriction to `X_K`
twists `ℒ` into the situation of `AlgebraicGeometry.Scheme.degree_eq_genus`:
`h^0(X_K, ℒ ⊗ ℒ₀|_{X_K}) = 1` and `h^1(X_K, ℒ ⊗ ℒ₀|_{X_K}) = 0`.

(blueprint: `sk-thm-picard-twist`) -/
theorem exists_isInvertible_twist [IsSepClosed k]
    (ℒ : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
    [ℒ.IsInvertible] :
    ∃ ℒ₀ : X.Modules, ℒ₀.IsInvertible ∧
      Modules.finrankH K (ℒ ⊗ₘ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj ℒ₀) 0 = 1 ∧
      Modules.finrankH K (ℒ ⊗ₘ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj ℒ₀) 1 = 0 :=
  sorry

end BaseChange

end AlgebraicGeometry.Scheme
