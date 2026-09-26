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
public import WeilConjectures.AlgebraicGeometry.Modules.Operations
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier

@[expose] public section

/-!
# Riemann–Roch, Serre duality and the twist lemma for curves

Let `X` be a smooth proper geometrically integral curve over a field `k`. We define its genus
`g = dim_k H^1(X, 𝒪_X)` and the degree `deg ℒ = χ(ℒ) - χ(𝒪_X)` of an invertible sheaf on it,
and state Riemann–Roch, Serre duality, and the two statements about line bundles on the base
change `X_K` of `X` along a field extension `K/k` that the Picard framework needs.

## Design notes

There is no divisor-theoretic degree of a line bundle anywhere in Mathlib, and no group of
Cartier or Weil divisors on a scheme. The degree is therefore *defined* cohomologically, as
`deg ℒ = χ(ℒ) - χ(𝒪_X)`; this is the standard alternative definition, it agrees with the
divisor-theoretic one on a smooth proper curve, and it is the only one expressible today. The
price is that the Riemann–Roch identity for a line bundle becomes a tautology; the content of
`riemannRoch` sits in the other two assertions, namely `χ(𝒪_X) = 1 - g` and the computation of
`h^0` of a line bundle of degree at least `2g - 1`, and in the rank-`r` assertion, where the
degree is measured against the free sheaf of rank `r` rather than against `𝒪_X`.

Since "locally free of rank `r`" is not packaged anywhere either, it is defined here as
`AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank`, in the style of
`SheafOfModules.IsInvertible`: local generators data all of whose generating families are
indexed by a type with `r` elements. The rank-one case is `SheafOfModules.IsInvertible`.

The tensor product, the dual and ampleness of a sheaf of modules are the `sorry`ed placeholders
of `WeilConjectures/AlgebraicGeometry/Modules/Operations.lean`, shared with the other files of
the Picard block. The canonical module `ω_X = Ω^n_{X/k}` has no placeholder anywhere — Mathlib
has neither the sheaf of differentials of a morphism of schemes nor exterior powers of sheaves
of modules — so one more tagged stub, `canonicalModule`, is added here. Serre duality is then
stated cleanly with it, rather than by quantifying over an unconstrained invertible `ω`, which
would make the statement plainly false.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank`: locally free of a given rank.
- `AlgebraicGeometry.Scheme.genus`: the genus `dim_k H^1(X, 𝒪_X)` of a curve.
- `AlgebraicGeometry.Scheme.Modules.degree`: the degree `χ(ℒ) - χ(𝒪_X)` of an invertible sheaf.
- `AlgebraicGeometry.Scheme.canonicalModule`: placeholder for `ω_X = Ω^n_{X/k}`.

## Main statements

- `AlgebraicGeometry.Scheme.riemannRoch`: Riemann–Roch for curves.
- `AlgebraicGeometry.Scheme.isAmple_of_degree_pos`: positive degree implies ample.
- `AlgebraicGeometry.Scheme.isAffine_compl_of_isAmple`: the complement of an effective Cartier
  divisor with ample associated line bundle is affine.
- `AlgebraicGeometry.Scheme.serreDuality`: the trace pairing is perfect.
- `AlgebraicGeometry.Scheme.degree_eq_genus`: a line bundle with `h^0 = 1` and no higher
  cohomology has degree `g`.
- `AlgebraicGeometry.Scheme.exists_isInvertible_twist`: the twist lemma.
-/

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

section Rank

variable {X : Scheme.{u}}

/-- A sheaf of modules on a scheme is **locally free of rank `r`** if there are local generators
data for it which are locally free data and whose families of generators are each indexed by a
type with `r` elements.

For `r = 1` this is `SheafOfModules.IsInvertible`; Mathlib packages neither the rank of a sheaf
of modules nor this predicate. -/
def Modules.IsLocallyFreeOfRank (M : X.Modules) (r : ℕ) : Prop :=
  ∃ q : SheafOfModules.LocalGeneratorsData.{u} M, q.IsLocallyFreeData ∧
    ∀ i, Nonempty ((q.generators i).I ≃ Fin r)

end Rank

section Defs

variable (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The **genus** `g = dim_k H^1(X, 𝒪_X)` of a `k`-scheme `X`.

This is the arithmetic genus, and it is the genus in the usual sense when `X` is a smooth proper
geometrically integral curve over `k`; no hypotheses are imposed on `X` here, so for other `X`
the value carries no meaning. -/
noncomputable def genus : ℕ := Modules.h (X := X) k (SheafOfModules.unit X.ringCatSheaf) 1

-- TODO(unify): sk-thm-picard-duality
/-- The **canonical module** `ω_X = Ω^n_{X/S}` of a morphism `f : X ⟶ S` of pure relative
dimension `n`, i.e. the `n`-th exterior power of the sheaf of relative differentials of `f`.

Placeholder: Mathlib has neither the sheaf of differentials of a morphism of schemes nor
exterior powers of sheaves of modules. -/
noncomputable def canonicalModule {Y S : Scheme.{u}} (_f : Y ⟶ S) (_n : ℕ) : Y.Modules := sorry

end Defs

section Degree

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The **degree** `deg ℒ = χ(ℒ) - χ(𝒪_X)` of a sheaf of modules on a `k`-scheme `X`.

On a smooth proper geometrically integral curve this agrees with the degree of the associated
divisor class, and it is the definition used throughout, because there is no divisor-theoretic
degree of a line bundle in Mathlib: neither Cartier nor Weil divisors on a scheme are defined
there. With this convention the Riemann–Roch identity `χ(ℒ) = deg ℒ + 1 - g` of
`AlgebraicGeometry.Scheme.riemannRoch` is a tautology for a line bundle, and the content of that
theorem is the identification `χ(𝒪_X) = 1 - g` together with the rank-`r` and `h^0` assertions.

The formula is the degree in the usual sense only for sheaves of rank one; for a locally free
sheaf of rank `r` the degree is `χ(ℱ) - χ(𝒪_X^r)`, which is what `riemannRoch` uses. -/
noncomputable def Modules.degree (M : X.Modules) : ℤ :=
  M.eulerChar k - Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf)

end Degree

section RiemannRoch

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- Blueprint `sk-thm-picard-rr`: Riemann–Roch for curves, and its geometric corollary.

Part (RR) for a smooth proper geometrically integral curve `X` over `k` of genus `g`: for a
locally free sheaf `ℱ` of rank `r`, the Euler characteristic
`χ(ℱ) = ∑_q (-1)^q dim_k H^q(X, ℱ)` satisfies `χ(ℱ) = deg ℱ + r (1 - g)`, where the degree of a
rank-`r` sheaf is measured against the free sheaf of rank `r`, `deg ℱ = χ(ℱ) - χ(𝒪_X^r)`; in
particular `χ(𝒪_X) = 1 - g`, and a line bundle `ℒ` of degree `d ≥ 2g - 1` has
`h^0(ℒ) = d + 1 - g`.

For a line bundle the first assertion is `χ(ℒ) = deg ℒ + 1 - g` with
`AlgebraicGeometry.Scheme.Modules.degree`, which that definition makes a tautology; see the
module docstring. -/
theorem riemannRoch (ℱ : X.Modules) (r : ℕ) (hℱ : ℱ.IsLocallyFreeOfRank r) :
    ℱ.eulerChar k =
        (ℱ.eulerChar k -
          Modules.eulerChar (X := X) k (SheafOfModules.free (ULift.{u} (Fin r)))) +
          r * (1 - (genus k X : ℤ)) ∧
      Modules.eulerChar (X := X) k (SheafOfModules.unit X.ringCatSheaf) = 1 - (genus k X : ℤ) ∧
      ∀ ℒ : X.Modules, ℒ.IsInvertible → 2 * (genus k X : ℤ) - 1 ≤ ℒ.degree k →
        (Modules.h k ℒ 0 : ℤ) = ℒ.degree k + 1 - genus k X :=
  sorry

/-- Blueprint `sk-thm-picard-rr`: Riemann–Roch for curves, and its geometric corollary.

Part (G), *positive degree implies ample*: an invertible sheaf of positive degree on a smooth
proper geometrically integral curve over `k` is ample. -/
theorem isAmple_of_degree_pos (ℒ : X.Modules) (hℒ : ℒ.IsInvertible) (hd : 0 < ℒ.degree k) :
    ℒ.IsAmple :=
  sorry

/-- Blueprint `sk-thm-picard-rr`: Riemann–Roch for curves, and its geometric corollary.

Part (H), *affine complement*: if `ℒ` is an ample invertible sheaf on `X` and `z : D ⟶ X` is an
effective Cartier divisor with `ℒ ≅ 𝒪_X(D)`, then `X \ Supp D` is affine.

The hypothesis `ℒ ≅ 𝒪_X(D)` is expressed without the twisting sheaf `𝒪_X(D)`, which does not
exist: it says that the ideal sheaf `𝒪_X(-D)` of `D`, i.e. the kernel of `𝒪_X ⟶ z_* 𝒪_D`,
is the image of a monomorphism from the dual `ℒᵛ`. The open complement of the support of `D` is
presented by an open immersion `j` whose range is the complement of the range of `z`. -/
theorem isAffine_compl_of_isAmple {D : Scheme.{u}} (z : D ⟶ X) (hz : IsEffectiveCartierCenter z)
    (ℒ : X.Modules) (hℒ : ℒ.IsInvertible) (hample : ℒ.IsAmple)
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

/-- Blueprint `sk-thm-picard-duality`: Serre duality.

Let `X` be a smooth proper geometrically integral curve over `k` of pure relative dimension
`n ≤ 1` and let `ℱ` be a finite locally free `𝒪_X`-module, say of rank `r`. With
`ω_X = Ω^n_{X/k}` the canonical module, the trace pairing is perfect in every degree `q`, i.e.
the `k`-vector space `H^q(X, ℱ)^∨` is isomorphic to `H^{n-q}(X, ℱᵛ ⊗ ω_X)`. -/
theorem serreDuality (n : ℕ) (hn : n ≤ 1) [SmoothOfRelativeDimension n (X ↘ Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))] (ℱ : X.Modules)
    (r : ℕ) (hℱ : ℱ.IsLocallyFreeOfRank r) (q : ℕ) :
    Nonempty (Module.Dual k (ℱ.H q) ≃ₗ[k] (ℱᵛ ⊗ₘ canonicalModule (X ↘ Spec (.of k)) n).H (n - q)) :=
  sorry

end Duality

section BaseChange

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [GeometricallyIntegral (X ↘ Spec (.of k))] (K : Type u) [Field K] [Algebra k K]

/-- Blueprint `sk-cor-picard-degree-g`: The degree of the dictionary.

Let `X` be a smooth projective curve of genus `g` over `k`, let `K/k` be a field extension and
let `ℒ` be a line bundle on the base change `X_K = X ×_{Spec k} Spec K` with `h^0(X_K, ℒ) = 1`
and `H^q(X_K, ℒ) = 0` for `q > 0`. Then `deg ℒ = χ(ℒ) - χ(𝒪_{X_K}) = 1 - (1 - g) = g`. -/
theorem degree_eq_genus
    (ℒ : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
    (hℒ : ℒ.IsInvertible) (h0 : Modules.h K ℒ 0 = 1)
    (hq : ∀ q : ℕ, 0 < q → Subsingleton (ℒ.H q)) :
    ℒ.degree K = (genus k X : ℤ) :=
  sorry

/-- Blueprint `sk-thm-picard-twist`: The twist lemma.

Let `k` be separably closed, let `X` be a smooth projective curve over `k`, let `K/k` be a field
extension and let `ℒ` be a line bundle on the base change `X_K = X ×_{Spec k} Spec K`. Then
there is a line bundle `ℒ₀` on `X` whose restriction to `X_K` twists `ℒ` into the situation of
`AlgebraicGeometry.Scheme.degree_eq_genus`:
`h^0(X_K, ℒ ⊗ ℒ₀|_{X_K}) = 1` and `h^1(X_K, ℒ ⊗ ℒ₀|_{X_K}) = 0`. -/
theorem exists_isInvertible_twist [IsSepClosed k]
    (ℒ : (Limits.pullback (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules)
    (hℒ : ℒ.IsInvertible) :
    ∃ ℒ₀ : X.Modules, ℒ₀.IsInvertible ∧
      Modules.h K (ℒ ⊗ₘ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj ℒ₀) 0 = 1 ∧
      Modules.h K (ℒ ⊗ₘ (Modules.pullback (Limits.pullback.fst (X ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj ℒ₀) 1 = 0 :=
  sorry

end BaseChange

end AlgebraicGeometry.Scheme
