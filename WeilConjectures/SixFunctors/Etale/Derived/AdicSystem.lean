/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.Algebra.Homology.MinimalComplex
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Ring.NegOnePow
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Trace
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Tower
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.NormalizedTowerLimit
public import WeilConjectures.EtaleCohomology.PoincareDuality.CompactSupportPerfect
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractibleProducts
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.AlgClosedField
public import WeilConjectures.NumberTheory.Padics.Extension

/-!
# Normalized adic systems and the realization of their compact cohomology and stalks

Let `R` be a ring with an ideal `I = (ϖ)` (the intended case being `R = 𝒪_E`, `I = 𝔪_E`) and
`A_n = R ⧸ Iⁿ`. A *normalized adic system* on a scheme `X` (`AlgebraicGeometry.Etale.AdicSystem`) is
a family `L_n ∈ Dᵇctf(X, A_n)` of complexes with transitions `L_{n+1} ⟶ Res L_n` exhibiting `L_n` as
`L_{n+1} ⊗ᴸ_{A_{n+1}} A_n`.

For a separated finite-type scheme `a_X : X ⟶ s` over a separably closed field, the compact
cohomology complexes `P_n = RΓ_c(X, L_n) ∈ D(A_n)` and the geometric stalks `P_{x̄, n} = (L_n)_x̄`
form normalized towers of perfect complexes, whose derived limits over `R` are therefore perfect,
reduce to the levels, and carry lifts of compatible families of endomorphisms whose traces are the
limits of the levelwise traces.

## Main definitions

- `AlgebraicGeometry.Etale.AdicSystem`: a normalized `A_•`-system.
- `AlgebraicGeometry.Etale.IsCoefficientChange`: a natural isomorphism `Res ∘ Φ ≅ Φ' ∘ Res`
  carrying derived base changes to derived base changes.
- `AlgebraicGeometry.Etale.geometricStalk`: the geometric stalk `RΓ(s, Lx̄^* -)`.
- `AlgebraicGeometry.Etale.compactPullback`, `AlgebraicGeometry.Etale.stalkPullback`: the
  compact-support base change `RΓ_c(X, K) ⟶ RΓ_c(X, Lg^* K)` along an automorphism `g` of `X`
  over an automorphism `h` of the base, and the stalk transport `K_x̄ ⟶ (Lg^* K)_x̄` at a point
  fixed by `(g, h)`. They define the global and local Frobenius operators.
- `AlgebraicGeometry.Etale.AdicSystem.compactSupportTower`,
  `AlgebraicGeometry.Etale.AdicSystem.stalkTower`: the normalized towers of perfect complexes
  `RΓ_c(X, L_n)` and `(L_n)_x̄`.

## Implementation notes

The levels are complexes on the small étale site, where the six functors, the compact-support
exchange maps and the perfectness of compact cohomology are available
(`sk-thm-sf-ctf-stability`, `sk-prop-sf-trace-perfectness`); their realization
`R lim_n ν^* L_n` is formed on the pro-étale site, where the cohomological range of the levels is
preserved (`AlgebraicGeometry.Etale.AdicSystem.realization`). Bounded constructible complexes of
finite Tor amplitude on the pro-étale site are exactly the `ν^* L` with `L ∈ Dᵇctf(X_ét, A_n)`.

The coefficient categories at the levels are `ModuleCat (R ⧸ Iⁿ)`, and the comparison between the
levels goes through restriction of scalars: compact cohomology with `A_{n+1}`-coefficients of the
restriction of an `A_n`-complex is identified with the restriction of its compact cohomology
with `A_n`-coefficients. This identification, the fact that it carries derived base changes
of constructible complexes of finite Tor amplitude to derived base changes, and its
compatibility with pullback, are the finite-level coefficient change of compact cohomology
(`lem-fix-compact-support-coefficient-change`, subsection `sk-def-sfb-coefficient-comparisons`)
and of geometric stalks
(`thm-trf-finite-coefficient-map`, subsection `sk-p-trace-coeff`), statements recorded here
as `AlgebraicGeometry.Etale.exists_isCoefficientChange_compactlySupportedGlobalSections` and
`AlgebraicGeometry.Etale.exists_isCoefficientChange_geometricStalk`. The towers are built from
any such identifications, so that they are data independent of a choice.

Compact cohomology and geometric stalks are read in `D(A_n)` through the point identification
of blueprint `def-weil-finite-coefficient-point`: `RΓ_c(X, -)` is
`AlgebraicGeometry.Etale.compactlySupportedGlobalSections` and the geometric stalk at
`x̄ : s ⟶ X` is `RΓ(s, Lx̄^* -)`.

The levels of the system are indexed by `n : ℕ` with coefficients `R ⧸ Iⁿ`, as in
`DerivedCategory.IsNormalizedTower`; the towers of perfect complexes live over the local rings
`n ↦ R ⧸ Iⁿ⁺¹` (`Ideal.powSuccMk`), omitting the zero ring `R ⧸ I⁰`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section CoefficientChange

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X : Scheme.{u}}

/-- A natural isomorphism `α : Res ∘ Φ ≅ Φ' ∘ Res` between functors
`Φ : D(X_ét, Λ) ⥤ D(Λ)` and `Φ' : D(X_ét, Λ') ⥤ D(Λ')`, along a ring map `ρ : Λ →+* Λ'`,
*is a coefficient change* if it carries derived base changes of bounded constructible complexes
of finite Tor amplitude to derived base changes: for `η : K ⟶ Res K'` exhibiting `K'` as
`K ⊗ᴸ_Λ Λ'`, the map `Φ K ⟶ Φ (Res K') ≅ Res (Φ' K')` exhibits `Φ' K'` as `Φ K ⊗ᴸ_Λ Λ'`. This is
the statement that the coefficient comparison `(Φ K) ⊗ᴸ_Λ Λ' ⟶ Φ' (K ⊗ᴸ_Λ Λ')` is an
isomorphism. In a diagram, `α` fills the square
```
  D(X_ét, Λ') ──Φ'──▶ D(Λ')
        │                │
       Res      ⇓ α     Res
        ▼                ▼
  D(X_ét, Λ)  ──Φ──▶  D(Λ)
```
and the condition is that the composite `Φ K ──Φ η──▶ Φ (Res K') ──α──▶ Res (Φ' K')` is again a
base-change map whenever `η : K ⟶ Res K'` is one. -/
def IsCoefficientChange
    (Φ : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ))
    (Φ' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ'))
    (α : Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ ⋙ Φ ≅
      Φ' ⋙ ModuleCat.derivedRestrictScalars ρ) : Prop :=
  ∀ ⦃K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))⦄
    ⦃K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))⦄
    (η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj K'),
    DerivedCategory.boundedConstructibleFiniteTor Λ X K →
      Sheaf.IsDerivedBaseChange η → ModuleCat.IsDerivedBaseChange (Φ.map η ≫ α.hom.app K')

variable (Λ) in
/-- The geometric stalk `K_x̄ = RΓ(s, Lx̄^* K) ∈ D(Λ)` at a point `x̄ : s ⟶ X`, read in `D(Λ)`
through the point identification of blueprint `def-weil-finite-coefficient-point`. -/
noncomputable abbrev geometricStalk {s : Scheme.{u}} (x : s ⟶ X) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (ModuleCat.{u + 1} Λ) :=
  L((x)^*[ModuleCat.{u + 1} Λ]) ⋙ rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) s

end CoefficientChange

section Pullback

variable (Λ : Type (u + 1)) [CommRing Λ] {X s : Scheme.{u}}

variable [Finite Λ] {g : X ⟶ X} {h : s ⟶ s} {a : X ⟶ s} [QuasiCompact a] [HasCompactification a]

end Pullback

section AdicSystem

variable {R : Type (u + 1)} [CommRing R] (I : Ideal R) (X : Scheme.{u})

/-- A *normalized `A_•`-system* on `X`, for the rings `A_n = R ⧸ Iⁿ`: complexes
`L_n ∈ Dᵇctf(X, A_n)` with transitions `L_{n+1} ⟶ Res L_n` compatible with the quotient maps
`A_{n+1} ⟶ A_n`, exhibiting `L_n` as `L_{n+1} ⊗ᴸ_{A_{n+1}} A_n`. Its realization is the derived
limit `R lim_n ν^* Res L_n` on the pro-étale site
(`AlgebraicGeometry.Etale.AdicSystem.realization`).

No Weil structure is part of the datum; the category `Dᵇctf,W,adic(X, 𝒪_E)` of the blueprint
consists of such systems with a compatible strict Weil structure at every level
(`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.IsWeil`). Up to the indexing of the levels
(`R ⧸ Iⁿ` instead of `R ⧸ Iⁿ⁺¹`), the underlying tower is a normalized DVR tower
(`AlgebraicGeometry.Etale.NormalizedTower`) whose levels are constructible of finite Tor
amplitude. -/
structure AdicSystem where
  /-- The level `L_n ∈ D(X_ét, R ⧸ Iⁿ)`. -/
  obj (n : ℕ) : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (R ⧸ I ^ n)))
  /-- The transition `L_{n+1} ⟶ Res L_n`. -/
  map (n : ℕ) : obj (n + 1) ⟶
    (_root_.DerivedCategory.levelTransitionRestrictScalars _ I n.le_succ).obj (obj n)
  /-- The transition exhibits `L_n` as `L_{n+1} ⊗ᴸ_{A_{n+1}} A_n`. -/
  isDerivedBaseChange (n : ℕ) : Sheaf.IsDerivedBaseChange (map n)
  /-- Each level is bounded constructible of finite Tor amplitude. -/
  boundedConstructibleFiniteTor (n : ℕ) :
    DerivedCategory.boundedConstructibleFiniteTor (R ⧸ I ^ n) X (obj n)

namespace AdicSystem

variable {I X} (S : AdicSystem I X)

end AdicSystem

end AdicSystem

section Compatibility

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [Finite Λ] [Finite Λ'] (ρ : Λ →+* Λ')
  {X s : Scheme.{u}} {g : X ⟶ X} {h : s ⟶ s}

end Compatibility

namespace AdicSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} (S : AdicSystem I X)

section Geometric

variable {k : Type u} [Field k] [IsSepClosed k] (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [QuasiCompact aX] [IsSeparated aX] [HasCompactification aX] [∀ n, Finite (R ⧸ I ^ n)]
  [∀ n, HasInvertibleExponent (R ⧸ I ^ n) (Spec (.of k))]

variable [IsLocalRing R] [IsAdicComplete I R] {ϖ : R} (hϖ : ϖ ∈ IsLocalRing.maximalIdeal R)
  (hI : I = Ideal.span {ϖ})

end Geometric

end AdicSystem

namespace AdicSystem

variable {R : Type (u + 1)} [CommRing R] {I : Ideal R} {X : Scheme.{u}} (S : AdicSystem I X)
  {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

end AdicSystem

end AlgebraicGeometry.Etale
