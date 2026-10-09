/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-!
# Coefficient-side vocabulary of `D(X_ét, Λ)`

The tensor-side finiteness vocabulary of the six-functor formalism: the constant complex
`Λ_X`, Tor amplitude, the category `D^b_{ctf}(X, Λ)` of bounded constructible complexes of
finite Tor amplitude, and ⊗-invertible objects.

These belong to the framework, not to any one chapter: the finiteness statements of
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness` and the purity conventions of
`WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions` both use them.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategoryModule`: the derived category `D(X_ét, Λ)`.
- `AlgebraicGeometry.Etale.constantComplex`: the constant complex `Λ_X`, the unit of the
  derived tensor product.
- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible`: ⊗-invertible objects.
- `AlgebraicGeometry.Etale.reductionModIdeal`: reduction of coefficients `K ↦ K ⊗^L (Λ/J)_X`.

Tor amplitude, finite Tor amplitude and `D^b_{ctf}` are not redefined for `Λ`: they are
`AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn`, `…finiteTorAmplitude` and
`…constructibleFiniteTor` of `WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude` for
`A = ModuleCat Λ`.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor_constantComplex`
- `AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor_shift`
- `AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor_derivedTensor`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
abbrev DerivedCategoryModule : Type (u + 2) :=
  DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- Blueprint `sk-def-sf-setting`: Coefficients and sites

The constant complex `Λ_X ∈ D(X_ét, Λ)`: the constant sheaf with value `Λ` placed in degree
zero, which is the unit of the derived tensor product `AlgebraicGeometry.Etale.derivedTensor`.
It is the coefficient object every statement of the purity chapter is normalized against; it
is only a name for the monoidal unit `𝟙_ _` of `D(X_ét, Λ)`. -/
noncomputable abbrev constantComplex :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  𝟙_ _

/-- An object `L` of `D(X_ét, Λ)` is *invertible* if it has a tensor inverse: there is an `M`
with `L ⊗^L M ≅ Λ_X`. A lisse rank-one sheaf placed in any degree and twisted by any power of
the Tate object is invertible in this sense, and these are the only invertible objects that
occur in the purity chapter. -/
def DerivedCategory.isInvertible :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun L ↦ ∃ M, Nonempty
    (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj L).obj M ≅ constantComplex Λ X)

/-- Reduction of coefficients along a quotient of the coefficient ring: the functor
`K ↦ K ⊗^L (Λ/J)_X` on `D(X_ét, Λ)`. For `Λ = A_{E,n}` and `J = ϖ^m` this is the finite
reduction `K ↦ K_m` of the adic formalism. -/
noncomputable def reductionModIdeal (J : Ideal Λ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ J))))

/-- Blueprint `sk-def-sf-setting`: Coefficients and sites

For a finite coefficient ring the constant complex lies in `D^b_{ctf}`: `Λ_X` is the constant
sheaf `Λ` in degree zero, which is constructible for the one-stratum stratification (its stalks
are `Λ`, finite), bounded, and flat, so of Tor amplitude `[0, 0]`. -/
theorem DerivedCategory.constructibleFiniteTor_constantComplex [Finite Λ] :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (constantComplex Λ X) :=
  sorry

/-- Blueprint `sk-def-sf-setting`: Coefficients and sites

`D^b_{ctf}(X, Λ)` is stable under shifts: shifting moves the cohomology sheaves and the Tor
amplitude by the same amount. -/
theorem DerivedCategory.constructibleFiniteTor_shift
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) (n : ℤ) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (K⟦n⟧) :=
  sorry

/-- Blueprint `sk-def-sf-setting`: Coefficients and sites

For a finite coefficient ring `D^b_{ctf}(X, Λ)` is stable under the derived tensor product: if
`K` has Tor amplitude in `[a, b]` and `L` in `[c, e]`, then `K ⊗^L L` has Tor amplitude in
`[a + c, b + e]`; it is bounded, and its cohomology sheaves are constructible, as one sees on a
common stratification over which `K` and `L` have bounded flat models with finite locally
constant terms. -/
theorem DerivedCategory.constructibleFiniteTor_derivedTensor [Finite Λ]
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hL : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X L) :
    DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj L) :=
  sorry

end Etale

end AlgebraicGeometry
