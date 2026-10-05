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
- `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`: Tor amplitude in `[a, b]`.
  Finite Tor amplitude is `AlgebraicGeometry.Etale.DerivedCategory.finiteTorAmplitude` of
  `WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`, for `A = ModuleCat Λ`.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleFiniteTor`:
  `D^b_{ctf}(X, Λ)`.
- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible`: ⊗-invertible objects.
- `AlgebraicGeometry.Etale.reductionModIdeal`: reduction of coefficients `K ↦ K ⊗^L (Λ/J)_X`.
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
It is the coefficient object every statement of the purity chapter is normalized against. -/
noncomputable def constantComplex :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  𝟙_ _

/-- Blueprint `sk-def-sf-setting`: Coefficients and sites

An object `K` of `D(X_ét, Λ)` has *Tor amplitude in `[a, b]`* if for every sheaf `F` of
`Λ`-modules on `X_ét` the derived tensor product `K ⊗^L F` has vanishing cohomology outside
`[a, b]`. -/
def DerivedCategory.hasTorAmplitudeIn (a b : ℤ) :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  fun K ↦ ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ), q < a ∨ b < q →
    IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
      ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)))

/-- Blueprint `sk-def-sf-setting`: Coefficients and sites

The category `D^b_{ctf}(X, Λ)` of the purity chapter, as an object property: bounded with
constructible cohomology sheaves and of finite Tor amplitude. -/
def DerivedCategory.boundedConstructibleFiniteTor :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X ⊓
    DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} Λ) X

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

end Etale

end AlgebraicGeometry
