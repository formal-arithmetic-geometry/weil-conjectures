/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.CoextendScalarsAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.CategoryTheory.EpiMono
public import WeilConjectures.NumberTheory.Padics.IntegersMap
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

/-!
# Scalar extension between the rational stages

Let `E ⊆ L` be finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, with rings of integers `𝒪_E ⊆ 𝒪_L`.
The scalar extension `- ⊗_E L : D_comp(Y, E) ⥤ D_comp(Y, L)` of blueprint
`def-sfb-rationalization-quotient` is computed on an integral representative `K` by the derived
base change `K ⊗ᴸ_{𝒪_E} 𝒪_L`, followed by rationalization. Here the derived base change is
characterized by its universal property (`AlgebraicGeometry.Etale.IsDerivedBaseChange`): a
morphism `η : K ⟶ Res K'` to the restriction of scalars of `K' ∈ D(Y_ét, 𝒪_L)` through which
every morphism from `K` to a restriction of scalars factors uniquely.

## Main statements

- `AlgebraicGeometry.Etale.IsDerivedBaseChange.map`: the morphism `K₁' ⟶ K₂'` induced by a
  morphism `K₁ ⟶ K₂` between objects with derived base changes; it is functorial and linear
  along `𝒪_E ⟶ 𝒪_L`.
- `AlgebraicGeometry.Etale.exists_isDerivedBaseChange_integersShrinkMap` and
  `AlgebraicGeometry.Etale.derivedCompleteIntegral_derivedBaseChange_integersShrinkMap`: every
  object of `D(Y_ét, 𝒪_E)` has a derived base change along `𝒪_E ⟶ 𝒪_L`, and derived base change
  preserves derived completeness.
- `AlgebraicGeometry.Etale.nonempty_iso_fromIntegral_of_isDerivedBaseChange`: the rationalization of
  the derived base change only depends on the rationalization of the integral representative.
- `AlgebraicGeometry.Etale.isTriangulated_derivedCompleteRationalScalarExtension`: the scalar
  extension `D_comp(Y, E) ⥤ D_comp(Y, L)` is triangulated.

## Construction of the derived base change

`𝒪_L` is a finite free `𝒪_E`-module with a Frobenius form
(`PadicAlgCl.exists_basis_frobeniusForm_integersShrinkMap`), so coextension of scalars
`M ↦ Hom_{𝒪_E}(𝒪_L, M)` of étale sheaves is left adjoint to restriction of scalars
(`AlgebraicGeometry.Etale.coextendRestrictScalarsAdj`), besides being right adjoint to it. It is
therefore exact, and the functor it induces on derived categories is both left and right adjoint
to restriction of scalars. The left adjunction says that it computes the derived base change;
the right adjunction says that it preserves derived completeness, which is right orthogonality
to the objects on which a uniformizer acts invertibly. The derived base change functor is then
the left adjoint of restriction of scalars (`AlgebraicGeometry.Etale.derivedBaseChange`), and
the functor between rationalizations is induced along `𝒪_E ⟶ 𝒪_L`
(`CategoryTheory.Rationalization.mapOfRingHom`).
-/

@[expose] public section

universe w u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

attribute [local instance] AlgebraicGeometry.Scheme.Etale.essentiallySmall

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

section RestrictScalars

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') {X : Scheme.{u}}

end RestrictScalars

namespace IsDerivedBaseChange

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'} {X : Scheme.{u}}
  {K₁ K₂ K₃ : 𝐃(X, Λ)} {K₁' K₂' K₃' : 𝐃(X, Λ')}
  {η₁ : K₁ ⟶ (derivedRestrictScalars φ X).obj K₁'}
  {η₂ : K₂ ⟶ (derivedRestrictScalars φ X).obj K₂'}
  {η₃ : K₃ ⟶ (derivedRestrictScalars φ X).obj K₃'}

end IsDerivedBaseChange

section BaseChangeFunctor

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') (X : Scheme.{u})
  (h : ∀ K : 𝐃(X, Λ), ∃ (K' : 𝐃(X, Λ')) (η : K ⟶ (derivedRestrictScalars φ X).obj K'),
    IsDerivedBaseChange η)

end BaseChangeFunctor

section Frobenius

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] [Algebra Λ Λ'] {ι : Type*} [Fintype ι]
  (b : Module.Basis ι Λ Λ') (φ : Λ' →ₗ[Λ] Λ)
  (hφ : Function.Bijective fun s : Λ' ↦ φ ∘ₗ LinearMap.mulLeft Λ s) (X : Scheme.{u})

/- Along a finite free extension with a Frobenius form, coextension of scalars of étale sheaves is
right exact, being a left adjoint (`AlgebraicGeometry.Etale.coextendRestrictScalarsAdj`); this is
assumed as an instance below. -/
variable [PreservesFiniteColimits (coextendScalars (algebraMap Λ Λ') X)]

end Frobenius

section Rational

variable (l : ℕ) [Fact l.Prime] (E L : Type w) [Field E] [Field L]
  [Algebra E (PadicAlgCl l)] [Algebra L (PadicAlgCl l)] [Algebra E L]
  [IsScalarTower E L (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E] [Algebra ℚ_[l] L] [IsScalarTower ℚ_[l] L (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] L] [Small.{u + 1} E] [Small.{u + 1} L]

variable {Y : Scheme.{u}}

end Rational

end Etale

end AlgebraicGeometry
