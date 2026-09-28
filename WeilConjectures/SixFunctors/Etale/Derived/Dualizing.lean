/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Perfect
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!

# The dualizing complex and Verdier duality on the étale site

Let `A` be a monoidal Grothendieck abelian coefficient category, let `S` be a base scheme and
let `a : X ⟶ S` be a structure morphism admitting a compactification. The *dualizing complex*
of `X` over `S` is `ω_X = Ra^! Λ_S`, the exceptional inverse image of the monoidal unit, and
the *Verdier dual* is `𝔻_X = RHom_X(-, ω_X)`.

## Main definitions

- `AlgebraicGeometry.Etale.dualizingComplex`: `ω_X = Ra^! Λ_S`.
- `AlgebraicGeometry.Etale.verdierDual`: `𝔻_X = RHom_X(-, ω_X)`.

## Main statements

- `AlgebraicGeometry.Etale.constructibleFiniteTor_verdierDual`
  (`sk-prop-sf-biduality-general`): `𝔻_X` carries `Dctf(X, A)` into itself.
- `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_verdierDual`
  (`sk-prop-sf-biduality-general`): general Verdier biduality, `𝔻_X 𝔻_X ≅ id` on `Dctf(X, A)`.

## Implementation notes

The blueprint's `sk-prop-sf-biduality-general` is stated for a finite-type scheme over a
separably closed field and for one of the coefficient stages, whose algebraic input is that
the stage is a quasi-Frobenius ring. Neither hypothesis is expressible for the general
coefficient category `A` used throughout this directory, so the statements below are made
relatively, for an arbitrary morphism `a : X ⟶ S` carrying a compactification. This is the
uniform convention of the `SixFunctors` folder; the absolute case is `S = Spec k`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X S : Scheme.{u}} (a : X ⟶ S) [HasCompactification a]

namespace Etale

/-- The dualizing complex `ω_X = Ra^! Λ_S` of a scheme `X` over a base `S`, the exceptional
inverse image along the structure morphism `a : X ⟶ S` of the monoidal unit `Λ_S`. -/
noncomputable def dualizingComplex : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (R(a)^![A]).obj (𝟙_ _)

/-- The Verdier dual `𝔻_X = RHom_X(-, ω_X) : D(X_ét)ᵒᵖ ⥤ D(X_ét)`, the internal hom into the
dualizing complex `AlgebraicGeometry.Etale.dualizingComplex`. -/
noncomputable def verdierDual :
    (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))ᵒᵖ ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (RHom(X)[A]).flip.obj (dualizingComplex A a)

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- Blueprint `sk-prop-sf-biduality-general`: General Verdier biduality.

The Verdier dual `𝔻_X = RHom(-, ω_X)` carries `Dctf(X, A)` into itself. -/
theorem constructibleFiniteTor_verdierDual
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K) :
    DerivedCategory.constructibleFiniteTor A X ((verdierDual A a).obj (op K)) :=
  sorry

/-- Blueprint `sk-prop-sf-biduality-general`: General Verdier biduality.

The Verdier dual is a contravariant anti-equivalence of `Dctf(X, A)`: the double-dual morphism
`K ⟶ 𝔻_X 𝔻_X K` is an isomorphism for every object `K` of `Dctf(X, A)`. -/
theorem nonempty_iso_verdierDual_verdierDual
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K) :
    Nonempty (K ≅ (verdierDual A a).obj (op ((verdierDual A a).obj (op K)))) :=
  sorry

end Etale

end AlgebraicGeometry
