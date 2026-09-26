/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.EtaleCohomology.PoincareDuality.Operations

/-!

# Perfectness at the point and on `X`

The duality theorems of the Poincaré duality chapter are stated for complexes that are
*perfect*, both at the point (the coefficient side) and on `X` (the sheaf side). This file
defines the two notions.

At the point, a *perfect point complex* is an object of `D(Λ)` represented by a bounded
complex of finite projective `Λ`-modules. Over a field this is the same as a bounded complex
with finite-dimensional cohomology.

On `X`, "perfect over `Λ_X`" is recorded in its intrinsic form: an object `K` of `D(X_proét)`
is perfect when it is *dualizable* for the derived tensor product, i.e. admits a right dual in
the monoidal category `D(X_proét)`. This is equivalent to the blueprint's "locally
quasi-isomorphic to a bounded complex of finite projective `Λ_X`-modules", and it is the form
in which perfectness is used: it is exactly what makes the evaluation
`K ⊗ᴸ K^∨ ⟶ Λ_X` and the biduality map behave.

## Main definitions

- `AlgebraicGeometry.ProEtale.IsPerfectPointComplex`: perfectness of an object of the
  coefficient derived category `D(Λ)`.
- `AlgebraicGeometry.ProEtale.IsPerfect`: perfectness over `Λ_X` of an object of
  `D(X_proét)`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

/-- Blueprint `sk-def-perfect`: Perfectness at the point and on `X`.

An object of the derived category of `Λ`-modules is a *perfect point complex* if it is
isomorphic to the image of a bounded complex of finite projective `Λ`-modules. -/
def IsPerfectPointComplex {Λ : Type (u + 1)} [CommRing Λ]
    (C : DerivedCategory (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ (K : CochainComplex (ModuleCat.{u + 1} Λ) ℤ) (a b : ℤ),
    (∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i)) ∧
      (∀ i : ℤ, Module.Finite Λ (K.X i)) ∧ (∀ i : ℤ, Module.Projective Λ (K.X i)) ∧
        Nonempty (C ≅ DerivedCategory.Q.obj K)

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X : Scheme.{u}}

/-- Blueprint `sk-def-perfect`: Perfectness at the point and on `X`.

An object `K` of `D(X_proét)` is *perfect over `Λ_X`* if it is dualizable for the derived
tensor product, that is, if it has a right dual. Concretely this says that `K` is locally
quasi-isomorphic to a bounded complex of finite projective `Λ_X`-modules. -/
def IsPerfect (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) : Prop :=
  Nonempty (HasRightDual K)

end ProEtale

end AlgebraicGeometry
