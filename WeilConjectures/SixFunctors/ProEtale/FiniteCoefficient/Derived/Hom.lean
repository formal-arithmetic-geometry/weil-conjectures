/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!

# The derived internal hom of pro-étale sheaves

Let `A` be a monoidal Grothendieck abelian coefficient category and let `X` be a scheme, so
that the derived category `D(X_proét)` of `A`-valued pro-étale sheaves on `X` carries the derived
tensor product `- ⊗ᴸ -` of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`.
Under the same hypotheses `D(X_proét)` is monoidal closed
(`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`), and this file defines the
*derived hom* of pro-étale sheaves to be the internal hom of that closed structure, i.e. the right
adjoint of the derived tensor product.

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedHom` : the derived hom
  `RHom(-, -) : D(X_proét)ᵒᵖ ⥤ D(X_proét) ⥤ D(X_proét)`, with scoped
  notation `RHom(X)[A]`.

## Main results

- `AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction₂` : the adjunction with parameter
  `- ⊗ᴸ - ⊣₂ RHom(-, -)` expressing that the derived hom is the internal hom of the derived
  tensor product.

- `AlgebraicGeometry.ProEtale.derivedTensorHomAdjunction` : its unary shadow, the adjunction
  `K ⊗ᴸ - ⊣ RHom(K, -)` for a fixed `K : D(X_proét)`.

## Implementation notes

This is the pro-étale counterpart of `WeilConjectures.SixFunctors.Etale.Derived.Hom`.

As in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`, the monoidal
structure on `Sheaf (Scheme.ProEt.topology X) A` is the global instance
`AlgebraicGeometry.ProEtale.sheafMonoidalCategory`. The *type* of `derivedHom` does not
mention it.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

namespace ProEtale

@[inherit_doc derivedHom]
scoped notation "RHom(" X ")[" A "]" => derivedHom A X

variable {X}

end ProEtale

end AlgebraicGeometry
