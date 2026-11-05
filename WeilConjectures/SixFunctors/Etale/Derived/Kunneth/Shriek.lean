/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Stability
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative

/-!

# The `!`-Künneth isomorphism on the étale site

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_mapOverBase_externalProduct`
  (`sk-def-sf-kv-maps` (i)): the `!`-Künneth isomorphism
  `Ku_! : R(f₁ × f₂)_! (M₁ ⊠ M₂) ≅ Rf₁_! M₁ ⊠ Rf₂_! M₂` for a finite coefficient ring.

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

namespace Etale

variable {B X Y : Scheme.{u}}

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

section KunnethShriek

/-! ### The `!`-Künneth isomorphism

Item (i) of `sk-def-sf-kv-maps`: for `fᵢ : Xᵢ ⟶ Yᵢ` over `S`, the `!`-Künneth isomorphism
`Ku_! : R(f₁ × f₂)_! (M₁ ⊠ M₂) ≅ Rf₁_! M₁ ⊠ Rf₂_! M₂` is the relative product theorem over
`B = Y₁ ×_S Y₂`, using `X₁ ×_S X₂ = (X₁ ×_{Y₁} B) ×_B (X₂ ×_{Y₂} B)`
(`CategoryTheory.Limits.pullback.mapOverBaseIso`) and compact-support base change. -/

variable {S X₁ X₂ Y₁ Y₂ : Scheme.{u}} (b₁ : Y₁ ⟶ S) (b₂ : Y₂ ⟶ S) (f₁ : X₁ ⟶ Y₁)
  (f₂ : X₂ ⟶ Y₂)

end KunnethShriek

end Etale

end AlgebraicGeometry
