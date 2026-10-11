/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# The derived pullback along the identity

`AlgebraicGeometry.Etale.leftDerivedUpperStarId`: the derived pullback `L(𝟙 X)^*` on `D(X_ét)`
is the identity. This is the étale counterpart of
`AlgebraicGeometry.ProEtale.leftDerivedUpperStarId`.
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived pullback along the identity is the identity: `L(𝟙 X)^* ≅ 𝟭`. It is the
comparison `L(𝟙 X)^* ≅ D((𝟙 X)^*)` for the exact functor `(𝟙 X)^*`, followed by the functor
induced by `(𝟙 X)^* ≅ 𝟭` and `D(𝟭) ≅ 𝟭`. -/
noncomputable def leftDerivedUpperStarId (X : Scheme.{u}) : L((𝟙 X)^*[A]) ≅ 𝟭 _ :=
  leftDerivedUpperStarIsoMapDerivedCategory A (𝟙 X) ≪≫
    Functor.mapDerivedCategoryNatIso (Etale.upperStarId A X) ≪≫
      Functor.mapDerivedCategoryIdIso _

end AlgebraicGeometry.Etale
