/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.UpperLowerStar

/-!
# The identity isomorphisms of the pro-étale pullback and pushforward

This is the pro-étale counterpart of the section `Id` of
`WeilConjectures.SixFunctors.UpperLowerStar.Defs`.

## Main definitions

- `AlgebraicGeometry.ProEtale.lowerStarId`: the identity isomorphism `(𝟙 X)_* ≅ 𝟭`.
- `AlgebraicGeometry.ProEtale.upperStarId`: the identity isomorphism `(𝟙 X)^* ≅ 𝟭`.
- `AlgebraicGeometry.ProEtale.leftDerivedUpperStarId`: the identity isomorphism
  `L(𝟙 X)^* ≅ 𝟭` of the derived pullback.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (X : Scheme.{u})

/-- The identity isomorphism `(𝟙 X)_* ≅ 𝟭` of the pushforward on pro-étale sheaves: base
change along `𝟙 X` is the identity functor by `MorphismProperty.Over.pullbackId`. -/
noncomputable def lowerStarId : (𝟙 X)_*[A] ≅ 𝟭 _ :=
  Functor.sheafPushforwardContinuousId' (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X) A
    (Scheme.ProEt.topology X)

/-- The identity isomorphism `(𝟙 X)^* ≅ 𝟭` of the pullback on pro-étale sheaves, obtained
from `lowerStarId` by uniqueness of left adjoints: both sides are left adjoint to
`(𝟙 X)_*`. -/
noncomputable def upperStarId : (𝟙 X)^*[A] ≅ 𝟭 _ :=
  (conjugateIsoEquiv Adjunction.id (ProEtale.upperStarLowerStarAdjunction A (𝟙 X))).symm
    (lowerStarId A X).symm

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The identity isomorphism `L(𝟙 X)^* ≅ 𝟭` of the derived pullback on pro-étale sheaves:
the derived functor of `upperStarId`, followed by the identification of the left derived
functor of the exact functor `𝟭` with `(𝟭 _).mapDerivedCategory ≅ 𝟭`. -/
noncomputable def leftDerivedUpperStarId : L((𝟙 X)^*[A]) ≅ 𝟭 _ :=
  Functor.leftDerivedFunctorNatIso _ (upperStarId A X) ≪≫
    (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

end AlgebraicGeometry.ProEtale
