/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.LowerShriek.Proper

/-!
# The idempotent of a clopen subscheme on the derived category

For an open immersion `j : U ⟶ X` with closed range, the derived category `D(X_proét)`
carries a canonical endomorphism `e_U : 𝟭 ⟶ 𝟭` of its identity functor, "multiplication by
the characteristic function of `U`": the composite

```
  𝟭 ──η──▶ Rj_* Lj^* ≃ j_* j^* ≃ j_! j^* ──ε──▶ 𝟭
```

of the unit of `Lj^* ⊣ Rj_*`, the levelwise identifications `Lj^* ≃ j^*` and `Rj_* ≃ j_*` of
the derived functors of the exact functors `j^*` and `j_*`, the inverse of the comparison
`j_! ⟶ j_*` (an isomorphism because the range of `j` is closed) and the counit of the derived
adjunction `j_! ⊣ j^*`.

Every map in it is canonical: none depends on a choice of compactification.

## Main definitions

- `AlgebraicGeometry.ProEtale.clopenIdempotent`: the endomorphism `e_U` of the identity
  functor of `D(X_proét)`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j` with closed range, the pushforward `j_*` is right exact: it is
isomorphic to the extension by zero `j_!`, a left adjoint. -/
lemma preservesFiniteColimits_lowerStar_of_isClosed_range (hj : IsClosed (Set.range j.base)) :
    PreservesFiniteColimits (j)_*[A] :=
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j hj
  preservesFiniteColimits_of_natIso (asIso (openImmersionLowerShriekToLowerStar A j))

/-- The derived pushforward along an open immersion `j` with closed range is the extension by
zero applied levelwise, `Rj_* ≃ j_*` (`j_*` is exact) followed by the inverse of the
comparison `j_! ≃ j_*`. -/
noncomputable def rightDerivedLowerStarIsoOfIsClosedRange (hj : IsClosed (Set.range j.base)) :
    R((j)_*[A]) ≅ D((j)_!open[A]) :=
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range A j hj
  have := preservesFiniteColimits_lowerStar_of_isClosed_range A j hj
  (j)_*[A].rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (openImmersionLowerShriekToLowerStar A j)).symm

/- The K-flat resolution package on `A`, which makes the derived pullback `Lj^*` and the
derived adjunction `j_! ⊣ j^*` available. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The idempotent `e_U : 𝟭 ⟶ 𝟭` of the clopen subscheme `U` on `D(X_proét)`, for an open
immersion `j : U ⟶ X` with closed range: the composite

```
  𝟭 ──η──▶ Rj_* Lj^* ≃ j_! j^* ──ε──▶ 𝟭
```

of the unit of `Lj^* ⊣ Rj_*`, `Lj^* ≃ j^*`, `rightDerivedLowerStarIsoOfIsClosedRange` and
the counit of the derived adjunction `j_! ⊣ j^*`. -/
noncomputable def clopenIdempotent (hj : IsClosed (Set.range j.base)) :
    𝟭 (DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) ⟶ 𝟭 _ :=
  (derivedUpperStarLowerStarAdjunction A j).unit ≫
    (Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A j) _ ≪≫
      Functor.isoWhiskerLeft _ (rightDerivedLowerStarIsoOfIsClosedRange A j hj)).hom ≫
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit

end AlgebraicGeometry.ProEtale
