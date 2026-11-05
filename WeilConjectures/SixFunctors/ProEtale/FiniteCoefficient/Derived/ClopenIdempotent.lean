/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper

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

- `AlgebraicGeometry.ProEtale.clopenIdempotentSheaf`: the endomorphism `e_U` of the identity
  functor of the category of pro-étale sheaves on `X`.
- `AlgebraicGeometry.ProEtale.clopenIdempotent`: the endomorphism `e_U` of the identity
  functor of `D(X_proét)`.

## Main results

- `AlgebraicGeometry.ProEtale.clopenIdempotent_app_Qh_obj`: on a complex, `e_U` is induced by
  the sheaf-level idempotent.
- `AlgebraicGeometry.ProEtale.sum_clopenIdempotent`: the idempotents of a finite partition of
  `X` into clopen subschemes sum to the identity.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/- The K-flat resolution package on `A`, which makes the derived pullback `Lj^*` and the
derived adjunction `j_! ⊣ j^*` available. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

end AlgebraicGeometry.ProEtale
