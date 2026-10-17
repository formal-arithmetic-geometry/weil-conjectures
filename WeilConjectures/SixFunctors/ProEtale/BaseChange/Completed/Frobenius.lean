/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.CompletedBaseChange.FrobeniusEquivalence
public import WeilConjectures.CategoryTheory.CompletedBaseChange.FrobeniusTower
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.Completed.Rectangle
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence

/-!
# Frobenius-equivariant pro-étale base change squares

Let
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
be a commutative square of schemes and let `Fr_X, Fr_Y, Fr_{X'}, Fr_{Y'}` be automorphisms of the
four corners commuting with the four edges,
`f Fr_X = Fr_Y f`, `g Fr_{Y'} = Fr_Y g`, `g' Fr_{X'} = Fr_X g'`, `f' Fr_{X'} = Fr_{Y'} f'`
(`def-weil-pbc-frobenius-tower-datum`). The derived pullbacks `Φ_Z = L Fr_Z^*` are equivalences
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarEquivalence`), the four faces of the Frobenius cube
carry the square isomorphisms `AlgebraicGeometry.ProEtale.leftDerivedUpperStarSquareIso`, and the
cube of these isomorphisms commutes with the Cartesian identification of the square
(`AlgebraicGeometry.ProEtale.frobeniusCube`). This gives a Frobenius datum
`AlgebraicGeometry.ProEtale.frobeniusDatum` on the pro-étale base change square
`AlgebraicGeometry.ProEtale.baseChangeSquare`, whose proper exchange maps
`β_f : Φ_Y Rf_* ≅ Rf_* Φ_X` are invertible because the `Φ_Z` are equivalences.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

/-- The derived pullback along an isomorphism of schemes `e : X ≅ Y` is an equivalence
`D(Y_proét) ≌ D(X_proét)` with inverse the derived pullback along `e⁻¹`. -/
noncomputable def leftDerivedUpperStarEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A) ≌
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  CategoryTheory.Equivalence.mk L((e.hom)^*[A]) L((e.inv)^*[A])
    ((leftDerivedUpperStarId A Y).symm ≪≫ leftDerivedUpperStarCongr A e.inv_hom_id.symm ≪≫
      leftDerivedUpperStarComp A e.inv e.hom)
    ((leftDerivedUpperStarComp A e.hom e.inv).symm ≪≫ leftDerivedUpperStarCongr A e.hom_inv_id ≪≫
      leftDerivedUpperStarId A X)

instance isEquivalence_leftDerivedUpperStar {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] :
    L((e)^*[A]).IsEquivalence :=
  (leftDerivedUpperStarEquivalence A (asIso e)).isEquivalence_functor

end ProEtale

end AlgebraicGeometry
