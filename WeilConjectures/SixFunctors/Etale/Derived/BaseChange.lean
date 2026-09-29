/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square

/-!
# The derived base change map `Lg^* Rf_* ⟶ Rf'_* Lg'^*` on unbounded derived categories

For a commutative square of schemes

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

(`sq : CommSq g' f' f g`) the square isomorphism of pullbacks
`AlgebraicGeometry.Etale.squareUpperStarIso sq : g^* ⋙ f'^* ≅ f^* ⋙ g'^*` derives to an
isomorphism `AlgebraicGeometry.Etale.derivedSquareUpperStarIso sq : Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*`
of total left derived functors on the unbounded derived categories `D(-_ét)`.

The **derived base change map** `AlgebraicGeometry.Etale.derivedBaseChangeMap sq :
Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`, that is `Lg^* Rf_* ⟶ Rf'_* Lg'^*`, is the mate
(`CategoryTheory.mateEquiv`) of the derived square isomorphism with respect to the derived
adjunctions `Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`, exactly as the underived
`AlgebraicGeometry.Etale.baseChangeMap` is the mate of `Etale.squareUpperStarIso`. It is
the exchange `Ex_*` on the unbounded derived categories, which the exchange `Ex_!` needs
since `Rf_!` lives there.

## TODO

Show that `AlgebraicGeometry.Etale.derivedBaseChangeMap` restricts on `D⁺` to
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`.

(blueprint: `sk-def-sf-exchanges`)
-/

@[expose] public section

universe u' u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [HasSmallSiteSheafify A]

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The derived square isomorphism `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a commutative square
`g' ≫ f = f' ≫ g`: the left derived functor of `AlgebraicGeometry.Etale.squareUpperStarIso`,
composed with the composition isomorphisms of left derived functors. -/
noncomputable def derivedSquareUpperStarIso (sq : CommSq g' f' f g) :
    L((g)^*[A]) ⋙ L((f')^*[A]) ≅ L((f)^*[A]) ⋙ L((g')^*[A]) :=
  (Functor.leftDerivedFunctorCompIso (g)^*[A] (f')^*[A]).symm ≪≫
    Functor.leftDerivedFunctorNatIso _ (Etale.squareUpperStarIso A sq) ≪≫
    Functor.leftDerivedFunctorCompIso (f)^*[A] (g')^*[A]

/-- The derived base change map as a `TwoSquare`, for the mate calculus. -/
noncomputable abbrev derivedBaseChangeSquare (sq : CommSq g' f' f g) :
    TwoSquare R((f)_*[A]) L((g')^*[A]) L((g)^*[A]) R((f')_*[A]) :=
  mateEquiv (Etale.derivedUpperStarLowerStarAdjunction A f)
    (Etale.derivedUpperStarLowerStarAdjunction A f')
    (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso A sq).hom)

/-- **The derived base change map** `Ex_* : Lg^* Rf_* ⟶ Rf'_* Lg'^*` of a commutative square,
on the unbounded derived categories of étale sheaves, as a natural transformation
`Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`: the mate of the derived square isomorphism
`AlgebraicGeometry.Etale.derivedSquareUpperStarIso` with respect to the derived adjunctions
`Lf^* ⊣ Rf_*` and `Lf'^* ⊣ Rf'_*`. (blueprint: `sk-def-sf-exchanges`) -/
noncomputable def derivedBaseChangeMap (sq : CommSq g' f' f g) :
    R((f)_*[A]) ⋙ L((g)^*[A]) ⟶ L((g')^*[A]) ⋙ R((f')_*[A]) :=
  (derivedBaseChangeSquare A sq).natTrans

omit [HasSmallSiteSheafify A] in
/-- **The adjoint of the derived base change map** is the derived square isomorphism followed
by the counit: for `K` in `D(X_ét)`,
`Lf'^* (derivedBaseChangeMap K) ≫ ε_{f'} = derivedSquareUpperStarIso (Rf_* K) ≫ Lg'^* (ε_f K)`.
(blueprint: `sk-def-sf-exchanges`) -/
lemma leftDerived_map_derivedBaseChangeMap_app_counit (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (L((f')^*[A])).map ((derivedBaseChangeMap A sq).app K) ≫
        (Etale.derivedUpperStarLowerStarAdjunction A f').counit.app ((L((g')^*[A])).obj K) =
      (derivedSquareUpperStarIso A sq).hom.app ((R((f)_*[A])).obj K) ≫
        (L((g')^*[A])).map ((Etale.derivedUpperStarLowerStarAdjunction A f).counit.app K) :=
  mateEquiv_counit _ _ _ K

omit [HasSmallSiteSheafify A] in
/-- **The unit form of the derived base change map**: for `M` in `D(Y_ét)`,
`Lg^* (η_f M) ≫ derivedBaseChangeMap (Lf^* M) =
η_{f'} (Lg^* M) ≫ Rf'_* (derivedSquareUpperStarIso M)`. -/
lemma map_unit_derivedBaseChangeMap_app (sq : CommSq g' f' f g)
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (L((g)^*[A])).map ((Etale.derivedUpperStarLowerStarAdjunction A f).unit.app M) ≫
        (derivedBaseChangeMap A sq).app ((L((f)^*[A])).obj M) =
      (Etale.derivedUpperStarLowerStarAdjunction A f').unit.app ((L((g)^*[A])).obj M) ≫
        (R((f')_*[A])).map ((derivedSquareUpperStarIso A sq).hom.app M) :=
  unit_mateEquiv _ _ _ M

omit [HasSmallSiteSheafify A] in
/-- **Naturality of the derived base change map** in the complex. -/
lemma derivedBaseChangeMap_naturality (sq : CommSq g' f' f g)
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : K ⟶ K') :
    (L((g)^*[A])).map ((R((f)_*[A])).map φ) ≫ (derivedBaseChangeMap A sq).app K' =
      (derivedBaseChangeMap A sq).app K ≫ (R((f')_*[A])).map ((L((g')^*[A])).map φ) :=
  (derivedBaseChangeMap A sq).naturality φ

end Etale

end AlgebraicGeometry
