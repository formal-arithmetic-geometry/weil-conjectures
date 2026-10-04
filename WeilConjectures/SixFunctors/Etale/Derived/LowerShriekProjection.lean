/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-!
# The projection map for the compactly supported direct image

Let `f : X ⟶ Y` be a morphism of schemes with a compactification
`c = (X ⟶[i] Z ⟶[g] Y)`, so that `Rf_!(c) = Di_! ⋙ Rg_*`. We construct the projection map
```
PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)
```
natural in `K` in `D(X_ét)` and `L` in `D(Y_ét)`, as the composite
```
Rg_*(i_!K) ⊗ᴸ L
  | rightDerivedLowerStarProjectionMap g
  v
Rg_*(i_!K ⊗ᴸ Lg^*L)
  | Rg_*(derivedOpenImmersionLowerShriekProjectionIso i).inv
  v
Rg_*(i_!(K ⊗ᴸ Li^*Lg^*L))
  | Rg_*i_!(K ⊗ᴸ Compactification.leftDerivedUpperStarCompIso c)
  v
Rg_*(i_!(K ⊗ᴸ Lf^*L))
```
The last two arrows are `Rg_*` applied to the isomorphism
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIsoOfCompactification c`.

## Main definitions and results

- `AlgebraicGeometry.Etale.derivedTensorRightDerivedLowerShriek c` and
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar c`: the
  bifunctors `(K, L) ↦ Rf_!(c)K ⊗ᴸ L` and `(K, L) ↦ Rf_!(c)(K ⊗ᴸ Lf^*L)`, of type
  `D(X_ét) ⥤ D(Y_ét) ⥤ D(Y_ét)`.
- `AlgebraicGeometry.Compactification.leftDerivedUpperStarCompIso c`: the isomorphism
  `Lg^* ⋙ Li^* ≅ Lf^*`.
- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIsoOfCompactification c`:
  the isomorphism `i_!K ⊗ᴸ Lg^*L ≅ i_!(K ⊗ᴸ Lf^*L)` of bifunctors
  `D(X_ét) ⥤ D(Y_ét) ⥤ D(Z_ét)`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekProjectionMapOfCompactification c`: the
  projection map `PF_c`, as a natural transformation between these bifunctors.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekProjectionMap f`: the projection map for the
  chosen compactification `HasCompactification.compactification f`.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekProjectionMapOfCompactification_app_app`:
  the value of `PF_c` at `(K, L)` is the composite above.

The results depend on `sorryAx` through `AlgebraicGeometry.Etale.derivedTensor`.

## Implementation notes

The open-immersion step uses
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso`, whose proof that the
open-immersion projection map is an isomorphism goes through open–closed conservativity on
stalks. That proof needs a concrete structure on `A` whose forgetful functor
reflects isomorphisms, preserves filtered colimits and preserves sheaves on `Z_ét`; these
hypotheses therefore appear on `PF_c`. They hold for `A = ModuleCat Λ`.

`AlgebraicGeometry.Etale.rightDerivedLowerShriekProjectionMap` asks for `HasSheafCompose` on
every scheme rather than only on the scheme of the chosen compactification, so that the
statements using it do not have to name `(HasCompactification.compactification f).Z`.

## TODO

- Generalise `AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_closedComplement_map`
  to Grothendieck abelian coefficients without a concrete structure, and with it
  `AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekProjectionMap`. Then `PF_c`
  only needs `Etale.UpperStarPreservesFlat A`, and the concrete-category hypotheses can be
  dropped here and downstream.
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

namespace Compactification

open Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The isomorphism `Lg^* ⋙ Li^* ≅ Lf^*` for a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of
`f`: the inverse of `AlgebraicGeometry.Etale.leftDerivedUpperStarComp` for `f = i ≫ g`. -/
noncomputable def leftDerivedUpperStarCompIso :
    L((c.g)^*[A]) ⋙ L((c.i)^*[A]) ≅ L((f)^*[A]) :=
  (leftDerivedUpperStarComp A c.i c.g f c.comm).symm

@[simp]
lemma leftDerivedUpperStarCompIso_hom :
    (c.leftDerivedUpperStarCompIso A).hom = (leftDerivedUpperStarComp A c.i c.g f c.comm).inv :=
  rfl

@[simp]
lemma leftDerivedUpperStarCompIso_inv :
    (c.leftDerivedUpperStarCompIso A).inv = (leftDerivedUpperStarComp A c.i c.g f c.comm).hom :=
  rfl

end Compactification

namespace Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The bifunctor `(K, L) ↦ Rf_!(c)K ⊗ᴸ L`, of type `D(X_ét) ⥤ D(Y_ét) ⥤ D(Y_ét)`. -/
noncomputable def derivedTensorRightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  Rf_!(c)[A] ⋙ -⊗ᴸ-(Y)[A]

@[simp]
lemma derivedTensorRightDerivedLowerShriek_obj_obj
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((derivedTensorRightDerivedLowerShriek A c).obj K).obj L =
      ((-⊗ᴸ-(Y)[A]).obj ((Rf_!(c)[A]).obj K)).obj L :=
  rfl

/-- The bifunctor `(K, L) ↦ Rf_!(c)(K ⊗ᴸ Lf^*L)`, of type `D(X_ét) ⥤ D(Y_ét) ⥤ D(Y_ét)`. -/
noncomputable def rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Functor.postcompose₂.obj Rf_!(c)[A]).obj
    ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((f)^*[A])).obj (-⊗ᴸ-(X)[A]))

@[simp]
lemma rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar_obj_obj
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar A c).obj K).obj L =
      (Rf_!(c)[A]).obj (((-⊗ᴸ-(X)[A]).obj K).obj (L((f)^*[A]).obj L)) :=
  rfl

variable [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]

/-- The isomorphism `i_!K ⊗ᴸ Lg^*L ≅ i_!(K ⊗ᴸ Lf^*L)` of bifunctors
`D(X_ét) ⥤ D(Y_ét) ⥤ D(Z_ét)`, for a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`:
```
i_!K ⊗ᴸ Lg^*L
  | (derivedOpenImmersionLowerShriekProjectionIso i).inv
  v
i_!(K ⊗ᴸ Li^*Lg^*L)
  | i_!(K ⊗ᴸ Compactification.leftDerivedUpperStarCompIso c)
  v
i_!(K ⊗ᴸ Lf^*L)
``` -/
noncomputable def derivedOpenImmersionLowerShriekProjectionIsoOfCompactification
    [c.Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] :
    (((Functor.whiskeringLeft₂ _).obj D((c.i)_!open[A])).obj L((c.g)^*[A])).obj
        (-⊗ᴸ-(c.Z)[A]) ≅
      (Functor.postcompose₂.obj D((c.i)_!open[A])).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((f)^*[A])).obj (-⊗ᴸ-(X)[A])) :=
  (Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekProjectionIso A c.i)
      ((Functor.whiskeringLeft _ _ _).obj L((c.g)^*[A]))).symm ≪≫
    Functor.isoWhiskerLeft ((Functor.postcompose₂.obj D((c.i)_!open[A])).obj (-⊗ᴸ-(X)[A]))
      ((Functor.whiskeringLeft _ _ _).mapIso (c.leftDerivedUpperStarCompIso A))

@[reassoc (attr := simp)]
lemma derivedOpenImmersionLowerShriekProjectionIsoOfCompactification_hom_app_app
    [c.Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (((derivedOpenImmersionLowerShriekProjectionIsoOfCompactification A c).hom.app K).app L) =
      ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
          (L((c.g)^*[A]).obj L) ≫
        D((c.i)_!open[A]).map
          (((-⊗ᴸ-(X)[A]).obj K).map ((c.leftDerivedUpperStarCompIso A).hom.app L)) :=
  rfl

/-- The **projection map** `PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)` for a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, as a natural transformation of bifunctors
`D(X_ét) ⥤ D(Y_ét) ⥤ D(Y_ét)`. It is the composite
```
Rg_*(i_!K) ⊗ᴸ L
  | rightDerivedLowerStarProjectionMap g
  v
Rg_*(i_!K ⊗ᴸ Lg^*L)
  | Rg_*(derivedOpenImmersionLowerShriekProjectionIso i).inv
  v
Rg_*(i_!(K ⊗ᴸ Li^*Lg^*L))
  | Rg_*i_!(K ⊗ᴸ Compactification.leftDerivedUpperStarCompIso c)
  v
Rg_*(i_!(K ⊗ᴸ Lf^*L))
```
where the last two arrows form `Rg_*` of
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIsoOfCompactification c`. -/
noncomputable def rightDerivedLowerShriekProjectionMapOfCompactification
    [c.Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] :
    derivedTensorRightDerivedLowerShriek A c ⟶
      rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar A c :=
  Functor.whiskerLeft D((c.i)_!open[A]) (rightDerivedLowerStarProjectionMap A c.g) ≫
    (Functor.postcompose₂.obj R((c.g)_*[A])).map
      (derivedOpenImmersionLowerShriekProjectionIsoOfCompactification A c).hom

/-- The value of the projection map `PF_c` at `(K, L)` is the composite of the three arrows
in the docstring of
`AlgebraicGeometry.Etale.rightDerivedLowerShriekProjectionMapOfCompactification`. -/
@[reassoc (attr := simp)]
lemma rightDerivedLowerShriekProjectionMapOfCompactification_app_app
    [c.Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((rightDerivedLowerShriekProjectionMapOfCompactification A c).app K).app L =
      ((rightDerivedLowerStarProjectionMap A c.g).app (D((c.i)_!open[A]).obj K)).app L ≫
        R((c.g)_*[A]).map
          (((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
            (L((c.g)^*[A]).obj L)) ≫
        R((c.g)_*[A]).map (D((c.i)_!open[A]).map (((-⊗ᴸ-(X)[A]).obj K).map
          ((c.leftDerivedUpperStarCompIso A).hom.app L))) := by
  simp [rightDerivedLowerShriekProjectionMapOfCompactification]

/-- The **projection map** `PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` for a morphism
`f : X ⟶ Y` admitting a compactification: the projection map
`AlgebraicGeometry.Etale.rightDerivedLowerShriekProjectionMapOfCompactification` for the chosen
compactification `HasCompactification.compactification f`. -/
noncomputable def rightDerivedLowerShriekProjectionMap (f : X ⟶ Y) [HasCompactification f]
    [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)] :
    derivedTensorRightDerivedLowerShriek A (HasCompactification.compactification f) ⟶
      rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar A
        (HasCompactification.compactification f) :=
  rightDerivedLowerShriekProjectionMapOfCompactification A
    (HasCompactification.compactification f)

end Etale

end AlgebraicGeometry
