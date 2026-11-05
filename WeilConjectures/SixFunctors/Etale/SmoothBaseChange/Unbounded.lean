/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension

/-!
# Smooth base change on the unbounded derived categories

Consider a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `g` smooth and `f` quasi-compact, quasi-separated and locally of finite type, `Y` locally of
finite type over a separably closed field `k`, and a coefficient ring `Λ` killed by an integer
invertible on `Y`. This file upgrades the smooth base change theorem
`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth` to the unbounded derived
categories: the derived base change map

`Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`

of `D(-_ét, Λ)` is an isomorphism (`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_smooth`).

The argument is the one of the unbounded proper base change theorem
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`, through
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isIso_baseChangeMap`:

* in degree `0` the smooth base change theorem says that the underived base change map
  `g^* f_* ⟶ f'_* g'^*` is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_baseChangeMap_of_smooth`);
* in positive degrees it says that `g'^*` of an injective sheaf is `f'_*`-acyclic;
* the higher direct images along `f'` vanish, at each geometric point of `Y'`, above a bound
  only depending on the point: over an affine open neighbourhood `V` of the point, smooth base
  change along the open immersion `V ⟶ Y'` identifies them with the higher direct images along
  `X' ×_{Y'} V ⟶ V`, which vanish above twice the dimension of the quasi-compact scheme
  `X' ×_{Y'} V` (`AlgebraicGeometry.Etale.isZero_higherDirectImage_of_two_mul_lt`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

namespace Etale

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- The degree-`q` smooth base change map at a sheaf `F`, read as a map
`g^* R^q f_* F ⟶ R^q f'_* g'^* F` between the classical higher direct images. Its source is
identified with `g^*` of `R^q f_* F` and its target with `R^q f'_*` of `g'^* F`. -/
noncomputable def baseChangeHomologyMapSourceIso (p : X ⟶ Y) (q : ℕ)
    (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (h : X' ⟶ Y) :
    (Etale.baseChangeSourceFunctor Λ p h q).obj F ≅
      (p)^*[ModuleCat.{u + 1} Λ].obj ((((h)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F) :=
  (((p)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusHomologyFunctorIso q).symm.app
      ((h)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
    (p)^*[ModuleCat.{u + 1} Λ].mapIso
      ((h)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorPlusObjSingleFunctorIso F q)

/-- The target of the degree-`q` base change map at `F` is `R^q h_*` of `e^* F`. -/
noncomputable def baseChangeHomologyMapTargetIso (e : Y ⟶ X') (h : Y ⟶ X) (q : ℕ)
    (F : Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Etale.baseChangeTargetFunctor Λ e h q).obj F ≅
      (((h)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj ((e)^*[ModuleCat.{u + 1} Λ].obj F) :=
  (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((h)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlus.mapIso
        ((((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).app F)) ≪≫
    (h)_*[ModuleCat.{u + 1} Λ].homologyRightDerivedFunctorPlusObjSingleFunctorIso _ q

section

variable [HasInvertibleExponent Λ Y] [Smooth g] [QuasiCompact f] [QuasiSeparated f]

end

end Etale

end AlgebraicGeometry
