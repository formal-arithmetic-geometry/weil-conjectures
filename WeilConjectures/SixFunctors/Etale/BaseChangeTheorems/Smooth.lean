/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf

/-!

# The smooth base change theorem

Fix a commutative ring `Λ` and a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `g` **smooth**, recorded as `sq : IsPullback g' f' f g`. This file states the
general smooth base change theorem in étale cohomology: for every object `K` of the
bounded below derived category `D⁺(X_ét, Λ)` all of whose cohomology sheaves are torsion
with order invertible on `Y` , the derived base-change morphism

`BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs` is an isomorphism
if `f` is qcqs.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [QuasiCompact f] [QuasiSeparated f]

/-- **The smooth base change theorem** in étale cohomology. -/
theorem Etale.isIso_baseChange_of_isProper [Smooth g] (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : Etale.DerivedCategory.Plus.orderInvertibleOnHomology f K) :
    IsIso ((Etale.baseChange Ab.{u + 1} sq.toCommSq).app K) :=
  sorry

/-- **The smooth base change theorem as an isomorphism of functors** in étale cohomology. -/
theorem Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring [Smooth g]
    (sq : IsPullback g' f' f g) (htor : ∀ (a : Λ), IsUnit (addOrderOf a : Γ(Y, ⊤))) :
    IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
  sorry

end AlgebraicGeometry
