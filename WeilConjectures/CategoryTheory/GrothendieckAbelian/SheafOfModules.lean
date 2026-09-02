/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!

# Categories of sheaves of modules are Grothendieck abelian (sorried)

The category `SheafOfModules.{u} R` of sheaves of modules over a sheaf of rings `R` on an
essentially small site is a Grothendieck abelian category. In particular, for a scheme
`X : Scheme.{u}`, the category `X.Modules` of `𝒪_X`-modules is Grothendieck abelian.

This is the single missing link that makes Mathlib's chain of instances fire for `X.Modules`:
a Grothendieck abelian category has enough injectives, hence has injective resolutions, and
`Ext`-groups in it are small. This file records the statement, checks that the chain fires, and
leaves the proof to a future contribution.

**The proof is not formalised.** The general instance is stated with a `sorry`ed proof; see
its docstring for a sketch of why it is true. Since `IsGrothendieckAbelian` is a `Prop`-valued
class, no data is fabricated by doing so.

Note that the instance is nevertheless global, so `#print axioms` reports `sorryAx` on every
declaration whose elaboration goes through it — in particular on `Scheme.Modules.cohomology`
and on the invariants built from it (`eulerCharacteristic`, `degree`, `genus`), none of which
contains a `sorry` of its own.

## Blueprint

`SheafOfModules.isGrothendieckAbelian` implements `lem:pc-sheaves-of-modules-grothendieck`.

-/

@[expose] public section

universe v₁ u₁ u

open CategoryTheory AlgebraicGeometry

namespace SheafOfModules

/-- The category of sheaves of modules over a sheaf of rings `R` on an essentially small site
is Grothendieck abelian.

**This proof is not formalised.** Sketch: the category `PresheafOfModules.{u} R.obj` of
presheaves of modules is Grothendieck abelian, being a locally presentable category in which
filtered colimits are computed sectionwise, hence exact, and which has the separating family
`PresheafOfModules.freeYoneda R.obj` of free modules on representables
(see `Mathlib/Algebra/Category/ModuleCat/Presheaf/Generator.lean`); essential smallness of the
site is what makes that family small. Sheaves of modules form a reflective subcategory of
presheaves of modules whose reflector, sheafification, is exact — this is what the `Abelian`
instance on `SheafOfModules` uses to transfer the abelian structure — and a Giraud subcategory
of a Grothendieck abelian category is again Grothendieck abelian: colimits are computed by
sheafifying the presheaf colimit, filtered colimits stay exact because sheafification is exact,
and the sheafifications of the presheaf generators form a separating family. -/
instance isGrothendieckAbelian {C : Type u₁} [Category.{v₁} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) :=
  sorry

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- The category of `𝒪_X`-modules on a scheme `X` is Grothendieck abelian: the instance above
for the small Zariski site of `X`, whose objects are the open subsets of `X`.

**This proof is not formalised**, since it rests on `SheafOfModules.isGrothendieckAbelian`. -/
instance isGrothendieckAbelian (X : Scheme.{u}) : IsGrothendieckAbelian.{u} X.Modules :=
  inferInstanceAs (IsGrothendieckAbelian.{u} (SheafOfModules.{u} X.ringCatSheaf))

end AlgebraicGeometry.Scheme.Modules

-- Modules on a scheme have enough injectives.
example (X : Scheme.{u}) : EnoughInjectives X.Modules := inferInstance

-- Modules on a scheme have injective resolutions.
example (X : Scheme.{u}) : HasInjectiveResolutions X.Modules := inferInstance

-- `Ext`-groups of modules on a scheme are small.
example (X : Scheme.{u}) : HasExt.{u} X.Modules := inferInstance
