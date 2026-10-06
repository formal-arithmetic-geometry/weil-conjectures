/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.CategoryTheory.ModuleObjects.Braided

/-!

# The derived category of module objects and the derived tensor product

Let `C` be a symmetric monoidal Grothendieck abelian category whose tensor product is additive
and preserves colimits in each variable, and let `R : C` be a commutative algebra object. The
category `Mod C R` of `R`-module objects is abelian
(`WeilConjectures.CategoryTheory.ModuleObjects.Abelian`)
and symmetric monoidal for the relative tensor product `⊗_R`
(`WeilConjectures.CategoryTheory.ModuleObjects.Braided`), so it has an ordinary derived category
```
D(Mod_R(C)) = DerivedCategory (Mod C R),
```
obtained by inverting the quasi-isomorphisms of complexes of `R`-modules. The tensor product of
complexes of `R`-modules is the totalization of the termwise relative tensor product, and the
*derived tensor product* `K ⊗ᴸ_R L` is computed by replacing `K` by a K-flat resolution. This is
the K-flat machinery of `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`,
which makes `DerivedCategory (Mod C R)` a monoidal category with tensor product `⊗ᴸ_R`
(`Mod.derivedMonoidalCategory`), such that the localization functor
`Mod C R`-complexes `⥤ D(Mod_R(C))` is lax monoidal.

## Sorried input

The K-flat machinery requires three properties of `Mod C R` which are not formalized yet and
are stated here as `sorry`ed instances:

* `Mod.monoidalClosed`: the relative tensor product is closed; the internal hom `Hom_R(M, N)` is
  the equalizer of the two maps `Hom(M, N) ⇉ Hom(R ⊗ M, N)` induced by the actions.
* `Mod.isGrothendieckAbelian`: `Mod C R` is Grothendieck abelian, since colimits and finite
  limits are computed in `C` and `R ⊗ G` is a separator for a separator `G` of `C`.
* `Mod.hasFunctorialFlatResolution`: every `R`-module object has a functorial resolution by
  flat `R`-module objects, e.g. by the free modules `R ⊗ -` on flat objects of `C`.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R : C} [MonObj R] [IsCommMonObj R]

/-- The relative tensor product of module objects is closed. -/
noncomputable instance monoidalClosed : MonoidalClosed (Mod C R) :=
  sorry

/-- The category of module objects over an algebra object in a Grothendieck abelian category
is Grothendieck abelian. -/
instance isGrothendieckAbelian [IsGrothendieckAbelian.{v} C] :
    IsGrothendieckAbelian.{v} (Mod C R) :=
  sorry

/-- Module objects admit functorial flat resolutions. -/
instance hasFunctorialFlatResolution [IsGrothendieckAbelian.{v} C] :
    Abelian.HasFunctorialFlatResolution (Mod C R) :=
  sorry

variable [IsGrothendieckAbelian.{v} C]

/-- Small colimits of module objects, from the Grothendieck abelian structure. -/
instance hasColimitsOfSize : HasColimitsOfSize.{0, 0} (Mod C R) :=
  hasColimitsOfSizeShrink _

/-- Complexes of module objects are monoidal for the total relative tensor product. -/
noncomputable instance monoidalCategoryCochainComplex :
    MonoidalCategory (CochainComplex (Mod C R) ℤ) :=
  inferInstance

/-- The derived category of module objects is monoidal for the derived tensor product
`K ⊗ᴸ_R L`. -/
noncomputable instance derivedMonoidalCategory :
    MonoidalCategory (DerivedCategory (Mod C R)) :=
  inferInstance

/-- The localization functor to the derived category of module objects is lax monoidal: the
derived tensor product receives a natural map from the tensor product of complexes. -/
noncomputable instance laxMonoidalQ : (DerivedCategory.Q (C := Mod C R)).LaxMonoidal :=
  inferInstance

/-- The derived tensor product of module objects is the left derived functor of the tensor
product of complexes with respect to quasi-isomorphisms: it is computed on K-flat
resolutions. -/
instance isLeftDerivedFunctor₂_curriedTensor :
    (curriedTensor (DerivedCategory (Mod C R))).IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Mod C R) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (Mod C R) (ComplexShape.up ℤ)) :=
  inferInstance

end CategoryTheory.Mod
