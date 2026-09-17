/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize

/-!

# The derived category of a monoidal Grothendieck abelian category is monoidal

The K-flat machinery migrated from mathlib PR #25848 equips the derived category
`DerivedCategory A` with a monoidal structure as soon as the localization functor
`Qh : K(A) ⥤ D(A)` satisfies `Functor.HasDerivedMonoidalCategory` with respect to
quasi-isomorphisms; see `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`.

Verifying that hypothesis by hand at every use site is impractical, because it is phrased in
terms of the derived bifunctor, trifunctors and quadrifunctor of the tensor product. This
file packages it once and for all as an instance, deduced from conditions that are
checkable in practice:

* `A` is a monoidal Grothendieck abelian category (`IsGrothendieckAbelian`,
  `MonoidalCategory`, `MonoidalPreadditive`, `BraidedCategory`);
* the tensor product is closed (`MonoidalClosed`), so that `- ⊗ X` and `X ⊗ -` are left
  adjoints and hence preserve all colimits;
* `A` admits functorial flat resolutions (`Abelian.HasFunctorialFlatResolution`).

Together these give the K-flat left derivability structure, which is what
`CategoryTheory.MorphismProperty.kFlat_derivesMonoidal` turns into
`Functor.HasDerivedMonoidalCategory`.

## Main results

- `DerivedCategory.hasDerivedMonoidalCategory` : the instance
  `Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso A (.up ℤ))`, from which
  `MonoidalCategory (DerivedCategory A)` follows by
  `WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal`.

## TODO

The proof is currently `sorry`. It should go through the K-flat route already available in
`WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`: the hypotheses above give
`(HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure`
(this part is already proved, in
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat`), and the instance
`CategoryTheory.MorphismProperty.instHasDerivedMonoidalCategory` then applies. What remains
is to discharge the ambient graded-object and colimit side conditions from
`MonoidalClosed A` and `IsGrothendieckAbelian A` rather than assuming them.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace DerivedCategory

variable (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{w} A]

instance (X₁ X₂ : GradedObject ℤ A) : X₁.HasTensor X₂ := inferInstance

noncomputable instance : MonoidalCategory (HomotopyCategory A (ComplexShape.up ℤ)) :=
  have (X₁ X₂ : GradedObject ℤ A) : X₁.HasTensor X₂ := inferInstance
  inferInstance

/-- For a monoidal closed Grothendieck abelian category `A` admitting functorial flat
resolutions, the localization functor `Qh : K(A) ⥤ D(A)` admits a derived monoidal
structure with respect to quasi-isomorphisms. Consequently `DerivedCategory A` is monoidal,
with tensor product the derived tensor product `- ⊗ᴸ -`. -/
instance (priority := 2000) hasDerivedMonoidalCategory [Abelian.HasFunctorialFlatResolution A] :
    Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  sorry

end DerivedCategory
