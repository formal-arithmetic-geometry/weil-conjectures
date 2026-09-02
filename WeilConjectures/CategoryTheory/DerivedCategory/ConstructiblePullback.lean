/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!

# The derived pullback preserves bounded constructible complexes

For a morphism of schemes `g : Z ⟶ Y`, the pullback `g^*` on étale sheaves is exact, so
it induces a functor `(Etale.upperStar A g).mapDerivedCategory` between the derived
categories of étale sheaves. This file shows that this derived pullback sends `Dᵇc(Y, A)`
into `Dᵇc(Z, A)`, and restricts it to a functor
`Etale.DerivedCategoryBoundedConstructible.upperStar : Dᵇc(Y, A) ⥤ Dᵇc(Z, A)`.

The two halves of the statement are:

- boundedness is preserved because an exact functor is t-exact for the canonical
  t-structures (`CategoryTheory.Functor.bounded_mapDerivedCategory_obj`);
- constructibility of the homology sheaves is preserved because the homology of the
  derived pullback is the pullback of the homology
  (`CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso`) and the pullback of a
  constructible étale sheaf is constructible
  (`AlgebraicGeometry.Scheme.isConstructibleSheaf_upperStar`, stated with `sorry` in
  `WeilConjectures.ConstructibleSheaf.Pullback`).

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible.upperStar`: the derived
  pullback `Dᵇc(Y, A) ⥤ Dᵇc(Z, A)`, with the compatibilities
  `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible.upperStarCompιIso` with the
  inclusions into the derived categories and
  `AlgebraicGeometry.Etale.DerivedCategoryBoundedConstructible.toPlusUpperStarIso` with the
  derived pullback on the bounded below derived categories.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.bounded_upperStar_mapDerivedCategory_obj`: the
  derived pullback preserves boundedness.
- `AlgebraicGeometry.Etale.DerivedCategory.constructibleHomology_upperStar_mapDerivedCategory_obj`:
  the derived pullback preserves constructibility of the homology sheaves.
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_upperStar_mapDerivedCategory_obj`:
  the derived pullback preserves bounded constructible objects.

-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [IsGrothendieckAbelian.{u + 1} A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

namespace Etale.DerivedCategory

/-- The derived pullback along `g : Z ⟶ Y` preserves boundedness for the canonical
t-structures: the pullback on sheaves is exact, so the derived pullback is t-exact. -/
theorem bounded_upperStar_mapDerivedCategory_obj
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hM : _root_.DerivedCategory.TStructure.t.bounded M) :
    _root_.DerivedCategory.TStructure.t.bounded
      ((Etale.upperStar A g).mapDerivedCategory.obj M) :=
  (Etale.upperStar A g).bounded_mapDerivedCategory_obj hM

/-- The derived pullback along `g : Z ⟶ Y` preserves constructibility of the homology
sheaves: the homology of the derived pullback is the pullback of the homology, and the
pullback of a constructible étale sheaf is constructible. -/
theorem constructibleHomology_upperStar_mapDerivedCategory_obj
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hM : constructibleHomology A Y M) :
    constructibleHomology A Z ((Etale.upperStar A g).mapDerivedCategory.obj M) := fun n ↦ by
  have := hM n
  have e := ((Etale.upperStar A g).mapDerivedCategoryHomologyFunctorIso n).app M
  dsimp only [Functor.comp_obj] at e
  exact Scheme.IsConstructibleSheaf.of_iso e

/-- The derived pullback along `g : Z ⟶ Y` preserves bounded constructible objects,
combining `Etale.DerivedCategory.bounded_upperStar_mapDerivedCategory_obj` and
`Etale.DerivedCategory.constructibleHomology_upperStar_mapDerivedCategory_obj`. -/
theorem boundedConstructible_upperStar_mapDerivedCategory_obj
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hM : boundedConstructible A Y M) :
    boundedConstructible A Z ((Etale.upperStar A g).mapDerivedCategory.obj M) := by
  rw [boundedConstructible_iff] at hM ⊢
  exact ⟨bounded_upperStar_mapDerivedCategory_obj A g hM.1,
    constructibleHomology_upperStar_mapDerivedCategory_obj A g hM.2⟩

end Etale.DerivedCategory

namespace Etale.DerivedCategoryBoundedConstructible

/-- The derived pullback `Dᵇc(Y, A) ⥤ Dᵇc(Z, A)` along a morphism of schemes
`g : Z ⟶ Y`: the restriction of `(Etale.upperStar A g).mapDerivedCategory`, which is well
defined by
`Etale.DerivedCategory.boundedConstructible_upperStar_mapDerivedCategory_obj`. -/
noncomputable def upperStar : Dᵇc(Y, A) ⥤ Dᵇc(Z, A) :=
  (Etale.DerivedCategory.boundedConstructible A Z).lift
    (Etale.DerivedCategoryBoundedConstructible.ι A Y ⋙ (Etale.upperStar A g).mapDerivedCategory)
    fun K ↦ Etale.DerivedCategory.boundedConstructible_upperStar_mapDerivedCategory_obj A g
      K.property

/-- The derived pullback on `Dᵇc` is compatible with the inclusions into the derived
categories of étale sheaves: the square

```
                upperStar
     Dᵇc(Y, A) -----------> Dᵇc(Z, A)
        |                      |
        ι                      ι
        v                      v
       D(Y)   -------------->  D(Z)
              mapDerivedCategory
```

commutes up to the isomorphism given here (in fact definitionally). -/
noncomputable def upperStarCompιIso :
    upperStar A g ⋙ Etale.DerivedCategoryBoundedConstructible.ι A Z ≅
      Etale.DerivedCategoryBoundedConstructible.ι A Y ⋙
        (Etale.upperStar A g).mapDerivedCategory :=
  (Etale.DerivedCategory.boundedConstructible A Z).liftCompιIso _ _

/-- The derived pullback on `Dᵇc` is compatible with the derived pullback on the bounded
below derived categories: the square

```
                 upperStar
      Dᵇc(Y, A) -----------> Dᵇc(Z, A)
         |                      |
      toPlus                 toPlus
         v                      v
      D⁺(Y)  -------------->  D⁺(Z)
             mapDerivedCategoryPlus
```

commutes, both composites being restrictions of `(Etale.upperStar A g).mapDerivedCategory`
along the fully faithful inclusions of the derived categories. -/
noncomputable def toPlusUpperStarIso :
    toPlus A Y ⋙ (Etale.upperStar A g).mapDerivedCategoryPlus ≅
      upperStar A g ⋙ toPlus A Z :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (toPlus A Y)
        (Etale.upperStar A g).mapDerivedCategoryPlusCompatibility ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ObjectProperty.ιOfLECompιIso _)
        (Etale.upperStar A g).mapDerivedCategory ≪≫
      (upperStarCompιIso A g).symm ≪≫
      Functor.isoWhiskerLeft (upperStar A g) (ObjectProperty.ιOfLECompιIso _).symm ≪≫
      (Functor.associator _ _ _).symm)

end Etale.DerivedCategoryBoundedConstructible

end AlgebraicGeometry

end
