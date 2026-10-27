/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(blueprint: lem-z8-ordinary-finite-single-unit-normalization).

# Normalized single-unit composition equations
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local implicit_reducible] constantSheaf
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
attribute [local implicit_reducible] sheafMonoidalCategory sheafBraidedCategory
attribute [local instance 21000] sheafBraidedCategory
attribute [local instance 20000] SymmetricCategory.toBraidedCategory
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar

/-- The canonical single-object unit comparison with ordinary coefficient endpoints. -/
def ordinaryFiniteSingleUnitIso (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    ordinaryFiniteUnit A X ≅ 𝟙_ (DerivedCategoryModule A X) :=
  singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X

/-- The cached comparison is the existing canonical single-object comparison. -/
theorem ordinaryFiniteSingleUnitIso_eq (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    ordinaryFiniteSingleUnitIso A X = singleFunctorObjUnitIso (ModuleCat.{u + 1} A) X := rfl

/-- Associativity before the single-object unit comparison, with normalized endpoints. -/
theorem ordinaryFiniteSingleUnit_assoc (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {K L : DerivedCategoryModule A X} (f : K ⟶ L) (g : L ⟶ ordinaryFiniteUnit A X) :
    (f ≫ g) ≫ (ordinaryFiniteSingleUnitIso A X).hom =
      f ≫ g ≫ (ordinaryFiniteSingleUnitIso A X).hom := by
  rw [Category.assoc]

end AlgebraicGeometry.Etale
