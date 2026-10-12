/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-! # The sections comparison restriction square

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-sections-comparison-restriction-square).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The comparison from termwise sections to derived sections respects restriction
along one morphism, before taking homology or changing a complex by an isomorphism.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-sections-comparison-restriction-square).

Proof: in the homotopy category the derived adjunction unit factors the image of
its underived unit followed by the direct-image derived unit. Apply derived
sections and use naturality of its unit to move the underived adjunction unit
past that unit. The composition right-derived unit factorization and the
underived isomorphism of pushforward sections with sections identify the result
with the underived restriction followed by the sections derived unit. Cancel
only the exact inverse-image localization comparison. Transport from homotopy
classes to complexes by the naturality of quotientCompQhIso. This gives the
square for every complex, including unbounded and zero complexes, without
assuming that either sections comparison is invertible. -/
theorem sectionsComparison_restriction_square {X Y : Scheme.{v}} (a : X ⟶ Y)
    (C : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :
  let restriction :=
    Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (upperStar AddCommGrpCat.{v + 1} a)
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} a).hom
  let toDerived (Z : Scheme.{v})
      (B : CochainComplex (Sheaf Z.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :=
    (DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
        (((Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
          (.up ℤ)).obj B) ≫
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj B) ≫
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
        ((DerivedCategory.quotientCompQhIso _).hom.app B)
  toDerived Y C ≫
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
      ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit.app
        (DerivedCategory.Q.obj C)) ≫
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      AddCommGrpCat.{v + 1} a).hom.app
        ((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategory.obj
          (DerivedCategory.Q.obj C)) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex restriction (.up ℤ)).app C) ≫
      toDerived X
        (((upperStar AddCommGrpCat.{v + 1} a).mapHomologicalComplex (.up ℤ)).obj C) ≫
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
        ((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategoryFactors.inv.app C) := by sorry

end AlgebraicGeometry.Etale
