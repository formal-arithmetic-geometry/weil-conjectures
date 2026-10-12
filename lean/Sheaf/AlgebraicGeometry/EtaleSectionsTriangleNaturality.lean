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

/-! # Naturality of the termwise-to-derived sections comparison

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-sections-comparison-triangle-naturality).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The sections comparison commutes with restriction along any triangle of schemes.
The local lets spell out the existing comparison maps without importing their defining
module, which uses this theorem. No injectivity or boundedness is required for this square.

Source: Stacks Project, Tag 03Q9, final paragraph, the maps from each neighbourhood
complex to the limit complex and their realization on cohomology.
(blueprint: lem-weil-pbc-sections-comparison-triangle-naturality).

Proof: first work in the homotopy category. Write F for inverse image along a,
R for direct image, G for sections on Y and H for sections on X. The derived
adjunction unit satisfies Q(eta) followed by the derived-direct-image unit equals
eta_D followed by R(F's exact-localization comparison). Naturality of the
right-derived G unit moves Q(eta) past that unit. The defining factorization of
the derived composition isomorphism, followed by the derived isomorphism RG = H,
identifies the resulting composite with Q of the underived sections restriction
followed by H's right-derived unit. Cancel F's localization comparison to get the
restriction square. Pass from the homotopy category to the derived category using
the quotientCompQhIso naturality squares. Next apply the square to g applied
termwise to J, and use naturality of H's derived unit for the chain isomorphism
from a applied to g applied to J to h applied to J. Compatibility of
mapDerivedCategoryNatIso and mapDerivedCategoryCompIso with their localization
factorizations identifies this isomorphism with the displayed derived composition
map. Finally move q.inv through the derived adjunction unit, Leray isomorphism,
and inverse-image composition isomorphism by their naturality, and apply H^n.
This proves the square without inverting any sections unit. It applies also to
nonetale a, negative n, zero complexes, and empty schemes. -/
theorem sectionsComparison_triangle_naturality {X Y T : Scheme.{v}}
    (a : X ⟶ Y) (g : Y ⟶ T) (h : X ⟶ T) (hh : h = a ≫ g)
    {K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1})}
    (J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ)
    (q : K ≅ DerivedCategory.Q.obj J) (n : ℤ) :
  let restriction :=
    Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (upperStar AddCommGrpCat.{v + 1} a)
          (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1} a).hom
  let toDerived (Y : Scheme.{v})
      (C : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) ℤ) :=
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        ((DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
            (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
              (.up ℤ)).obj C) ≫
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ _).obj C) ≫
          (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
            ((DerivedCategory.quotientCompQhIso _).hom.app C))
  let comparison (Y : Scheme.{v}) (g : Y ⟶ T) :=
    toDerived Y
          (((upperStar AddCommGrpCat.{v + 1} g).mapHomologicalComplex (.up ℤ)).obj J) ≫
        (cohomology AddCommGrpCat.{v + 1} Y n).map
          (((upperStar AddCommGrpCat.{v + 1} g).mapDerivedCategoryFactors.inv.app J) ≫
            (upperStar AddCommGrpCat.{v + 1} g).mapDerivedCategory.map q.inv)
  let chainRestriction :=
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
        (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex restriction (.up ℤ)).app
              (((upperStar AddCommGrpCat.{v + 1} g).mapHomologicalComplex (.up ℤ)).obj J) ≫
            ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
              (.up ℤ)).map ((NatIso.mapHomologicalComplex
                (upperStarComp AddCommGrpCat.{v + 1} a g h hh) (.up ℤ)).inv.app J)))
  comparison Y g ≫
    (cohomology AddCommGrpCat.{v + 1} Y n).map
      ((mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} a).unit.app
        ((upperStar AddCommGrpCat.{v + 1} g).mapDerivedCategory.obj K)) ≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{v + 1} a).hom.app
          ((upperStar AddCommGrpCat.{v + 1} a).mapDerivedCategory.obj
            ((upperStar AddCommGrpCat.{v + 1} g).mapDerivedCategory.obj K))) ≫
    (cohomology AddCommGrpCat.{v + 1} X n).map
      ((Functor.mapDerivedCategoryNatIso
        (upperStarComp AddCommGrpCat.{v + 1} a g h hh) ≪≫
          Functor.mapDerivedCategoryCompIso
            (upperStar AddCommGrpCat.{v + 1} g)
            (upperStar AddCommGrpCat.{v + 1} a)).inv.app K) =
    chainRestriction ≫ comparison X h := by sorry

end AlgebraicGeometry.Etale
