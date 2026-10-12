/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-! # Composition of the unbounded Leray comparison -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The canonical Leray comparisons associate with the derived direct-image comparison.
Source: Stacks Project, Tags 05T2, 015M and 03CB.
(blueprint: lem-weil-pbc-derived-leray-composition).

Proof: The underived direct-image comparison and terminal-section comparisons associate.
Both composites evaluate a sheaf on the same composite base change of the terminal object;
the two base-change isomorphisms coincide by the uniqueness of the pullback isomorphism
commuting with the projections. Apply the right-derived comparison construction to this
equality. The composition comparison for direct images agrees with the mate defining
rightDerivedLowerStarComp: the underived comparison is the mate of upperStarComp, and the
right-derived comparison preserves this conjugacy for exact left adjoints. Each direct
image preserves K-injective complexes, being right adjoint to exact inverse image. Thus
iterated direct image followed by global sections computes the composite right-derived
functor. Precomposing either displayed transformation with its composite derived unit gives
the localization of the same underived terminal-section comparison. The universal property
of this composite right-derived functor identifies the transformations; evaluate at M.
This works on the unbounded category, using K-injectives, with no boundedness hypothesis. -/
theorem derivedLeray_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (M : DerivedCategory (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
      ((rightDerivedLowerStarComp AddCommGrpCat.{u + 1} g f).hom.app M) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{u + 1} (g ≫ f)).hom.app M =
    (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      AddCommGrpCat.{u + 1} f).hom.app
        ((lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.obj M) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
        AddCommGrpCat.{u + 1} g).hom.app M := by sorry

end AlgebraicGeometry.Etale
