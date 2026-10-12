/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import Sheaf.AlgebraicGeometry.DerivedCategories

/-! # Lifting a commuting cube to bounded below right derived functors

Source: Stacks Project, Tag 0736, uniqueness of right derived transformations.
(blueprint: lem-weil-pbc-right-derived-plus-cube)
-/

@[expose] public section

open CategoryTheory Limits
open scoped CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {B C B' C' B₀ C₀ B₀' C₀' : Type*}
  [Category* B] [Category* C] [Category* B'] [Category* C']
  [Category* B₀] [Category* C₀] [Category* B₀'] [Category* C₀']
  [Abelian B] [Abelian C] [Abelian B'] [Abelian C']
  [Abelian B₀] [Abelian C₀] [Abelian B₀'] [Abelian C₀']
  [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory B'] [HasDerivedCategory C']
  [HasDerivedCategory B₀] [HasDerivedCategory C₀]
  [HasDerivedCategory B₀'] [HasDerivedCategory C₀']
  [EnoughInjectives B] [EnoughInjectives B']
  [EnoughInjectives B₀] [EnoughInjectives B₀']
  (G : B ⥤ C) (H : B' ⥤ C') (G₀ : B₀ ⥤ C₀) (H₀ : B₀' ⥤ C₀')
  (P : B ⥤ B') (Q : C ⥤ C') (P₀ : B₀ ⥤ B₀') (Q₀ : C₀ ⥤ C₀')
  (U : B ⥤ B₀) (V : C ⥤ C₀) (U' : B' ⥤ B₀') (V' : C' ⥤ C₀')
  [G.Additive] [H.Additive] [G₀.Additive] [H₀.Additive]
  [P.Additive] [Q.Additive] [P₀.Additive] [Q₀.Additive]
  [U.Additive] [V.Additive] [U'.Additive] [V'.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
  [PreservesFiniteLimits P₀] [PreservesFiniteColimits P₀]
  [PreservesFiniteLimits Q₀] [PreservesFiniteColimits Q₀]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  [PreservesFiniteLimits U'] [PreservesFiniteColimits U']
  [PreservesFiniteLimits V'] [PreservesFiniteColimits V']

/-- A commuting cube with exact transverse edges remains commuting after right derivation.

Source: Stacks Project, Tag 0736, construction and uniqueness of derived transformations.
(blueprint: lem-weil-pbc-right-derived-plus-cube)

Proof: Compare the two natural transformations from RG followed by DQ and DV'.
Precompose with the unit of RG, whiskered by DQ and DV'. The factorization
identity for each rightDerivedFunctorPlusBaseChange replaces its derived
comparison by the corresponding termwise map followed by the target derived
unit. The factorization identities for mapDerivedCategoryPlusCompIso and
mapDerivedCategoryPlusNatIso replace the two exact comparison isomorphisms
by their maps on homotopy categories. Naturality of the unit of RH₀ moves
these comparison maps past the final unit. The two resulting composites are
the images of the assumed underived cube equation, followed by the same
unit of RH₀. They are equal. The composite RG ⋙ DQ ⋙ DV' is an absolute
right derived functor, so rightDerived_ext proves equality of the natural
transformations. Evaluate at K. This uses no preservation of injectives by
U or U', and does not require invertibility of a or b. -/
theorem rightDerivedFunctorPlusBaseChange_cube
    (e : G ⋙ Q ⟶ P ⋙ H) (e₀ : G₀ ⋙ Q₀ ⟶ P₀ ⋙ H₀)
    (a : G ⋙ V ⟶ U ⋙ G₀) (b : H ⋙ V' ⟶ U' ⋙ H₀)
    (c : V ⋙ Q₀ ≅ Q ⋙ V') (d : U ⋙ P₀ ≅ P ⋙ U')
    (h : ∀ F : B, V'.map (e.app F) ≫ b.app (P.obj F) ≫ H₀.map (d.inv.app F) =
      c.inv.app (G.obj F) ≫ Q₀.map (a.app F) ≫ e₀.app (U.obj F))
    (K : DerivedCategory.Plus B) :
    D+(V').map ((rightDerivedFunctorPlusBaseChange e).app K) ≫
        (rightDerivedFunctorPlusBaseChange b).app (D+(P).obj K) ≫
        R+(H₀).map (((mapDerivedCategoryPlusCompIso U P₀).symm ≪≫
          mapDerivedCategoryPlusNatIso d ≪≫ mapDerivedCategoryPlusCompIso P U').inv.app K) =
      ((mapDerivedCategoryPlusCompIso V Q₀).symm ≪≫
        mapDerivedCategoryPlusNatIso c ≪≫ mapDerivedCategoryPlusCompIso Q V').inv.app
          (R+(G).obj K) ≫
        D+(Q₀).map ((rightDerivedFunctorPlusBaseChange a).app K) ≫
        (rightDerivedFunctorPlusBaseChange e₀).app (D+(U).obj K) := by sorry

end CategoryTheory.Functor
