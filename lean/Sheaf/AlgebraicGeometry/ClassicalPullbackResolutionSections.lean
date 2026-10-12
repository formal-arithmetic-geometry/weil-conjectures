/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-! # Pullback computed on a comparison of injective resolutions -/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale

/-- Classical derived base change is computed by the section map on resolutions.
Source: Stacks Project, Tag 01F8, equation 01F9; site version Tag 08J6.
(blueprint: lem-weil-pbc-classical-pullback-resolution-sections)

Proof: Use the chosen bounded below injective resolutions I of G and J of L G.
The homotopy hφ says that φ represents the identity of L G in the derived category,
because exact inverse image carries the augmentation of I to a quasi-isomorphism.
The derived base-change transformation is characterized by compatibility with the
derived-functor units. On I this compatibility identifies it with η on each term,
followed by the derived Γ' unit on L I. Naturality of that unit along φ, and its
invertibility on J, identifies this composite with Γ'(φ) following η(I).
Apply degree-q homology and the canonical comparisons computing classical right
derived functors by the chosen resolutions. These are precisely
isoRightDerivedObjCochainComplex, so the displayed equality follows. A different
lift gives the same homology map, since additive Γ' preserves homotopies.
No acyclicity of L I for Γ' is assumed. The unit on J supplies the replacement,
so the argument applies in degree zero, to zero sheaves, and to empty schemes. -/
theorem classicalPullback_resolution_sections
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (φ : ((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (.up ℤ)).obj
      (injectiveResolution G).cochainComplex ⟶
      (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g').obj G)).cochainComplex)
    (hφ : Nonempty (Homotopy
      (((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (.up ℤ)).map
        (injectiveResolution G).ι' ≫ φ)
      ((HomologicalComplex.singleMapHomologicalComplex
        (upperStar AddCommGrpCat.{u + 1} g') (.up ℤ) 0).hom.app G ≫
        (injectiveResolution ((upperStar AddCommGrpCat.{u + 1} g').obj G)).ι'))) :
    let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
    let Γ' := Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}
    let L := upperStar AddCommGrpCat.{u + 1} g'
    let η : Γ ⟶ L ⋙ Γ' :=
      (Functor.leftUnitor Γ).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit Γ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g').hom
    let b := (NatTrans.mapHomologicalComplex η (.up ℤ)).app
      (injectiveResolution G).cochainComplex ≫
        (Γ'.mapHomologicalComplex (.up ℤ)).map φ
    let e : Γ ⋙ 𝟭 _ ⟶ L ⋙ Γ' := (Functor.rightUnitor Γ).hom ≫ η
    ((injectiveResolution G).isoRightDerivedObjCochainComplex Γ q).hom ≫
        HomologicalComplex.homologyMap b (q : ℤ) =
      (Functor.rightDerivedBaseChange e q).app G ≫
        ((injectiveResolution (L.obj G)).isoRightDerivedObjCochainComplex Γ' q).hom := by
  sorry

end AlgebraicGeometry
