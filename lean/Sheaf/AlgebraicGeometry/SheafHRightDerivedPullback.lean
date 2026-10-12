/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # Ext compatibility with classical derived pullback

Source: Stacks Project, Tag 01F8 and equations 01F9 and 01FA.
(blueprint: lem-weil-pbc-sheafH-right-derived-pullback)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale

/-- There exist Ext/classical comparisons on the two schemes that identify the
classical right-derived section map with the Ext pullback map.

Source: Stacks Project, Tag 01F8 and equations 01F9 and 01FA.
(blueprint: lem-weil-pbc-sheafH-right-derived-pullback)

Proof: take the chosen injective resolutions of G and its inverse image. Apply exact
inverse image to the first augmentation and lift it into the second resolution.
Compute the classical derived base-change map by this lift. Compute Ext pullback
by applying inverse image to an Ext cocycle and precomposing the constant-sheaf
comparison. Evaluation at 1 in the constant integers identifies the two cochain
maps termwise. The sections identifications commute with differentials, so their
homology maps agree. The comparison theorem makes the result independent of the
chosen lift. The same formula holds in degree zero and for the zero sheaf. -/
theorem sheafHRightDerivedIso_pullback {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}
    let Γ' := Sheaf.Γ X'.smallEtaleTopology AddCommGrpCat.{u + 1}
    let L := upperStar AddCommGrpCat.{u + 1} g'
    let e : Γ ⋙ 𝟭 _ ⟶ L ⋙ Γ' :=
      (Functor.rightUnitor Γ).hom ≫ (Functor.leftUnitor Γ).inv ≫
        Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g').unit Γ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L (lowerStarCompGlobalSectionsIso AddCommGrpCat.{u + 1} g').hom
    ∃ (r : (Sheaf.functorH.{u + 1} X.smallEtaleTopology q).obj G ≅
        (Γ.rightDerived q).obj G)
      (r' : (Sheaf.functorH.{u + 1} X'.smallEtaleTopology q).obj (L.obj G) ≅
        (Γ'.rightDerived q).obj (L.obj G)),
      r.hom ≫ (Functor.rightDerivedBaseChange e q).app G =
        AddCommGrpCat.ofHom (cohomologyMap g' G q) ≫ r'.hom := by
  sorry

end AlgebraicGeometry
