/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SheafHExtResolutionSectionsIso

/-! # Pullback computed on a comparison of injective resolutions -/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Scheme Etale

/-- Ext pullback is the homology map of the unit section map followed by the lift.
Source: Stacks Project, Tag 01F8, equations 01F9 and 01FA; site version Tag 08J6.
(blueprint: lem-weil-pbc-ext-pullback-resolution-sections)

Proof: Represent an Ext class by a cocycle from the constant integer sheaf into
its chosen injective resolution. Apply exact inverse image, precompose with the
constant-sheaf comparison, and postcompose with φ. The augmentation homotopy hφ
identifies this cocycle with the Ext pullback, using localization on the K-injective
target. Evaluation at 1 transforms the inverse-image cocycle into the section-unit
map η; evaluation commutes with φ by naturality of the constant-sheaf adjunction.
Thus the two maps of cocycles agree after evaluation. Coboundaries map to
coboundaries, so this equality descends to homology. The explicit extSectionsIso
is exactly the Ext/resolution equivalence followed by this evaluation map.
Degree zero has no incoming boundaries in the chosen resolutions; the same
argument works there, and for the zero sheaf and empty schemes. -/
theorem extPullback_resolution_sections
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
    (SheafPullbackResolution.extSectionsIso X G q).hom ≫
        HomologicalComplex.homologyMap b (q : ℤ) =
      AddCommGrpCat.ofHom (cohomologyMap g' G q) ≫
        (SheafPullbackResolution.extSectionsIso X' (L.obj G) q).hom := by
  sorry

end AlgebraicGeometry
