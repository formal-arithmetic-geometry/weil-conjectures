/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
public import Sheaf.AlgebraicGeometry.EtaleObjectSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

@[expose] public section
universe v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Naturality of object sections under an étale arrow.
Source: Stacks Project, Tags 03Q9 and 03S2; this is the pointwise
comparison after evaluation at the identity étale object.
Proof: expand the two comparison maps, use adjunction-unit naturality and
pullback hom_ext for the defining square.
(blueprint: lem-weil-pbc-object-sections-naturality) -/
theorem objectSections_naturality {X : Scheme.{v}} {U V : X.Etale}
    (b : U ⟶ V) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    F.obj.map b.op ≫ (etaleObjectSectionsIso U).hom.app F ≫
      (Sheaf.Γ U.left.smallEtaleTopology AddCommGrpCat.{v + 1}).map
        ((upperStarComp AddCommGrpCat.{v + 1} b.left V.hom U.hom b.w.symm).hom.app F) =
    (etaleObjectSectionsIso V).hom.app F ≫
      globalSectionsUpperStarMap AddCommGrpCat.{v + 1} b.left
        ((upperStar AddCommGrpCat.{v + 1} V.hom).obj F)  := by sorry

end AlgebraicGeometry.Etale
