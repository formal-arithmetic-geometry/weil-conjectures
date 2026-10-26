/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransportCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldUpperStarCompCoherence

/-!
# Coherence of the derived residue field transport with composition

The isomorphisms `ProEtale.residueFieldDerivedUpperStarIso : Lh^* ⋙ D(G) ≅ D(G) ⋙ Lh^*` are
compatible with the composition isomorphisms of derived pullbacks
(`ProEtale.residueFieldDerivedUpperStarIsoCompCoherenceAt`). This follows from the underived
compatibility `ProEtale.residueFieldModuleSheafUpperStarIso_compCoherence`, by applying
`D(-)` (`CategoryTheory.Functor.mapDerivedCategory_compCoherence`) and transporting along the
isomorphisms `L(h^*) ≅ D(h^*)` (`CategoryTheory.compCoherence_of_isoConj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing PadicAlgCl

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : FiniteIntermediateField ℓ)

/-- **The derived residue field transport is compatible with composition**: the isomorphisms
`residueFieldDerivedUpperStarIso` are compatible with the composition isomorphisms
`L(p ≫ q)^* ≅ Lq^* ⋙ Lp^*` of derived pullbacks. -/
theorem residueFieldDerivedUpperStarIsoCompCoherenceAt {X Y Z : Scheme.{u}} (p : X ⟶ Y)
    (q : Y ⟶ Z) : ResidueFieldDerivedUpperStarIsoCompCoherenceAt ℓ E p q := by
  refine compCoherence_of_isoConj
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) q)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) p)
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) (p ≫ q))
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) q)
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) p)
    (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) (p ≫ q))
    ((Functor.mapDerivedCategoryCompIso
        ((q)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)⟧)
        (residueFieldModuleSheaf Y ℓ E)).inv ≫
      (Functor.mapDerivedCategoryNatIso (residueFieldModuleSheafUpperStarIso ℓ E q)).hom ≫
      (Functor.mapDerivedCategoryCompIso (residueFieldModuleSheaf Z ℓ E)
        ((q)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])).hom)
    ((Functor.mapDerivedCategoryCompIso
        ((p)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)⟧)
        (residueFieldModuleSheaf X ℓ E)).inv ≫
      (Functor.mapDerivedCategoryNatIso (residueFieldModuleSheafUpperStarIso ℓ E p)).hom ≫
      (Functor.mapDerivedCategoryCompIso (residueFieldModuleSheaf Y ℓ E)
        ((p)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])).hom)
    ((Functor.mapDerivedCategoryCompIso
        ((p ≫ q)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)⟧)
        (residueFieldModuleSheaf X ℓ E)).inv ≫
      (Functor.mapDerivedCategoryNatIso (residueFieldModuleSheafUpperStarIso ℓ E (p ≫ q))).hom ≫
      (Functor.mapDerivedCategoryCompIso (residueFieldModuleSheaf Z ℓ E)
        ((p ≫ q)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])).hom)
    ((Functor.mapDerivedCategoryNatIso (CondensedRing.upperStarComp
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) p q)).hom ≫
      (Functor.mapDerivedCategoryCompIso
        ((q)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)⟧)
        ((p)^*⟦Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)⟧)).hom)
    ((Functor.mapDerivedCategoryNatIso (ProEtale.upperStarComp
      (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) p q)).hom ≫
      (Functor.mapDerivedCategoryCompIso
        ((q)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])
        ((p)^*[ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)])).hom)
    ?_ (residueFieldDerivedUpperStarIso ℓ E q) (residueFieldDerivedUpperStarIso ℓ E p)
    (residueFieldDerivedUpperStarIso ℓ E (p ≫ q)) ?_ ?_ ?_
    (CondensedRing.leftDerivedUpperStarComp
      (Profinite.continuousMapRingObj.{u} (integersResidueField ℓ E.1)) p q)
    (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} (ResidueFieldCoeff.{u} ℓ E)) p q)
    ?_ ?_
  · exact Functor.mapDerivedCategory_compCoherence' _ _ _ _ _
      (residueFieldModuleSheafUpperStarIso_compCoherence ℓ E p q)
  · exact isoWhiskerRight_trans_isoWhiskerLeft_hom_app _ _ _ _ _
  · exact isoWhiskerRight_trans_isoWhiskerLeft_hom_app _ _ _ _ _
  · exact isoWhiskerRight_trans_isoWhiskerLeft_hom_app _ _ _ _ _
  · exact trans_trans_isoWhiskerLeft_hom_app _ _ _ _ _ _
  · exact trans_trans_isoWhiskerLeft_hom_app _ _ _ _ _ _

end AlgebraicGeometry.ProEtale
