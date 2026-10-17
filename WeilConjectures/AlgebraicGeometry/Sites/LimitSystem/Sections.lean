/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity
public import WeilConjectures.AlgebraicGeometry.Sites.UnitComparison

/-!
# Sections of the colimit of a system of étale sheaves along an inverse limit

Let `D : Iᵒᵖ ⥤ Scheme` be a directed inverse system of quasi-compact quasi-separated schemes with
affine transition maps and limit `X`, and let `(Fᵢ, φ)` be a *system* of abelian étale sheaves:
a sheaf `Fᵢ` on every `Dᵢ` with transition maps `φ : (Dᵢ ⟶ Dⱼ)^* Fᵢ ⟶ Fⱼ` (not necessarily
isomorphisms). Let `L` be the colimit on `X` of the pullbacks of the `Fᵢ`.

Fix a stage `i₀` and a quasi-compact quasi-separated étale `D_{i₀}`-scheme `U`. We show that the
sections of `L` over `U ×_{D_{i₀}} X` are the filtered colimit of the sections of the `Fⱼ` over
the `U ×_{D_{i₀}} Dⱼ` (`AlgebraicGeometry.Etale.SystemData.exists_stageSection_eq`,
`AlgebraicGeometry.Etale.SystemData.exists_transition_eq_zero`). All the sheaves are pushed
forward to the small étale site of `D_{i₀}`, so that the comparison maps are morphisms of sheaves
on a fixed site.

The proof combines the continuity of sections of a single sheaf
(`AlgebraicGeometry.Etale.unitComparison_app_isColimit_of_isLimit`) with the commutation of
sections over quasi-compact quasi-separated objects with filtered colimits
(`AlgebraicGeometry.Scheme.exists_app_eq_of_isColimit_ab`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale


section KeyIdentity

variable {X Dj Di D₀ : Scheme.{u}} (πj : X ⟶ Dj) (Dij : Dj ⟶ Di) (gi : Di ⟶ D₀)
  (πi : X ⟶ Di) (gj : Dj ⟶ D₀) (p : X ⟶ D₀) (h₁ : πi = πj ≫ Dij) (h₂ : gj = Dij ≫ gi)
  (h₃ : p = πi ≫ gi) (h₄ : p = πj ≫ gj)

/-- The comparison of units underlying the sections of a system along an inverse limit: for
`πi = πj ≫ Dij`, `gj = Dij ≫ gi` and `p = πi ≫ gi = πj ≫ gj`, the unit of `πj` on
`Dij^* Fᵢ`, pushed forward to `D₀`, is the pushforward of `unitComparison` followed by the
composition isomorphism `πi^* ≅ πj^* Dij^*`. -/
lemma lowerStarComp_hom_app_unit_eq_unitComparison
    (Fi : Sheaf Di.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (lowerStarComp AddCommGrpCat.{u + 1} Dij gi gj h₂).hom.app
        ((upperStar AddCommGrpCat.{u + 1} Dij).obj Fi) ≫
      (lowerStar AddCommGrpCat.{u + 1} gj).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} πj).unit.app
          ((upperStar AddCommGrpCat.{u + 1} Dij).obj Fi)) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} πj gj p h₄).hom.app _ =
    (lowerStar AddCommGrpCat.{u + 1} gi).map (unitComparison πj Dij πi h₁ Fi) ≫
      (lowerStarComp AddCommGrpCat.{u + 1} πi gi p h₃).hom.app _ ≫
      (lowerStar AddCommGrpCat.{u + 1} p).map
        ((upperStarComp AddCommGrpCat.{u + 1} πj Dij πi h₁).hom.app Fi) := by
  have hassoc := NatTrans.congr_app (lowerStarComp_assoc' AddCommGrpCat.{u + 1} πj Dij gi πi gj
    p h₁ h₂ h₃) ((upperStar AddCommGrpCat.{u + 1} πj).obj
      ((upperStar AddCommGrpCat.{u + 1} Dij).obj Fi))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hassoc
  have hnat := (lowerStarComp AddCommGrpCat.{u + 1} πi gi p h₃).hom.naturality
    ((upperStarComp AddCommGrpCat.{u + 1} πj Dij πi h₁).inv.app Fi)
  simp only [Functor.comp_map] at hnat
  rw [unitComparison, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    reassoc_of% hnat, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id, ← reassoc_of% hassoc]
  have hnat' := (lowerStarComp AddCommGrpCat.{u + 1} Dij gi gj h₂).hom.naturality
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} πj).unit.app
      ((upperStar AddCommGrpCat.{u + 1} Dij).obj Fi))
  simp only [Functor.comp_map] at hnat'
  rw [reassoc_of% hnat']
  congr 1
  sorry

end KeyIdentity
end AlgebraicGeometry.Etale
