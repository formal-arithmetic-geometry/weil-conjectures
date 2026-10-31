/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleDerivedCohomologyPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-! # The module cohomology pullback and its adjunction-unit formula
Source: Stacks 01EZ, 01F8 and 08J6.
(blueprint: new-pur-module-cohomology-pullback-derived-unit). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The specified resolution-defined module pullback is the derived adjunction unit
followed by the canonical Leray comparison.
Source: Stacks 01EZ, 01F8 and 08J6.
(blueprint: new-pur-module-cohomology-pullback-derived-unit).

Proof: apply right-derived extensionality and precompose with the derived sections
unit on the homotopy category. The derived adjunction unit factorization and naturality
move the inverse-image factorization through Leray. The Leray unit equation reduces
the result to the ordinary section map. After the faithful homotopy inclusion the
remaining identity is the quotient of the defining equality of complex maps. -/
theorem moduleDerivedCohomologyPullback_eq_derivedUnit
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    moduleDerivedCohomologyPullback A f K =
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctorPlus.map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).derivedPlus.unit.app K) ≫
      (moduleLerayPlus A f).hom.app
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryPlus.obj K) := by
  unfold moduleDerivedCohomologyPullback moduleLerayPlus
  let L := upperStar (ModuleCat.{u + 1} A) f
  let R := lowerStar (ModuleCat.{u + 1} A) f
  let G := Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} A)
  let H := Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  have : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let e := lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} A) f
  let β := Functor.whiskerRight
      (NatTrans.mapHomotopyCategoryPlus
        ((Functor.leftUnitor G).inv ≫ Functor.whiskerRight adj.unit G ≫
          (Functor.associator L R G).hom ≫ Functor.whiskerLeft L e.hom))
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ H))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft L.mapHomotopyCategoryPlus H.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv H.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom
  let γ := (Functor.leftUnitor G.rightDerivedFunctorPlus).inv ≫
    Functor.whiskerRight adj.derivedPlus.unit G.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft L.mapDerivedCategoryPlus
      (Functor.rightDerivedFunctorPlusCompIso' R G e).hom
  suffices h : Functor.rightDerivedDesc _ G.rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso _) _ β = γ by
    simpa only [γ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.leftUnitor_inv_app, Category.id_comp, Category.assoc] using
      NatTrans.congr_app h K
  apply Functor.rightDerived_ext _ G.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso _)
  rw [Functor.rightDerived_fac]
  ext M : 2
  simp only [β, γ, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Category.id_comp, Category.comp_id]
  -- Compute the derived unit before using naturality of the Leray comparison.
  have hu : adj.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app M) ≫
        R.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj M) ≫
        R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app M) := by
    rw [← Category.assoc, ← adj.derivedPlus_unit_app_fac, Category.assoc,
      ← Functor.map_comp]
    simp
  rw [hu, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
  have hn := (Functor.rightDerivedFunctorPlusCompIso' R G e).hom.naturality
    (L.mapDerivedCategoryPlusFactorsh.inv.app M)
  simp only [Functor.comp_map] at hn
  dsimp only [Functor.comp_obj] at hn
  rw [hn]
  have hG := G.rightDerivedFunctorPlusUnit.naturality
    (adj.mapHomotopyCategoryPlus.unit.app M)
  simp only [Functor.comp_map] at hG
  rw [← reassoc_of% hG]
  rw [← Functor.rightDerivedFunctorPlusCompUnit_app_assoc]
  have hc := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac R G e)
    (L.mapHomotopyCategoryPlus.obj M)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc
  rw [reassoc_of% hc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  apply (HomotopyCategory.Plus.ι _).map_injective
  obtain ⟨M, hM⟩ := M
  obtain ⟨A, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  simp only [Functor.map_comp, NatTrans.ι_map_mapHomotopyCategoryPlus_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]
  rw [(HomotopyCategory.Plus.ι _).map_id, Category.comp_id]
  change _ = (G.mapHomotopyCategory _).map
      ((HomotopyCategory.Plus.ι _).map
        (adj.mapHomotopyCategoryPlus.unit.app ⟨_, hM⟩)) ≫ _
  rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app]
  change (HomotopyCategory.quotient _ _).map
      ((NatTrans.mapHomologicalComplex
        (G.leftUnitor.inv ≫ Functor.whiskerRight adj.unit G ≫
          (Functor.associator L R G).hom ≫ Functor.whiskerLeft L e.hom) _).app A) ≫
        𝟙 _ =
      (G.mapHomotopyCategory _).map
        ((adj.mapHomotopyCategory _).unit.app ((HomotopyCategory.quotient _ _).obj A)) ≫
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex e.hom _).app
          ((L.mapHomologicalComplex _).obj A))
  rw [Category.comp_id, Adjunction.mapHomotopyCategory_unit_app_quotient,
    Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  congr 1

end AlgebraicGeometry.Etale
