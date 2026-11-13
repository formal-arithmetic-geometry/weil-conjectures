/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisCanonicalData
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenCompositionNormalization
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisOpenRestrictionNormalization
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisUnderivedOpenCounitSquare

/-! # Counit computation for the canonical open composition comparison

Source: Stacks Project, Cohomology, Tags 08FE, 0D5T and 08BV.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

private theorem counit_transport
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {LX : C ⥤ C'} {RX : C' ⥤ C} {LY : D ⥤ D'} {RY : D' ⥤ D}
    (a : LX ⊣ RX) (b : LY ⊣ RY) (F : C ⥤ D) (G : C' ⥤ D')
    (α : F ⋙ LY ≅ LX ⋙ G) (β : RX ⋙ F ≅ G ⋙ RY)
    {A B : C'} (e : A ≅ B)
    (hA : LY.map (β.hom.app A) ≫ b.counit.app (G.obj A) =
      α.hom.app (RX.obj A) ≫ G.map (a.counit.app A)) :
    LY.map (β.hom.app B) ≫ b.counit.app (G.obj B) =
      α.hom.app (RX.obj B) ≫ G.map (a.counit.app B) := by
  let m : (RX ⋙ F) ⋙ LY ⟶ G :=
    Functor.whiskerRight β.hom LY ≫ (Functor.associator G RY LY).hom ≫
      Functor.whiskerLeft G b.counit ≫ G.rightUnitor.hom
  let n : (RX ⋙ F) ⋙ LY ⟶ G :=
    (Functor.associator RX F LY).hom ≫ Functor.whiskerLeft RX α.hom ≫
      (Functor.associator RX LX G).inv ≫ Functor.whiskerRight a.counit G ≫
      G.leftUnitor.hom
  have hi : m.app A = n.app A := by simpa [m, n] using hA
  have he : m.app B = n.app B := by
    apply (cancel_epi (((RX ⋙ F) ⋙ LY).map e.hom)).mp
    rw [m.naturality, n.naturality, hi]
  simpa [m, n] using he

set_option maxHeartbeats 700000 in
-- The diagram chase elaborates several specialized derived-category interfaces.
/-- On a K-injective complex on the inverse-image open, restricting the normalized
composition comparison and then applying the base-open counit agrees with first
using the open-restriction comparison and then pushing forward the source-open counit.
The parameter β is fixed by hβ to the canonical composite. Keeping it as an
explicit parameter avoids unfolding its right-derived choice in each projection.
This concerns an arbitrary complex on the open, not a restriction unit on X.

Source: Stacks Project, Tags 08FE (sectionwise restriction/direct-image identity),
0D5T (composition of derived direct images), and 08BV (open adjunction computation). -/
theorem schemeMVOpenComposition_counit_Q
    (X Y : Scheme.{u}) (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (U : Y.Opens)
    (β : schemeDerivedDirectImage (h ⁻¹ᵁ U).ι ⋙ schemeDerivedDirectImage h ≅
      schemeDerivedDirectImage (h ∣_ U) ⋙ schemeDerivedDirectImage U.ι)
    (hβ : β = (schemeMVDirectImageComposition (h ⁻¹ᵁ U).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h U).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ U) U.ι)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    (schemeMVDerivedRestriction Y U).map
        (β.hom.app (DerivedCategory.Q.obj I)) ≫
        (schemeMVAdjunction Y U).counit.app
          ((schemeDerivedDirectImage (h ∣_ U)).obj (DerivedCategory.Q.obj I)) =
      (schemeMVOpenRestrictionComparison h U).hom.app
          ((schemeDerivedDirectImage (h ⁻¹ᵁ U).ι).obj (DerivedCategory.Q.obj I)) ≫
        (schemeDerivedDirectImage (h ∣_ U)).map
          ((schemeMVAdjunction X (h ⁻¹ᵁ U)).counit.app (DerivedCategory.Q.obj I)) := by
  let RX := RingedSpace.moduleDirectImage (h ⁻¹ᵁ U).ι.toLRSHom.toShHom
  let F := RingedSpace.moduleDirectImage h.toLRSHom.toShHom
  let G := RingedSpace.moduleDirectImage (h ∣_ U).toLRSHom.toShHom
  let RY := RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom
  let LX := schemeOpenRestriction X (h ⁻¹ᵁ U)
  let LY := schemeOpenRestriction Y U
  let a₀ : LX ⊣ RX := schemeOpenModuleAdjunction X (h ⁻¹ᵁ U)
  let b₀ : LY ⊣ RY := schemeOpenModuleAdjunction Y U
  let a := schemeMVAdjunction X (h ⁻¹ᵁ U)
  let b := schemeMVAdjunction Y U
  let α := schemeMVOpenRestrictionComparison h U
  let K := (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I
  let RXh := RX.mapHomotopyCategory (ComplexShape.up ℤ)
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ)
  let Gh := G.mapHomotopyCategory (ComplexShape.up ℤ)
  let RYh := RY.mapHomotopyCategory (ComplexShape.up ℤ)
  let LXh := LX.mapHomotopyCategory (ComplexShape.up ℤ)
  let LYh := LY.mapHomotopyCategory (ComplexShape.up ℤ)
  let α₀ := (schemeMVHomotopyOpenRestriction h U).hom.app (RXh.obj K)
  let β₀ := (schemeMVHomotopyOpenComposition h U).hom.app K
  let εX := ((a₀.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app K)
  let εY := ((b₀.mapHomotopyCategory (ComplexShape.up ℤ)).counit.app (Gh.obj K))
  have ha : LX.mapDerivedCategory.map (RX.rightDerivedFunctorUnit.app K) ≫
      a.counit.app (DerivedCategory.Qh.obj K) =
    LX.mapDerivedCategoryFactorsh.hom.app (RXh.obj K) ≫ DerivedCategory.Qh.map εX := by
    exact (a₀.mapHomotopyCategory (ComplexShape.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      LX.mapDerivedCategoryFactorsh.hom RX.rightDerivedFunctorUnit K
  have hb : LY.mapDerivedCategory.map (RY.rightDerivedFunctorUnit.app (Gh.obj K)) ≫
      b.counit.app (DerivedCategory.Qh.obj (Gh.obj K)) =
    LY.mapDerivedCategoryFactorsh.hom.app (RYh.obj (Gh.obj K)) ≫
      DerivedCategory.Qh.map εY := by
    exact (b₀.mapHomotopyCategory (ComplexShape.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      LY.mapDerivedCategoryFactorsh.hom RY.rightDerivedFunctorUnit (Gh.obj K)
  have hα := schemeMVOpenRestriction_unit_normalization X Y h U (RXh.obj K)
  change LY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app (RXh.obj K)) ≫
      α.hom.app (DerivedCategory.Qh.obj (RXh.obj K)) ≫
      G.rightDerivedFunctor.map (LX.mapDerivedCategoryFactorsh.hom.app (RXh.obj K)) =
    LY.mapDerivedCategoryFactorsh.hom.app (Fh.obj (RXh.obj K)) ≫
      DerivedCategory.Qh.map α₀ ≫
      G.rightDerivedFunctorUnit.app (LXh.obj (RXh.obj K)) at hα
  have hα' : LY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app (RXh.obj K)) ≫
      α.hom.app (DerivedCategory.Qh.obj (RXh.obj K)) =
    LY.mapDerivedCategoryFactorsh.hom.app (Fh.obj (RXh.obj K)) ≫
      DerivedCategory.Qh.map α₀ ≫
      G.rightDerivedFunctorUnit.app (LXh.obj (RXh.obj K)) ≫
      G.rightDerivedFunctor.map (LX.mapDerivedCategoryFactorsh.inv.app (RXh.obj K)) := by
    have hid : G.rightDerivedFunctor.map
        (LX.mapDerivedCategoryFactorsh.hom.app (RXh.obj K)) ≫
        G.rightDerivedFunctor.map (LX.mapDerivedCategoryFactorsh.inv.app (RXh.obj K)) =
        𝟙 _ := (G.rightDerivedFunctor.mapIso
          (LX.mapDerivedCategoryFactorsh.app (RXh.obj K))).hom_inv_id
    have he := congrArg (fun f ↦ f ≫ G.rightDerivedFunctor.map
      (LX.mapDerivedCategoryFactorsh.inv.app (RXh.obj K))) hα
    simp only [Category.assoc, hid] at he
    erw [Category.comp_id] at he
    exact he
  have hβ' := schemeMVOpenComposition_unit_normalization X Y h U β hβ K
  change F.rightDerivedFunctorUnit.app (RXh.obj K) ≫
      F.rightDerivedFunctor.map (RX.rightDerivedFunctorUnit.app K) ≫
      β.hom.app (DerivedCategory.Qh.obj K) =
    DerivedCategory.Qh.map β₀ ≫ RY.rightDerivedFunctorUnit.app (Gh.obj K) ≫
      RY.rightDerivedFunctor.map (G.rightDerivedFunctorUnit.app K) at hβ'
  have h₀ := schemeMVUnderivedOpenCounit_square X Y h U K
  change LYh.map β₀ ≫ εY = α₀ ≫ Gh.map εX at h₀
  have : RX.PreservesKInjectiveComplexes := a₀.preservesKInjectiveComplexes
  have hs : IsIso (F.rightDerivedFunctorUnit.app (RXh.obj K)) := by
    have : CochainComplex.IsKInjective
        ((RX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := inferInstance
    change IsIso (F.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((RX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))
    infer_instance
  have ht : IsIso (RX.rightDerivedFunctorUnit.app K) := by
    dsimp [K]
    infer_instance
  let s := LY.mapDerivedCategory.map
    (F.rightDerivedFunctorUnit.app (RXh.obj K) ≫
      F.rightDerivedFunctor.map (RX.rightDerivedFunctorUnit.app K))
  have hs' : IsIso s := by dsimp [s]; infer_instance
  have hc : LY.mapDerivedCategory.map (β.hom.app (DerivedCategory.Qh.obj K)) ≫
      b.counit.app (G.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)) =
    α.hom.app (RX.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)) ≫
      G.rightDerivedFunctor.map (a.counit.app (DerivedCategory.Qh.obj K)) := by
    apply (cancel_epi s).mp
    have hl : s ≫ LY.mapDerivedCategory.map (β.hom.app (DerivedCategory.Qh.obj K)) ≫
        b.counit.app (G.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)) =
      LY.mapDerivedCategoryFactorsh.hom.app (Fh.obj (RXh.obj K)) ≫
        DerivedCategory.Qh.map (LYh.map β₀ ≫ εY) ≫
        G.rightDerivedFunctorUnit.app K := by
      dsimp only [s]
      rw [← Functor.map_comp_assoc]
      simp only [Category.assoc]
      rw [hβ']
      simp only [Functor.map_comp, Category.assoc]
      have hn : LY.mapDerivedCategory.map
          (RY.rightDerivedFunctor.map (G.rightDerivedFunctorUnit.app K)) ≫
          b.counit.app (G.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)) =
        b.counit.app (DerivedCategory.Qh.obj (Gh.obj K)) ≫
          G.rightDerivedFunctorUnit.app K :=
        b.counit.naturality (G.rightDerivedFunctorUnit.app K)
      rw [hn]
      rw [← Category.assoc (LY.mapDerivedCategory.map
        (RY.rightDerivedFunctorUnit.app (Gh.obj K))), hb]
      have hf : LY.mapDerivedCategory.map (DerivedCategory.Qh.map β₀) ≫
          LY.mapDerivedCategoryFactorsh.hom.app (RYh.obj (Gh.obj K)) =
        LY.mapDerivedCategoryFactorsh.hom.app (Fh.obj (RXh.obj K)) ≫
          DerivedCategory.Qh.map (LYh.map β₀) :=
        LY.mapDerivedCategoryFactorsh.hom.naturality β₀
      simp only [Category.assoc]
      rw [reassoc_of% hf]
    have hr : s ≫ α.hom.app (RX.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)) ≫
        G.rightDerivedFunctor.map (a.counit.app (DerivedCategory.Qh.obj K)) =
      LY.mapDerivedCategoryFactorsh.hom.app (Fh.obj (RXh.obj K)) ≫
        DerivedCategory.Qh.map (α₀ ≫ Gh.map εX) ≫ G.rightDerivedFunctorUnit.app K := by
      dsimp only [s]
      simp only [Functor.map_comp, Category.assoc]
      have hn : LY.mapDerivedCategory.map
          (F.rightDerivedFunctor.map (RX.rightDerivedFunctorUnit.app K)) ≫
          α.hom.app (RX.rightDerivedFunctor.obj (DerivedCategory.Qh.obj K)) =
        α.hom.app (DerivedCategory.Qh.obj (RXh.obj K)) ≫
          G.rightDerivedFunctor.map (LX.mapDerivedCategory.map
            (RX.rightDerivedFunctorUnit.app K)) :=
        α.hom.naturality (RX.rightDerivedFunctorUnit.app K)
      rw [reassoc_of% hn]
      simp only [Functor.comp_obj]
      rw [← Category.assoc, hα']
      simp only [Category.assoc, ← Functor.map_comp]
      rw [ha]
      simp only [Iso.inv_hom_id_app_assoc]
      have hg : DerivedCategory.Qh.map (Gh.map εX) ≫
          G.rightDerivedFunctorUnit.app K =
        G.rightDerivedFunctorUnit.app (LXh.obj (RXh.obj K)) ≫
          G.rightDerivedFunctor.map (DerivedCategory.Qh.map εX) :=
        G.rightDerivedFunctorUnit.naturality εX
      rw [← hg]
    rw [hl, hr, h₀]
  exact counit_transport a b F.rightDerivedFunctor G.rightDerivedFunctor α β
    ((DerivedCategory.quotientCompQhIso _).app I) hc

end AlgebraicGeometry
