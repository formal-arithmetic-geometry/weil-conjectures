/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenDirectImageUnit
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction

import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization
import all WeilConjectures.AlgebraicGeometry.SingleComplexOpenHomotopyTensorCounit
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenUnderivedTensorMate

/-! # The open pullback square evaluated on a direct-image representative

## References

* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem finish_counit
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : D ⥤ E) (L : C ⥤ E) (T : C ⥤ D) (ε : L ⟶ T ⋙ Q)
    {A B : C} {Z : D} (e : A ⟶ B) (v : T.obj B ⟶ Z)
    (k : T.obj A ⟶ Z) (lhs : L.obj A ⟶ Q.obj Z)
    (h : lhs = ε.app A ≫ Q.map k) (hm : k = T.map e ≫ v) :
    lhs = L.map e ≫ ε.app B ≫ Q.map v := by
  rw [h, hm, Q.map_comp]
  have hn := ε.naturality e
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc]

private theorem cancel_representative_tail
    {C : Type*} [Category C] {A B D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (e : E ≅ H)
    (x : A ⟶ F) (y : F ⟶ G) (z : G ⟶ H)
    (h : a ≫ b ≫ c ≫ e.hom = x ≫ y ≫ z) :
    a ≫ b ≫ c = x ≫ y ≫ z ≫ e.inv := by
  have h' := congrArg (fun k ↦ k ≫ e.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h'

set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The representative identity after cancelling the open-restriction factorization.

This is the mate calculation before composing with the inverse factorization
isomorphism. It is strictly weaker than the displayed representative identity,
and is isolated so that the remaining categorical cancellation is explicit. -/
theorem singleComplexOpen_pullback_counit_representative_postcomp
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ := (Classical.choose exists_derivedPullbackComposition) (f ∣_ V)
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let c := @singleComplexOpenPinnedComposition.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback (f ∣_ V)).map
        (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          rY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I))) ≪≫
        (c (f ∣_ V) V.ι).app ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)))).hom ≫
      rX.mapDerivedCategory.map ((a f).counit.app (DerivedCategory.Qh.obj I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I =
    (derivedPullback (f ∣_ V)).map (DerivedCategory.Qh.map
      ((singleComplexOpenHomotopyDirectImageIso f V).hom.app I)) ≫
      (ε (f ∣_ V)).app ((F₀.mapHomotopyCategory (.up ℤ)).obj
        ((rX.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ∣_ V)))
          |>.mapHomotopyCategory (.up ℤ)).counit.app
          ((rX.mapHomotopyCategory (.up ℤ)).obj I)) := by
  classical
  let _ : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
    (Scheme.Modules.tensorPullback k).Additive :=
    @Classical.choose _ _ exists_derivedPullbackComposition
  have h := singleComplexOpen_pullback_counit_homotopy_factorization f V I
  have hm := singleComplexOpen_homotopy_tensor_counit f V I
  exact finish_counit DerivedCategory.Qh
    (DerivedCategory.Qh ⋙ derivedPullback (f ∣_ V))
    ((Scheme.Modules.tensorPullback (f ∣_ V)).mapHomotopyCategory (.up ℤ))
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) (f ∣_ V))
    ((singleComplexOpenHomotopyDirectImageIso f V).hom.app I) _ _ _ h hm

set_option cleanup.letToHave false in
/-- The pullback-composition route, after the direct-image unit, is the localization
of the sectionwise counit. This calculation does not use the derived open direct-image
comparison: it compares the explicit pullback factors with the underived adjunction. -/
theorem singleComplexOpen_pullback_counit_representative
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ := (Classical.choose exists_derivedPullbackComposition) (f ∣_ V)
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let c := @singleComplexOpenPinnedComposition.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback (f ∣_ V)).map
        (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          rY.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I))) ≪≫
        (c (f ∣_ V) V.ι).app ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            ((schemeDerivedDirectImage f).obj (DerivedCategory.Qh.obj I)))).hom ≫
      rX.mapDerivedCategory.map ((a f).counit.app (DerivedCategory.Qh.obj I)) =
    (derivedPullback (f ∣_ V)).map
        (DerivedCategory.Qh.map ((singleComplexOpenHomotopyDirectImageIso f V).hom.app I)) ≫
      (ε (f ∣_ V)).app ((F₀.mapHomotopyCategory (.up ℤ)).obj
        ((rX.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ∣_ V)))
          |>.mapHomotopyCategory (.up ℤ)).counit.app
          ((rX.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      rX.mapDerivedCategoryFactorsh.inv.app I := by
  exact cancel_representative_tail _ _ _
    ((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategoryFactorsh.app I) _ _ _
    (singleComplexOpen_pullback_counit_representative_postcomp f V I)

end AlgebraicGeometry
