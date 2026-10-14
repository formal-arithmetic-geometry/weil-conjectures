/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import Sheaf.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData

/-! # Normalizing the derived unit through the open pullback square

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-unit-square-factorization).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem map_comp_square_factorization
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    (r : C ⥤ D) (L₀ : D ⥤ E) (L : C ⥤ B) (s : B ⥤ E)
    (S : r ⋙ L₀ ⟶ L ⋙ s)
    {P N : C} {T W : B} {H : D} {J : E}
    (k : H ⟶ r.obj P) (β : P ⟶ N) (α : L.obj N ⟶ T)
    (ε : L.obj P ⟶ W) (v : W ⟶ T) (j : s.obj T ⟶ J)
    (hn : L.map β ≫ α = ε ≫ v) :
    L₀.map (k ≫ r.map β) ≫ S.app N ≫ s.map α ≫ j =
      L₀.map k ≫ S.app P ≫ s.map ε ≫ s.map v ≫ j := by
  have hnat := S.naturality β
  simp only [Functor.comp_map] at hnat
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, ← s.map_comp_assoc, hn, s.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
-- The existing signature contains the unused F₀ binding; preserve it verbatim.
set_option maxHeartbeats 800000 in
-- Normalizing the pinned derived choices and scheme-module instance aliases needs this budget.
/-- A separate step of the open counit factorization.
Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-unit-square-factorization).

Proof: Put P = F_h(I), beta = F.rightDerivedFunctorUnit(I), and let v be
 the homotopy tensor adjunction counit at I. Apply the pinned derived Hom-equivalence
 compatibility to the homotopy morphism v. The homotopy adjunction sends v to the
 identity of P, so its localized image followed by beta is beta itself. Injectivity
 of the derived Hom equivalence, whose inverse sends beta to Lf(beta) followed by
 the derived counit, gives
 Lf(beta) followed by a_f.counit = epsilon_f(P) followed by Qh(v).
 Let S be the composite natural isomorphism formed by the five displayed factors.
 Its naturality at beta moves Lf0(rY(beta)) from before S to rX(Lf(beta)) after S.
 First distribute Lf0 over the composite with the inverse source factorization.
 Then substitute this naturality equation, combine the two successive rX images,
 apply the normalized counit identity, and distribute rX over its two factors.
 Associativity gives exactly the displayed intermediate composite. This uses no
 tensor comparison cancellation, no boundedness, and no inverse of beta; hence it
 also applies to empty opens and the zero complex. -/
theorem singleComplexOpen_unit_square_factorization
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
      @Classical.choose _ _ exists_derivedPullbackComposition
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
    (derivedPullback (f ∣_ V)).map
      (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I))) ≪≫
        (c (f ∣_ V) V.ι).app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))).hom ≫
      rX.mapDerivedCategory.map ((ε f).app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      rX.mapDerivedCategory.map (DerivedCategory.Qh.map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
          |>.mapHomotopyCategory (.up ℤ)).counit.app I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let hAdd : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
    @Classical.choose _ _ exists_derivedPullbackComposition
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let rY := schemeOpenRestriction Y V
  let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
  let a := @singleComplexOpenPinnedAdjunction.{u, w} _
  let c := @singleComplexOpenPinnedComposition.{u, w} _
  let ε := @Classical.choose _ _
    (Classical.choose_spec exists_derivedPullbackComposition)
  let P := (F.mapHomotopyCategory (.up ℤ)).obj I
  let β := F.rightDerivedFunctorUnit.app I
  let ah := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
    |>.mapHomotopyCategory (.up ℤ)
  have hcompat := Classical.choose_spec (exists_schemeDerivedAdjunction f
    (hAdd := hAdd f) (ε f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f)) P I (ah.counit.app I)
  have hn : (derivedPullback f).map β ≫ (a f).counit.app (DerivedCategory.Qh.obj I) =
      (ε f).app P ≫ DerivedCategory.Qh.map (ah.counit.app I) := by
    change (a f).homEquiv (DerivedCategory.Qh.obj P) (DerivedCategory.Qh.obj I)
      ((ε f).app P ≫ DerivedCategory.Qh.map (ah.counit.app I)) =
      DerivedCategory.Qh.map (ah.homEquiv P I (ah.counit.app I)) ≫ β at hcompat
    have hv : ah.homEquiv P I (ah.counit.app I) = 𝟙 P := by
      rw [← ah.homEquiv_symm_id I]
      exact (ah.homEquiv _ I).apply_symm_apply (𝟙 _)
    have hc : (a f).homEquiv (DerivedCategory.Qh.obj P) (DerivedCategory.Qh.obj I)
        ((ε f).app P ≫ DerivedCategory.Qh.map (ah.counit.app I)) = β := by
      erw [hv, DerivedCategory.Qh.map_id, Category.id_comp] at hcompat
      exact hcompat
    simpa only [Adjunction.homEquiv_counit, Equiv.symm_apply_apply] using
      congrArg ((a f).homEquiv (DerivedCategory.Qh.obj P)
        (DerivedCategory.Qh.obj I)).symm hc.symm
  let S : rY.mapDerivedCategory ⋙ derivedPullback (f ∣_ V) ≅
      derivedPullback f ⋙ rX.mapDerivedCategory :=
    Functor.isoWhiskerRight (singleComplexOpenPullbackIso Y V).symm _ ≪≫
      c (f ∣_ V) V.ι ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k) (morphismRestrict_ι f V)) ≪≫
      (c (f ⁻¹ᵁ V).ι f).symm ≪≫
      Functor.isoWhiskerLeft _ (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V))
  have hmain : (derivedPullback (f ∣_ V)).map
      (rY.mapDerivedCategoryFactorsh.inv.app P ≫ rY.mapDerivedCategory.map β) ≫
      S.hom.app _ ≫ rX.mapDerivedCategory.map ((a f).counit.app _) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I =
    (derivedPullback (f ∣_ V)).map (rY.mapDerivedCategoryFactorsh.inv.app P) ≫
      S.hom.app (DerivedCategory.Qh.obj P) ≫
      rX.mapDerivedCategory.map ((ε f).app P) ≫
      rX.mapDerivedCategory.map (DerivedCategory.Qh.map (ah.counit.app I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I := by
    exact map_comp_square_factorization rY.mapDerivedCategory (derivedPullback (f ∣_ V))
      (derivedPullback f) rX.mapDerivedCategory S.hom _ β _ _ _ _ hn
  simpa only [S, Iso.app_hom, Functor.mapIso_hom, Functor.comp_obj, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    eqToIso.hom, eqToHom_app] using hmain

end AlgebraicGeometry
