/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor

/-! # Constant sheaves and scalar forgetting under étale pullback

Auxiliary coherence lemmas for the naturality of the étale Kummer class.
Source: blueprint lem-pur-relative-kummer-exchange-from-conclusions (auxiliary lemmas).
-/
@[expose] public section
set_option autoImplicit false
universe u' u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

section ConstantCoherence

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  {D B : Type*} [Category* D] [Category* B] (U : D ⥤ B) [HasWeakSheafify J D]
  [HasWeakSheafify J B] [J.PreservesSheafification U] [J.HasSheafCompose U]

/-- The unit of the constant sheaf adjunction is compatible with `constantCommuteCompose`. -/
theorem constantSheafAdj_unit_app_comp_constantCommuteCompose_inv' {T : C}
    (hT : IsTerminal T) (M : D) :
    (constantSheafAdj J B hT).unit.app (U.obj M) ≫
        ((sheafSections J B).obj (Opposite.op T)).map
          ((constantCommuteCompose J U).inv.app M) =
      U.map ((constantSheafAdj J D hT).unit.app M) := by
  refine Eq.trans ((constantSheafAdj J B hT).homEquiv_unit _ _ _).symm ?_
  apply ((constantSheafAdj J B hT).homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  have hc := constantSheafAdj_counit_w J U ((constantSheaf J D).obj M) hT
  have hn := (constantCommuteCompose J U).hom.naturality ((constantSheafAdj J D hT).unit.app M)
  have ht := (constantSheafAdj J D hT).left_triangle_components M
  simp only [Functor.comp_map] at hn
  rw [← cancel_epi ((constantCommuteCompose J U).hom.app M), Iso.hom_inv_id_app]
  erw [← reassoc_of% hn]
  erw [hc]
  rw [← Functor.map_comp]
  erw [ht]
  exact ((sheafCompose J U).map_id _).symm

end ConstantCoherence

section UpperStarConstant

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The unit of `Adjunction.ofNatIsoRight`. -/
lemma ofNatIsoRight_unit_app' {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G H : D ⥤ C} (adj : F ⊣ G) (e : G ≅ H) (x : C) :
    (adj.ofNatIsoRight e).unit.app x = adj.unit.app x ≫ e.hom.app _ := by
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id]

/-- The identification `f^* A_T ≅ A_S` through the units of the adjunctions. -/
lemma unit_app_upperStarConstantSheafIso' {S T : Scheme.{u}} (f : S ⟶ T) (a : A) :
    (constantSheafAdj T.smallEtaleTopology A terminalIsTerminal).unit.app a ≫
      ((sheafSections T.smallEtaleTopology A).obj (op (⊤_ T.Etale))).map
        ((Etale.upperStarLowerStarAdjunction A f).unit.app _ ≫
          (Etale.lowerStar A f).map ((Scheme.upperStarConstantSheafIso A f).hom.app a)) ≫
      (Etale.lowerStarCompSheafSectionsTerminalIso A f).hom.app _ =
    (constantSheafAdj S.smallEtaleTopology A terminalIsTerminal).unit.app a := by
  have := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj T.smallEtaleTopology A terminalIsTerminal).comp
        (Etale.upperStarLowerStarAdjunction A f)).ofNatIsoRight
      (Etale.lowerStarCompSheafSectionsTerminalIso A f))
    (constantSheafAdj S.smallEtaleTopology A terminalIsTerminal) a
  rw [Adjunction.homEquiv_unit, ofNatIsoRight_unit_app'] at this
  rw [← this, Scheme.upperStarConstantSheafIso]
  simp only [Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  erw [← (Etale.lowerStarCompSheafSectionsTerminalIso A f).hom.naturality]
  rfl

end UpperStarConstant

section ForgetConstant

variable (P : PurityFiniteSetting.{u})

/-- The pullback of the comparison `A_T ⟶ forget (A_T)` of constant sheaves with the
scalar-forgetting functor is the corresponding comparison on `X`. -/
lemma upperStar_constantCommuteCompose_inv {X T : Scheme.{u}} (f : X ⟶ T)
    (M : ModuleCat.{u + 1} P.Coefficient) :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).map
        ((constantCommuteCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})).inv.app M) ≫
      Etale.upperStarForget₂Comparison P.Coefficient f
        ((constantSheaf T.smallEtaleTopology _).obj M) ≫
      (P.forgetEtale X).map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) f).hom.app M) =
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app
        ((forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).obj M) ≫
      (constantCommuteCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})).inv.app M := by
  apply ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    Adjunction.unit_naturality_assoc]
  erw [reassoc_of% (Etale.unit_comp_lowerStar_map_upperStarForget₂Comparison P.Coefficient f
    ((constantSheaf T.smallEtaleTopology _).obj M))]
  apply ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine (cancel_mono ((Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f).hom.app
    ((P.forgetEtale X).obj ((constantSheaf X.smallEtaleTopology _).obj M)))).1 ?_
  have h3 := unit_app_upperStarConstantSheafIso' AddCommGrpCat.{u + 1} f
    ((forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).obj M)
  have h4 := unit_app_upperStarConstantSheafIso' (ModuleCat.{u + 1} P.Coefficient) f M
  have h5 := constantSheafAdj_unit_app_comp_constantCommuteCompose_inv' T.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) terminalIsTerminal M
  have h6 := constantSheafAdj_unit_app_comp_constantCommuteCompose_inv' X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}) terminalIsTerminal M
  have h7 := (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f).hom.naturality
    ((constantCommuteCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})).inv.app M)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at h3 h4 h7 ⊢
  erw [h7, reassoc_of% h3, h6, reassoc_of% h5, ← h4]
  simp only [Functor.map_comp]
  rfl

end ForgetConstant

end WeilConjectures.PurityFiniteSetting
