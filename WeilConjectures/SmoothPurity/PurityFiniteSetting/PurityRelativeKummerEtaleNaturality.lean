/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor

/-! # Naturality of the étale Kummer class under pullback

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

section KummerNaturality

variable (P : PurityFiniteSetting.{u})

/-- The scalar-forgetting comparison of pullbacks is natural. -/
@[reassoc]
lemma upperStarForget₂Comparison_naturality' {X T : Scheme.{u}} (f : X ⟶ T)
    {B B' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)} (φ : B ⟶ B') :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).map ((P.forgetEtale T).map φ) ≫
        Etale.upperStarForget₂Comparison P.Coefficient f B' =
      Etale.upperStarForget₂Comparison P.Coefficient f B ≫
        (P.forgetEtale X).map ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).map φ) := by
  apply ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp]
  have h1 := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.naturality
    ((P.forgetEtale T).map φ)
  simp only [Functor.id_map, Functor.comp_map] at h1
  have hB := Etale.unit_comp_lowerStar_map_upperStarForget₂Comparison P.Coefficient f B
  have hB' := Etale.unit_comp_lowerStar_map_upperStarForget₂Comparison P.Coefficient f B'
  have h2 := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) f).unit.naturality
    φ
  simp only [Functor.id_map, Functor.comp_map] at h2
  erw [← Category.assoc, ← h1, Category.assoc, hB', ← Category.assoc, hB]
  exact (congrArg (P.forgetEtale T).map h2).trans (Functor.map_comp _ _ _)

/-- Scalar forgetting commutes with pullback. -/
noncomputable def forgetUpperStarIso {X T : Scheme.{u}} (f : X ⟶ T) :
    P.forgetEtale T ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f ≅
      Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f ⋙ P.forgetEtale X :=
  NatIso.ofComponents (fun B ↦ asIso (Etale.upperStarForget₂Comparison P.Coefficient f B))
    (fun φ ↦ upperStarForget₂Comparison_naturality' P f φ)

/-- The degree-zero generator `ℤ ⟶ A` is compatible with pullback. -/
lemma integerToConstant_upperStar {X T : Scheme.{u}} (f : X ⟶ T) :
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app
        (AddCommGrpCat.of (ULift ℤ)) ≫ P.integerToConstant X =
      (Etale.upperStar AddCommGrpCat.{u + 1} f).map (P.integerToConstant T) ≫
        Etale.upperStarForget₂Comparison P.Coefficient f (P.constantEtale T) ≫
        (P.forgetEtale X).map ((Scheme.upperStarConstantSheafIso
          (ModuleCat.{u + 1} P.Coefficient) f).hom.app (ModuleCat.of P.Coefficient P.Coefficient)) := by
  have hn := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.naturality
    ((AddCommGrpCat.uliftZMultiplesAddEquiv (AddCommGrpCat.of P.Coefficient)).symm 1)
  simp only [integerToConstant, Functor.map_comp, Category.assoc, Functor.comp_map] at hn ⊢
  erw [upperStar_constantCommuteCompose_inv P f (ModuleCat.of P.Coefficient P.Coefficient),
    reassoc_of% hn]

/-- Composition of the maps induced on cohomology. -/
lemma sheafH_map_map {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    {F G H : Sheaf J AddCommGrpCat.{u + 1}} (a : F ⟶ G) (b : G ⟶ H) (n : ℕ) (x : Sheaf.H F n) :
    Sheaf.H.map b n (Sheaf.H.map a n x) = Sheaf.H.map (a ≫ b) n x := by
  rw [Sheaf.H.map_apply, Sheaf.H.map_apply, Sheaf.H.map_apply,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

variable (h : P.ramificationIndex ∣ P.level)

/-- The defining property of the étale Kummer class. -/
lemma moduleClassToAbelian_kummerEtale (T : Scheme.{u}) (hT : IsUnit (P.exponent : Γ(T, ⊤)))
    (s : Γ(T, ⊤)ˣ) :
    P.moduleClassToAbelian T (P.twistEtale h T) (P.kummerEtale h T hT s) =
      Sheaf.H.map (P.rootCoefficientMap h T) 1 (T.kummerδ₀ P.exponent hT (Additive.ofMul s)) :=
  (Equiv.ofBijective _ (P.moduleClassToAbelian_bijective T (P.twistEtale h T))).apply_symm_apply _

/-- The pulled-back root coefficient map. -/
lemma rootCoefficientMap_upperStar {X T : Scheme.{u}} (f : X ⟶ T) :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).map (P.rootCoefficientMap h T) ≫
        Etale.upperStarForget₂Comparison P.Coefficient f (P.twistEtale h T) ≫
        (P.forgetEtale X).map (P.twistEtalePullback h f) =
      Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf P.exponent f ≫
        P.rootCoefficientMap h X := by
  have hroot : P.rootPullback f =
      Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf P.exponent f :=
    ((Classical.choose_spec (P.existsUnique_rootPullback f)).2 _
      (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι P.exponent f)).symm
  rw [← hroot]
  exact (Classical.choose_spec (P.existsUnique_twistEtalePullback h f)).1

/-- Naturality of the étale Kummer class. -/
theorem kummerEtale_upperStar {X T : Scheme.{u}} (f : X ⟶ T)
    (hT : IsUnit (P.exponent : Γ(T, ⊤))) (hX : IsUnit (P.exponent : Γ(X, ⊤)))
    (s : Γ(T, ⊤)ˣ) :
    ((P.kummerEtale h T hT s).mapExactFunctor
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f)).comp
        (Abelian.Ext.mk₀ (P.twistEtalePullback h f)) (add_zero 1) =
      (Abelian.Ext.mk₀ ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient)
        f).hom.app (ModuleCat.of P.Coefficient P.Coefficient))).comp
        (P.kummerEtale h X hX (Units.map f.appTop.hom s)) (zero_add 1) := by
  suffices key : (Abelian.Ext.mk₀ ((Scheme.upperStarConstantSheafIso
      (ModuleCat.{u + 1} P.Coefficient) f).inv.app (ModuleCat.of P.Coefficient P.Coefficient))).comp
      (((P.kummerEtale h T hT s).mapExactFunctor
        (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) f)).comp
        (Abelian.Ext.mk₀ (P.twistEtalePullback h f)) (add_zero 1)) (zero_add 1) =
      P.kummerEtale h X hX (Units.map f.appTop.hom s) by
    rw [← key, Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.hom_inv_id_app, Abelian.Ext.mk₀_id_comp]
  apply (P.moduleClassToAbelian_bijective X (P.twistEtale h X)).1
  rw [moduleClassToAbelian_kummerEtale, ← Scheme.sheafH_map_cohomologyMap_kummerδ₀ f P.exponent hT hX s,
    sheafH_map_map, ← rootCoefficientMap_upperStar, ← sheafH_map_map, ← sheafH_map_map,
    ← Etale.cohomologyMap_map, ← moduleClassToAbelian_kummerEtale P h T hT s]
  simp only [moduleClassToAbelian, Etale.cohomologyMap_apply, Sheaf.H.map_apply,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  have hι : P.integerToConstant X ≫ (P.forgetEtale X).map
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) f).inv.app
        (ModuleCat.of P.Coefficient P.Coefficient)) ≫
      (forgetUpperStarIso P f).inv.app (P.constantEtale T) =
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
        (AddCommGrpCat.of (ULift ℤ))).hom ≫
        (Etale.upperStar AddCommGrpCat.{u + 1} f).map (P.integerToConstant T) := by
    rw [← cancel_epi ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).hom.app
      (AddCommGrpCat.of (ULift ℤ))), reassoc_of% (integerToConstant_upperStar P f)]
    simp [forgetUpperStarIso, ← Functor.map_comp_assoc]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, IsIso.hom_inv_id, Category.comp_id]
  rw [Abelian.Ext.mapExactFunctor_mapExactFunctor, Abelian.Ext.mapExactFunctor_mapExactFunctor,
    Abelian.Ext.mapExactFunctor_eq_of_iso (forgetUpperStarIso P f)]
  simp only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀_assoc, Abelian.Ext.mk₀_comp_mk₀]
  first
    | (erw [hι]; rfl)
    | (simp only [hι]; rfl)

end KummerNaturality

end WeilConjectures.PurityFiniteSetting
