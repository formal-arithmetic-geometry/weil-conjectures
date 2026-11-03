/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateBoundaryModel.CoordinateBoundaryGeometricPullbackDefs
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.Equivalence
import all Mathlib.Logic.Equiv.Defs
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeNaturality
import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.SmoothPurity.FiniteEtaleTateLinePullback
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Kummer.PurityFiniteKummerLevel
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor
/-! # Pullback of the actual coordinate Kummer extension
Source: Milne Theorem 9.4 and the relative finite Kummer coefficient normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] constantEtale forgetEtale twistEtale
  Line Punctured coordinate openImmersion puncturedMap
  Etale.lowerStar Functor.sheafPushforwardContinuous sheafCompose
  MorphismProperty
private theorem integerToConstant_transpose (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
    (f : P.constantEtale T ⟶ F) :
    ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).homEquiv _ _) (P.integerToConstant T ≫ (P.forgetEtale T).map f) =
      ((AddCommGrpCat.uliftZMultiplesAddEquiv
          (AddCommGrpCat.of P.Coefficient)).symm 1) ≫
        (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).map
          (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
            terminalIsTerminal).homEquiv _ _) f) := by
  let J := T.smallEtaleTopology
  let U := forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}
  let am := constantSheafAdj J (ModuleCat.{u + 1} P.Coefficient)
    (terminalIsTerminal (C := T.Etale))
  let ab := constantSheafAdj J AddCommGrpCat.{u + 1}
    (terminalIsTerminal (C := T.Etale))
  apply (ab.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  have hf := (am.homEquiv _ F).symm_apply_apply f
  rw [Adjunction.homEquiv_counit] at hf
  conv_lhs => rw [← hf]
  simp only [integerToConstant, Functor.map_comp, Category.assoc]
  erw [← (constantCommuteCompose J U).inv.naturality_assoc]
  erw [← constantSheafAdj_counit_w J U F (terminalIsTerminal (C := T.Etale))]
  erw [Iso.inv_hom_id_app_assoc]
  rfl

private theorem integerToConstant_pullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (v : X ⟶ Y) :
    (Etale.upperStar AddCommGrpCat.{u + 1} v).map (P.integerToConstant Y) ≫
        Etale.upperStarForget₂Comparison P.Coefficient v (P.constantEtale Y) ≫
        (P.forgetEtale X).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) v).hom.app
            (ModuleCat.of P.Coefficient P.Coefficient)) =
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} v).hom.app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ P.integerToConstant X := by
  let c := (Scheme.upperStarConstantSheafIso
    (ModuleCat.{u + 1} P.Coefficient) v).hom.app
      (ModuleCat.of P.Coefficient P.Coefficient)
  let ab := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal
  let am := constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
    terminalIsTerminal
  let ax := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal
  let mx := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)
    terminalIsTerminal
  let av := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v
  let mv := Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) v
  let aa := (ab.comp av).ofNatIsoRight
    (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} v)
  let mm := (am.comp mv).ofNatIsoRight
    (Etale.lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} P.Coefficient) v)
  have hmate : av.homEquiv _ _
      ((Etale.upperStar AddCommGrpCat.{u + 1} v).map (P.integerToConstant Y) ≫
        Etale.upperStarForget₂Comparison P.Coefficient v (P.constantEtale Y) ≫
        (P.forgetEtale X).map c) =
      P.integerToConstant Y ≫ (P.forgetEtale Y).map (mv.homEquiv _ _ c) := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    dsimp only [av, Etale.upperStarForget₂Comparison]
    erw [Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_unit]
    simp only [CategoryTheory.Functor.map_comp]
    rfl
  apply (aa.homEquiv _ _).injective
  conv_rhs =>
    rw [Adjunction.homEquiv_naturality_right, Scheme.upperStarConstantSheafIso,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  simp only [Adjunction.comp_homEquiv]
  change ab.homEquiv _ _ (av.homEquiv _ _
    ((Etale.upperStar AddCommGrpCat.{u + 1} v).map (P.integerToConstant Y) ≫
      Etale.upperStarForget₂Comparison P.Coefficient v (P.constantEtale Y) ≫
      (P.forgetEtale X).map c)) ≫ _ = _
  erw [hmate, integerToConstant_transpose]
  have hm : mm.homEquiv _ _ c = mx.unit.app (ModuleCat.of P.Coefficient P.Coefficient) := by
    exact Adjunction.homEquiv_leftAdjointUniq_hom_app mm mx _
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at hm
  simp only [Adjunction.comp_homEquiv] at hm
  change am.homEquiv _ _ (mv.homEquiv _ _ c) ≫
    (Etale.lowerStarCompSheafSectionsTerminalIso
      (ModuleCat.{u + 1} P.Coefficient) v).hom.app _ = _ at hm
  have hx := integerToConstant_transpose P X (P.constantEtale X) (𝟙 _)
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hx
  change _ = ax.homEquiv _ _ (P.integerToConstant X)
  rw [hx]
  change _ = ((AddCommGrpCat.uliftZMultiplesAddEquiv
    (AddCommGrpCat.of P.Coefficient)).symm 1) ≫
      (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1}).map
        (mx.unit.app (ModuleCat.of P.Coefficient P.Coefficient))
  rw [← hm, CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

private theorem moduleClassToAbelian_pullback (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (v : X ⟶ Y)
    {F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)}
    {F' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)}
    (b : (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v).obj F ⟶ F')
    (x : Abelian.Ext (P.constantEtale Y) F 1) :
    P.moduleClassToAbelian X F'
        ((Abelian.Ext.mk₀ ((Scheme.upperStarConstantSheafIso
          (ModuleCat.{u + 1} P.Coefficient) v).inv.app
            (ModuleCat.of P.Coefficient P.Coefficient))).comp
          ((x.mapExactFunctor (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v)).comp
            (Abelian.Ext.mk₀ b) (add_zero 1)) (zero_add 1)) =
      Sheaf.H.map ((Etale.moduleAbelianUpperStarComparison P.Coefficient v).app F ≫
        (P.forgetEtale X).map b) 1
          (Etale.cohomologyMap v ((P.forgetEtale Y).obj F) 1
            (P.moduleClassToAbelian Y F x)) := by
  let L := Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) v
  let U := P.forgetEtale X
  let V := P.forgetEtale Y
  let H := Etale.upperStar AddCommGrpCat.{u + 1} v
  let τ := Etale.moduleAbelianUpperStarIso P.Coefficient v
  let c := (Scheme.upperStarConstantSheafIso
    (ModuleCat.{u + 1} P.Coefficient) v).app (ModuleCat.of P.Coefficient P.Coefficient)
  let d := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} v).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  have hi' := integerToConstant_pullback P v
  change H.map (P.integerToConstant Y) ≫ τ.hom.app (P.constantEtale Y) ≫ U.map c.hom =
    d.hom ≫ P.integerToConstant X at hi'
  have hi : P.integerToConstant X ≫ U.map c.inv ≫ τ.inv.app (P.constantEtale Y) =
      d.inv ≫ H.map (P.integerToConstant Y) := by
    have hh := congrArg (fun f ↦ d.inv ≫ f ≫ U.map c.inv ≫
      τ.inv.app (P.constantEtale Y)) hi'
    have hh' := hh.symm
    simp only [Category.assoc, ← U.map_comp_assoc, Iso.hom_inv_id, U.map_id,
      Category.id_comp,
      Iso.hom_inv_id_app, Iso.inv_hom_id_assoc] at hh'
    exact hh'.trans (congrArg (fun z ↦ d.inv ≫ z) (Category.comp_id _))
  have ht := Abelian.Ext.mapExactFunctor_comp_mk₀_eq L U (V ⋙ H) τ 1 x
  rw [← Abelian.Ext.mapExactFunctor_mapExactFunctor] at ht
  have ht' : (x.mapExactFunctor L).mapExactFunctor U =
      (Abelian.Ext.mk₀ (τ.inv.app (P.constantEtale Y))).comp
        (((x.mapExactFunctor V).mapExactFunctor H).comp (Abelian.Ext.mk₀ (τ.hom.app F))
          (add_zero 1)) (zero_add 1) := by
    rw [ht, Abelian.Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id_app,
      Abelian.Ext.mk₀_id_comp]
  simp only [moduleClassToAbelian, Sheaf.H.map_apply, Etale.cohomologyMap_apply,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  change (Abelian.Ext.mk₀ (P.integerToConstant X)).comp
      ((Abelian.Ext.mk₀ (U.map c.inv)).comp
        (((x.mapExactFunctor L).mapExactFunctor U).comp (Abelian.Ext.mk₀ (U.map b))
          (add_zero 1)) (zero_add 1)) (zero_add 1) =
    ((Abelian.Ext.mk₀ d.inv).comp
      ((Abelian.Ext.mk₀ (H.map (P.integerToConstant Y))).comp
        ((x.mapExactFunctor V).mapExactFunctor H) (zero_add 1)) (zero_add 1)).comp
      (Abelian.Ext.mk₀ (τ.hom.app F ≫ U.map b)) (add_zero 1)
  rw [ht']
  simp only [← Abelian.Ext.comp_assoc_of_third_deg_zero,
    ← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
  rw [hi]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]

private theorem moduleClassToAbelian_kummer (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (T : Scheme.{u})
    (hr : IsUnit (P.exponent : Γ(T, ⊤))) (t : Γ(T, ⊤)ˣ) :
    P.moduleClassToAbelian T (P.twistEtale h T) (P.kummerEtale h T hr t) =
      Sheaf.H.map (P.rootCoefficientMap h T) 1
        (T.kummerδ₀ P.exponent hr (Additive.ofMul t)) := by
  unfold kummerEtale
  exact (Equiv.ofBijective _
    (P.moduleClassToAbelian_bijective T (P.twistEtale h T))).apply_symm_apply _

private theorem coordinate_pro_kummer_pullback (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (g : T ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (hk : Abelian.Ext.coordinatePullbackIdentity
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g))
      (P.coordinateEtaleKummer h Y a) (P.coordinateEtaleKummer h T (g ≫ a))
      ((Scheme.upperStarConstantSheafIso
        (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g)).hom.app
          (ModuleCat.of P.Coefficient P.Coefficient))
      (P.twistEtalePullback h (puncturedMap g))) :
    Abelian.Ext.coordinatePullbackIdentity
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g))
      (P.coordinateKummer h Y a) (P.coordinateKummer h T (g ≫ a))
      ((ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g)).hom.app
          (P.constantEtale (Punctured Y)) ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) (Punctured T)).map
          ((Scheme.upperStarConstantSheafIso
            (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g)).hom.app
              (ModuleCat.of P.Coefficient P.Coefficient)))
      ((ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g)).hom.app
          (P.twistEtale h (Punctured Y)) ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) (Punctured T)).map
          (P.twistEtalePullback h (puncturedMap g))) := by
  let L := Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g)
  let V := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) (Punctured T)
  let U := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) (Punctured Y)
  let H := ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g)
  let τ := ProEtale.comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g)
  let x := P.coordinateEtaleKummer h Y a
  let y := P.coordinateEtaleKummer h T (g ≫ a)
  let b := P.twistEtalePullback h (puncturedMap g)
  let c := (Scheme.upperStarConstantSheafIso
    (ModuleCat.{u + 1} P.Coefficient) (puncturedMap g)).hom.app
      (ModuleCat.of P.Coefficient P.Coefficient)
  have ht := Abelian.Ext.mapExactFunctor_comp_mk₀_eq L V (U ⋙ H) τ 1 x
  rw [← Abelian.Ext.mapExactFunctor_mapExactFunctor] at ht
  change ((x.mapExactFunctor U).mapExactFunctor H).comp
      (Abelian.Ext.mk₀ (τ.hom.app _ ≫ V.map b)) (add_zero 1) =
    (Abelian.Ext.mk₀ (τ.hom.app _ ≫ V.map c)).comp (y.mapExactFunctor V) (zero_add 1)
  rw [← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.comp_assoc_of_third_deg_zero, ht,
    Abelian.Ext.comp_assoc_of_third_deg_zero, ← Abelian.Ext.mapExactFunctor_mk₀,
    ← Abelian.Ext.mapExactFunctor_comp]
  rw [show (x.mapExactFunctor L).comp (Abelian.Ext.mk₀ b) (add_zero 1) =
      (Abelian.Ext.mk₀ c).comp y (zero_add 1) from hk,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀_assoc]
  all_goals rfl

/-- The actual ordinary and pro-etale coordinate Kummer classes pull back together.
Source: lem-pur-relative-kummer-coefficient-normalization and the exact
finite-coefficient site comparison.
Proof: apply the normalized root insertion square on the etale site, then conjugate
by the canonical comparison-upper-star isomorphisms on the pro-etale site.
(blueprint: aux-lem-pur-coordinate-kummer-pullback) -/
theorem coordinate_kummer_pullback_aux (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) {T Y : Scheme.{u}} (g : T ⟶ Y)
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : P.CoordinateKummerPullback h g a := by
  have hk := coordinate_etale_kummer_pullback P h g a
  exact ⟨hk, coordinate_pro_kummer_pullback P h g a hk⟩
end WeilConjectures.PurityFiniteSetting
