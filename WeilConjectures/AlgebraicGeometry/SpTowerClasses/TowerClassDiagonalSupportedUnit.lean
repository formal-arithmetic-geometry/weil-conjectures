/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFiniteDiagonal
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryForgetComparison
import WeilConjectures.SmoothPurity.OpenClosedIntegralSections
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import all WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.Normalization.ExactClopenNormalization
import all WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate

/-! # The supported integral unit and the finite supported quotient

Helper results for `exists_diagonalFiniteSource`: the transported supported integral unit is the
canonical constant direct-image map, and on constant generators the finite supported quotient is
the finite quotient followed by the coefficient-pullback adjunct.
(blueprint: lem-sp-tower-class-diagonal-finite-source). -/


@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings SpTowerShriek.tau lineModule
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

section
open AlgebraicGeometry.Scheme
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

private theorem sheafification_lift_app
    {C E : Type*} [Category* C] [Category* E]
    (J : GrothendieckTopology C) [HasWeakSheafify J E]
    {P : Cᵒᵖ ⥤ E} (F : Sheaf J E) (t : P ⟶ F.obj) (U : Cᵒᵖ) :
    (toSheafify J P).app U ≫
        (((sheafificationAdjunction J E).homEquiv P F).symm t).hom.app U = t.app U := by
  have h := Equiv.apply_symm_apply ((sheafificationAdjunction J E).homEquiv P F) t
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun k ↦ k.app U) h

private theorem constant_comparison_mate
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J E] [HasWeakSheafify K E]
    (G : C ⥤ D) [G.IsContinuous J K]
    {L : Sheaf J E ⥤ Sheaf K E}
    (adj : L ⊣ G.sheafPushforwardContinuous E J K)
    {T : C} {S : D} (hT : IsTerminal T) (hS : IsTerminal S)
    (e : G.sheafPushforwardContinuous E J K ⋙ (sheafSections J E).obj (op T) ≅
      (sheafSections K E).obj (op S)) (a : E)
    (h : (toSheafify K ((Functor.const Dᵒᵖ).obj a)).app (op (G.obj T)) ≫
      e.hom.app ((constantSheaf K E).obj a) =
        (toSheafify K ((Functor.const Dᵒᵖ).obj a)).app (op S)) :
    adj.homEquiv _ _
        (((((constantSheafAdj J E hT).comp adj).ofNatIsoRight e).leftAdjointUniq
          (constantSheafAdj K E hS)).hom.app a) =
      ((sheafificationAdjunction J E).homEquiv _ _).symm
        (Functor.whiskerLeft G.op (toSheafify K ((Functor.const Dᵒᵖ).obj a))) := by
  apply ((constantSheafAdj J E hT).homEquiv _ _).injective
  apply (cancel_mono (e.hom.app ((constantSheaf K E).obj a))).mp
  have hu := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((constantSheafAdj J E hT).comp adj).ofNatIsoRight e)
    (constantSheafAdj K E hS) a
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hu
  refine hu.trans ?_
  rw [constantSheafAdj_homEquiv_apply]
  have hs : (constantSheafAdj K E hS).unit.app a =
      (toSheafify K ((Functor.const Dᵒᵖ).obj a)).app (op S) := by
    rw [← Adjunction.homEquiv_id, constantSheafAdj_homEquiv_apply]
    exact Category.comp_id _
  rw [hs]
  have hc := sheafification_lift_app J
    ((G.sheafPushforwardContinuous E J K).obj ((constantSheaf K E).obj a))
    (Functor.whiskerLeft G.op (toSheafify K ((Functor.const Dᵒᵖ).obj a))) (op T)
  exact h.symm.trans (congrArg (fun k ↦ k ≫ e.hom.app _) hc).symm

private theorem integer_comparison_mate_cartier (T : Scheme.{u}) :
    (comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _
        (cartierIntegralConstantComparisonIso T).hom =
      ((sheafificationAdjunction T.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _).symm (Functor.whiskerLeft (Scheme.toProEt T).op
          (toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) := by
  apply constant_comparison_mate T.smallEtaleTopology (Scheme.ProEt.topology T)
    (Scheme.toProEt T) (comparisonAdjunction AddCommGrpCat.{u + 1} T)
    (Scheme.Etale.isTerminalMkId T) (Scheme.ProEt.isTerminalMkId T)
    ((Scheme.toProEt T).sheafPushforwardContinuousCompSheafSectionsObjIso
      AddCommGrpCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)
      (op (Scheme.Etale.mk (𝟙 T))))
  exact Category.comp_id _

private theorem integer_comparison_mate_integer (T : Scheme.{u}) :
    (comparisonAdjunction AddCommGrpCat.{u + 1} T).homEquiv _ _
        (integerComparison T).hom =
      ((sheafificationAdjunction T.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _).symm (Functor.whiskerLeft (Scheme.toProEt T).op
          (toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) := by
  apply constant_comparison_mate T.smallEtaleTopology (Scheme.ProEt.topology T)
    (Scheme.toProEt T) (comparisonAdjunction AddCommGrpCat.{u + 1} T)
    (Scheme.Etale.isTerminalMkId T) (Scheme.ProEt.isTerminalMkId T)
    ((Scheme.toProEt T).sheafPushforwardContinuousCompSheafSectionsObjIso
      AddCommGrpCat.{u + 1} T.smallEtaleTopology (Scheme.ProEt.topology T)
      (op (Scheme.Etale.mk (𝟙 T))))
  exact Category.comp_id _

private theorem etale_constant_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
        (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom) =
      ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _).symm (Functor.whiskerLeft f.Etale.op
          (toSheafify X.smallEtaleTopology
            ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) := by
  apply constant_comparison_mate Y.smallEtaleTopology X.smallEtaleTopology
    f.Etale (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
    terminalIsTerminal terminalIsTerminal
    (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} f)
  change (toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app _ ≫
      (sheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).map
          (PreservesTerminal.iso f.Etale).inv.op = _
  exact ((toSheafify X.smallEtaleTopology
    ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality
      (PreservesTerminal.iso f.Etale).inv.op).symm.trans (Category.id_comp _)

/-- The supported integral unit followed by the comparison mates is the constant
direct-image map, before transport: the étale/pro-étale mate calculation. -/
private theorem supported_unit_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Etale.supportedIntegralUnit f ≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} f).map
        ((comparisonAdjunction AddCommGrpCat.{u + 1} X).homEquiv _ _
          (cartierIntegralConstantComparisonIso X).hom) ≫
      (lowerStarCompComparisonLowerStarIso f AddCommGrpCat.{u + 1}).inv.app
        ((constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) =
    (comparisonAdjunction AddCommGrpCat.{u + 1} Y).homEquiv _ _
        (integerComparison Y).hom ≫
      (comparisonLowerStar AddCommGrpCat.{u + 1} Y).map
        (proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
  unfold Etale.supportedIntegralUnit
  rw [integer_comparison_mate_integer Y, integer_comparison_mate_cartier X, etale_constant_mate f]
  apply ((sheafificationAdjunction Y.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    _ _).injective
  simp only [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  let Z := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let ηX := toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj Z)
  let ηPX := toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj Z)
  let ηPY := toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj Z)
  let BX := (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj Z
  let qX := ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    _ ((comparisonLowerStar AddCommGrpCat.{u + 1} X).obj BX)).symm
      (Functor.whiskerLeft (Scheme.toProEt X).op ηPX)
  let qp := proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1} Z
  let b := (lowerStarCompComparisonLowerStarIso f AddCommGrpCat.{u + 1}).inv.app BX
  change ηX.app (f.Etale.op.obj U) ≫
      (qX.hom.app (f.Etale.op.obj U) ≫ b.hom.app U) =
    ηPY.app ((Scheme.toProEt Y).op.obj U) ≫ qp.hom.app ((Scheme.toProEt Y).op.obj U)
  have hx := sheafification_lift_app X.smallEtaleTopology
    ((comparisonLowerStar AddCommGrpCat.{u + 1} X).obj BX)
    (Functor.whiskerLeft (Scheme.toProEt X).op ηPX) (f.Etale.op.obj U)
  have hy := sheafification_lift_app (Scheme.ProEt.topology Y)
    ((proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).obj BX)
    (Functor.whiskerLeft (proEtaleBaseChange f).op ηPX) ((Scheme.toProEt Y).op.obj U)
  have hb : b.hom.app U = 𝟙 _ := by
    dsimp [b, lowerStarCompComparisonLowerStarIso, toProEtCompOverPullbackIso]
    exact (Category.id_comp _).trans ((Category.comp_id _).trans (BX.obj.map_id _))
  calc
    _ = (ηX.app (f.Etale.op.obj U) ≫ qX.hom.app (f.Etale.op.obj U)) ≫ b.hom.app U :=
      (Category.assoc _ _ _).symm
    _ = ηPX.app ((Scheme.toProEt X).op.obj (f.Etale.op.obj U)) ≫ b.hom.app U :=
      congrArg (fun k ↦ k ≫ b.hom.app U) hx
    _ = ηPX.app ((Scheme.toProEt X).op.obj (f.Etale.op.obj U)) := by
      rw [hb]
      exact Category.comp_id _
    _ = _ := hy.symm

private theorem integralSource_comparison_unit
    {X Z : Scheme.{u}} (i : X ⟶ Z) :
    (comparisonAdjunction AddCommGrpCat.{u + 1} Z).unit.app
        ((Etale.lowerStar AddCommGrpCat.{u + 1} i).obj
          (Etale.supportedIntegralConstant X)) ≫
      (comparisonLowerStar AddCommGrpCat.{u + 1} Z).map
        (cartierIntegralSourceComparison i) =
    (Etale.lowerStar AddCommGrpCat.{u + 1} i).map
      ((comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app
          (Etale.supportedIntegralConstant X) ≫
        (comparisonLowerStar AddCommGrpCat.{u + 1} X).map
          (cartierIntegralConstantComparisonIso X).hom) ≫
      (lowerStarCompComparisonLowerStarIso i AddCommGrpCat.{u + 1}).inv.app
        ((constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
  have hm := unit_mateEquiv_symm
    (comparisonAdjunction AddCommGrpCat.{u + 1} X)
    (comparisonAdjunction AddCommGrpCat.{u + 1} Z)
    (lowerStarCompComparisonLowerStarIso i AddCommGrpCat.{u + 1}).inv
    (Etale.supportedIntegralConstant X)
  change _ = (comparisonAdjunction AddCommGrpCat.{u + 1} Z).unit.app _ ≫
    (comparisonLowerStar AddCommGrpCat.{u + 1} Z).map
      ((lowerStarComparisonUpperStarBaseChange i AddCommGrpCat.{u + 1}).app
        (Etale.supportedIntegralConstant X)) at hm
  unfold cartierIntegralSourceComparison
  rw [Functor.map_comp, ← Category.assoc]
  erw [← hm]
  simp only [Functor.map_comp, Category.assoc]
  have hh := (lowerStarCompComparisonLowerStarIso i AddCommGrpCat.{u + 1}).inv.naturality
    (cartierIntegralConstantComparisonIso X).hom
  simp only [Functor.comp_map] at hh
  erw [← hh]

/-- The transported supported integral unit is the canonical constant direct-image map. -/
theorem supportedIntegralUnit_eq_proEtaleConstantDirectImageMap (S : Scheme.{u}) :
    supportedIntegralUnit S = proEtaleConstantDirectImageMap (diagonalImmersion S)
      AddCommGrpCat.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  unfold supportedIntegralUnit
  rw [Iso.inv_comp_eq]
  apply ((comparisonAdjunction AddCommGrpCat.{u + 1}
    (diagonalSurface S)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    ← supported_unit_mate]
  congr 1
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact integralSource_comparison_unit (diagonalImmersion S)

end

section
open AlgebraicGeometry.Scheme

/-- On constant generators, the supported finite quotient after the canonical constant
direct-image map is the finite quotient followed by the coefficient pullback adjunct. -/
theorem proEtaleConstantDirectImageMap_comp_finiteSupportedQuotient
    {b : SpTowerShriek.Base l E}
    {S : Scheme.{u}} (g : SpTowerShriek.Geometry l E b (diagonalImmersion S))
    (p : CoefficientPullback l E b (diagonalImmersion S) g) (n : ℕ) :
    proEtaleConstantDirectImageMap (diagonalImmersion S) AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≫ finiteSupportedQuotient l E g n =
      finiteQuotient l E (diagonalSurface S) n ≫
        (finiteForget l E (diagonalSurface S) n).map
          ((SpTowerShriek.ev l E (diagonalSurface S) n).map
            ((g.ordinaryAdjunction.homEquiv _ _) p.iso.hom)) := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology (diagonalSurface S)) _ _
    (ObjectProperty.FullSubcategory.property _)
  have hunit := Equiv.apply_symm_apply
    ((sheafificationAdjunction (ProEt.topology (diagonalSurface S))
      AddCommGrpCat.{u + 1}).homEquiv
      ((Functor.const (diagonalSurface S).ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion S)).obj
        ((constantSheaf (ProEt.topology (ProjectiveLine S)) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))
    (Functor.whiskerLeft (proEtaleBaseChange (diagonalImmersion S)).op
      (toSheafify (ProEt.topology (ProjectiveLine S))
        ((Functor.const (ProjectiveLine S).ProEtᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))
  change toSheafify (ProEt.topology (diagonalSurface S)) _ ≫
    (proEtaleConstantDirectImageMap (diagonalImmersion S) AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom = _ at hunit
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    ← Category.assoc, hunit]
  ext U k
  let M := coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))
  let e := (g.ordinaryPushEvaluation n).app M
  have hinj : Function.Injective (e.hom.val.app U) := by
    apply Function.LeftInverse.injective (g := e.inv.val.app U)
    intro z
    exact congrArg (fun a ↦ a.val.app U z) e.hom_inv_id
  apply hinj
  apply eq_of_heq
  have h1 := (finiteSupportedQuotient_existsUnique l E g n).exists.choose_spec U k
  have hx := (finiteQuotient_existsUnique l E (diagonalSurface S) n).exists.choose_spec U k
  have h2 := p.normalization n U _ _ hx.symm
  have h3 := map_intCast ((proEtaleConstantDirectImageMap.{u, u + 2} (diagonalImmersion S)
    CommRingCat.{u + 1} (CommRingCat.of.{u + 1}
      (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app U).hom k.down
  exact h1.trans ((h2.trans (heq_of_eq h3)).symm)

/-- Integer and scalar generators evaluate to the finite integer quotient. -/
theorem finiteEvaluation_generators_eq_finiteQuotient {T : Scheme.{u}} (c : Chern l E T) (n : ℕ) :
    (abEvaluation T n).map (integerGenerator T (Rrings l T) c.reduction.forget) ≫
      (c.reduction.forget.F ⋙ abEvaluation T n).map (scalarGenerator l E T) ≫
      (finiteScalarForgetIso l E c n).hom.app (coefficient T (Arings l E T)) =
      finiteQuotient l E T n := by
  apply (finiteQuotient_existsUnique l E T n).unique ?_
    (finiteQuotient_existsUnique l E T n).exists.choose_spec
  intro U k
  let x : (coefficient T (Rrings l T)).val.obj (op (n, U.unop)) :=
    (k.down : ((Rrings l T).obj (op n)).obj.obj U)
  have hx := (integerGenerator_existsUnique T (Rrings l T)
    c.reduction.forget).exists.choose_spec n U k
  have hf := finiteBoundary_forgetMapSection T _ c.reduction.forget
    (scalarGenerator l E T) n U x _ hx
  have hs := (scalarGenerator_existsUnique l E T).exists.choose_spec (op (n, U.unop)) x
  have hy := hf.trans (hs.trans (heq_of_eq (map_intCast
    ((coefficientSystemMap l E T).hom.app (op (n, U.unop))).hom k.down)))
  exact (finiteScalarForgetIso_section l E c n (coefficient T (Arings l E T)) U _ _ hy).heq
end

end AlgebraicGeometry.ProEtale.SpTowerClasses
