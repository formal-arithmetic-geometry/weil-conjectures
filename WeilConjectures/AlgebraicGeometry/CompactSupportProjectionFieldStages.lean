/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleProjectionMates
import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionIntegralStages
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Tactic.Convert
import all Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.RationalProjectionComparisonEquations
import WeilConjectures.AlgebraicGeometry.CommonProjectionComparisonEquations

/-! # Field coefficient projection laws

The field part of the compact-support projection formula.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u v w v' w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures

section Transport
variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
  {P : SixFunctorPushStage D B} {P' : SixFunctorPushStage D B'}
  {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
  {Q : SixFunctorCompactifiedSquare D}
  {A : SixFunctorExchangeData P T Q} {A' : SixFunctorExchangeData P' T' Q}
  {V : ∀ X, B X ⥤ B' X} {c : SixFunctorCoefficientComparison P P' V}

private theorem coefficient_projection_isIso (e : SixFunctorExchangeComparison A A' V c)
    (K : B Q.X) (L : B Q.Y) [IsIso (A.projectionComponent K L)] :
    IsIso (A'.projectionComponent ((V Q.X).obj K) ((V Q.Y).obj L)) := by
  let es := (Functor.uncurry.obj (T' Q.Y)).mapIso
    (Iso.prod ((c.supportAdjunction Q.f Q.compactification).left.app K)
      (Iso.refl ((V Q.Y).obj L)))
  have : IsIso ((Functor.uncurry.obj (T' Q.Y)).map
      (Prod.mkHom ((c.supportAdjunction Q.f Q.compactification).left.hom.app K)
        (𝟙 ((V Q.Y).obj L)))) := show IsIso es.hom from inferInstance
  let et := (P'.support Q.f Q.compactification).mapIso
    ((Functor.uncurry.obj (T' Q.X)).mapIso
      (Iso.prod (Iso.refl ((V Q.X).obj K)) ((c.directAdjunction Q.f).left.app L).symm) ≪≫
      ((e.tensor Q.X).app (K, (P.pull Q.f).obj L)).symm)
  have : IsIso ((P'.support Q.f Q.compactification).map
      ((Functor.uncurry.obj (T' Q.X)).map
        (Prod.mkHom (𝟙 ((V Q.X).obj K)) ((c.directAdjunction Q.f).left.inv.app L)) ≫
        (e.tensor Q.X).inv.app (K, (P.pull Q.f).obj L))) :=
    show IsIso et.hom from inferInstance
  have h := eq_of_heq (e.projection K L)
  have hi : IsIso ((V Q.Y).map (A.projectionComponent K L) ≫
      (c.supportAdjunction Q.f Q.compactification).left.hom.app
        (((T Q.X).obj K).obj ((P.pull Q.f).obj L))) := inferInstance
  rw [h] at hi
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hi

private theorem projection_natural (A : SixFunctorExchangeData P T Q)
    (K K' : B Q.X) (L L' : B Q.Y) (a : K ⟶ K') (b : L ⟶ L') :
    ((T Q.Y).map ((P.support Q.f Q.compactification).map a)).app L ≫
        ((T Q.Y).obj ((P.support Q.f Q.compactification).obj K')).map b ≫
        A.projectionComponent K' L' =
      A.projectionComponent K L ≫ (P.support Q.f Q.compactification).map
        (((T Q.X).map a).app ((P.pull Q.f).obj L) ≫
          ((T Q.X).obj K').map ((P.pull Q.f).map b)) := by
  let η := Functor.uncurry.map A.stage.projection
  have hs : (P.support Q.f Q.compactification).prod (𝟭 (B Q.Y)) ⋙
      Functor.uncurry.obj (T Q.Y) =
      Functor.uncurry.obj (A.stage.compactSupport ⋙ A.stage.tensorY) := by
    simp only [← A.tensorY, ← A.compactSupport]
    rfl
  have ht : ((𝟭 (B Q.X)).prod (P.pull Q.f) ⋙ Functor.uncurry.obj (T Q.X)) ⋙
      P.support Q.f Q.compactification = Functor.uncurry.obj
        ((Functor.postcompose₂.obj A.stage.compactSupport).obj
          ((((Functor.whiskeringLeft₂ (B Q.X)).obj (𝟭 (B Q.X))).obj
            A.stage.pull).obj A.stage.tensorX)) := by
    simp only [← A.tensorX, ← A.compactSupport, ← A.pull]
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro M
      rfl
    intro M M' f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    dsimp
    exact A.stage.compactSupport.map_comp _ _
  let η' := (eqToHom hs) ≫ η ≫ (eqToHom ht.symm)
  have hc : ∀ K L, η'.app (K, L) = A.projectionComponent K L := by
    intro K L
    simp only [η', NatTrans.comp_app, eqToHom_app, η, Functor.uncurry_map_app,
      SixFunctorExchangeData.projectionComponent]
  simpa only [hc, Functor.comp_map, Functor.prod_map, Functor.id_map,
    Functor.uncurry_obj_map, Functor.prod_obj, Functor.id_obj, Category.assoc]
    using η'.naturality (Prod.mkHom a b)

private theorem projection_isIso_of_iso (A : SixFunctorExchangeData P T Q)
    {K K' : B Q.X} {L L' : B Q.Y} (a : K ≅ K') (b : L ≅ L')
    [IsIso (A.projectionComponent K' L')] : IsIso (A.projectionComponent K L) := by
  have h := projection_natural A K K' L L' a.hom b.hom
  have hi : IsIso
      (((T Q.Y).map ((P.support Q.f Q.compactification).map a.hom)).app L ≫
        ((T Q.Y).obj ((P.support Q.f Q.compactification).obj K')).map b.hom ≫
        A.projectionComponent K' L') := inferInstance
  rw [h] at hi
  simpa only [isIso_comp_right_iff] using hi

end Transport

private theorem coherence_of_laws {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
    {P : SixFunctorPushStage D B} {T : ∀ X, B X ⥤ B X ⥤ B X}
    {A : ∀ Q : SixFunctorCompactifiedSquare D, SixFunctorExchangeData P T Q}
    {Q : ∀ X, ObjectProperty (B X)} (h : CompactSupportProjectionLaws P T A Q) :
    CompactSupportProjectionCoherence P T A Q :=
  ⟨h.compactification, h.composition, h.pentagon, h.proper⟩

private theorem integral_finiteTor {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (X : SixFunctorSpace D)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    finiteTorConstructibleIntegral C.l E X.obj.left K.obj := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : ∀ x : X.obj.left, Invertible (C.l : X.obj.left.residueField x) := fun x ↦
    let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ X.obj.hom.appTop ≫
      X.obj.left.Γevaluation x).hom
    (Eq.mp (congrArg IsUnit (map_natCast φ C.l))
      ((isUnit_iff_ne_zero.mpr
        (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : C.l.Prime)
          C.different.symm)).map φ)).invertible
  rw [← (integral_residue_tor D C.l C.different E X.obj.left).2]
  exact K.property

private theorem rational_projection_isIso {D : FiniteFieldDatum.{u}}
    {C : D.CoefficientDatum} {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    (hH : CompactSupportProjectionLaws H.integral H.integralTensor H.integralExchange
      (fun X K ↦ finiteTorConstructibleIntegral C.l E X.obj.left K.obj))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : sfRationalConstructibleCategory C.l E X.obj.left)
    (L : sfRationalConstructibleCategory C.l E Y.obj.left) :
    IsIso (compactSupportProjectionComponent H.rationalExchange f c K L) := by
  have : IsIso ((H.integralExchange (compactSupportProjectionSquare f c)).projectionComponent
      K.obj L.obj) := hH.isIso f c K.obj L.obj (integral_finiteTor Y L.obj)
  exact coefficient_projection_isIso
    (H.rationalExchangeComparison (compactSupportProjectionSquare f c)) K.obj L.obj

private theorem rational_projection_laws {D : FiniteFieldDatum.{u}}
    {C : D.CoefficientDatum} {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (H : SixFunctorHigherOperations D C E)
    (hH : CompactSupportProjectionLaws H.integral H.integralTensor H.integralExchange
      (fun X K ↦ finiteTorConstructibleIntegral C.l E X.obj.left K.obj)) :
    CompactSupportProjectionLaws H.rational H.rationalTensor H.rationalExchange
      (fun _ _ ↦ True) := by
  have hc := compactSupportProjectionCoherence_rational H (coherence_of_laws hH)
  refine ⟨?_, ?_, hc.compactification, hc.composition, hc.pentagon, hc.proper⟩
  · intro X Y f _ _ _ c K L _
    exact rational_projection_isIso H hH f c K L
  · intro X Y f _ _ _ c K K' L L' _ _ a b
    exact projection_natural (H.rationalExchange (compactSupportProjectionSquare f c))
      K K' L L' a b

private theorem common_projection_isIso {D : FiniteFieldDatum.{u}}
    {C : D.CoefficientDatum} (H : SixFunctorCommonStages D C)
    (hH : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      CompactSupportProjectionLaws (H.coefficientStages E₀).rational
        (H.coefficientStages E₀).rationalTensor (H.coefficientStages E₀).rationalExchange
        (fun _ _ ↦ True))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left)
    (K : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar X.obj.left)
    (L : generalAlgebraicallyClosedConstructibleCategory C.l C.Qbar Y.obj.left) :
    IsIso (compactSupportProjectionComponent H.commonStageExchange f c K L) := by
  let E₀ := Padic.finiteCoefficientCompositum C.l C.Qbar K.stage L.stage
  have hK : K.stage ≤ E₀ :=
    ((Padic.finiteCoefficientFields_properties C.l C.Qbar).1 K.stage L.stage).1
  have hL : L.stage ≤ E₀ :=
    ((Padic.finiteCoefficientFields_properties C.l C.Qbar).1 K.stage L.stage).2
  have : IsIso ((sixFunctorCoefficientExchange D C H.coefficientStages E₀
      (compactSupportProjectionSquare f c)).projectionComponent
      (K.toStage hK) (L.toStage hL)) := by
    convert (hH E₀).isIso f c (K.toStage hK) (L.toStage hL) trivial using 0
    rfl
  have : IsIso ((H.commonStageExchange (compactSupportProjectionSquare f c)).projectionComponent
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left).ι E₀).obj
        (K.toStage hK))
      (((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar Y.obj.left).ι E₀).obj
        (L.toStage hL))) := by
    exact coefficient_projection_isIso
      (H.commonStageExchangeComparison E₀ (compactSupportProjectionSquare f c))
      (K.toStage hK) (L.toStage hL)
  exact projection_isIso_of_iso (H.commonStageExchange (compactSupportProjectionSquare f c))
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar X.obj.left).isoToStage K hK)
    ((GeneralAlgebraicallyClosedCoefficients.stageSystem C.l C.Qbar Y.obj.left).isoToStage L hL)

/-- The projection laws for rational and common finite-field coefficient stages.
Source: fix-prop-projection-formula.proof.md in
literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-pf-done;
field transport and coherence steps.
(blueprint: lem-sf-projection-field-stage-laws).
Proof: uncurry the specified projection mate to prove two-input naturality.
The coefficient projection square carries an integral inverse to a rational
inverse after cancellation of its endpoint isomorphisms. Every rational object
has a literal integral model, and the residue Tor criterion makes the second
model admissible. Apply this to the original field and every coefficient field
in the closure. At the common stage, present both inputs over their finite
coefficient compositum, use the rational inverse there, then use naturality
along the two presentation isomorphisms. Transport the four comparison
equations separately through rational localization and common-stage inclusion,
and assemble these with the proved invertibility and naturality fields. -/
theorem compactSupportProjectionFormula_fieldStages
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) :
    CompactSupportProjectionLaws S.higher.rational S.higher.rationalTensor
      S.higher.rationalExchange (fun _ _ ↦ True) ∧
    CompactSupportProjectionLaws S.closure.commonStage S.closure.commonStageTensor
      S.closure.commonStageExchange (fun _ _ ↦ True) ∧
    ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      CompactSupportProjectionLaws (S.closure.coefficientStages E₀).rational
        (S.closure.coefficientStages E₀).rationalTensor
        (S.closure.coefficientStages E₀).rationalExchange (fun _ _ ↦ True) := by
  obtain ⟨hI, hIE⟩ := compactSupportProjectionFormula_integralStages S
  have hR := rational_projection_laws S.higher hI
  have hE : ∀ E₀ : Padic.FiniteCoefficientFields C.l C.Qbar,
      CompactSupportProjectionLaws (S.closure.coefficientStages E₀).rational
        (S.closure.coefficientStages E₀).rationalTensor
        (S.closure.coefficientStages E₀).rationalExchange (fun _ _ ↦ True) :=
    fun E₀ ↦ rational_projection_laws (S.closure.coefficientStages E₀) (hIE E₀)
  have hc := compactSupportProjectionCoherence_common S.closure
    (fun E₀ ↦ coherence_of_laws (hE E₀))
  refine ⟨hR, ⟨?_, ?_, hc.compactification, hc.composition, hc.pentagon, hc.proper⟩, hE⟩
  · intro X Y f _ _ _ c K L _
    exact common_projection_isIso S.closure hE f c K L
  · intro X Y f _ _ _ c K K' L L' _ _ a b
    exact projection_natural (S.closure.commonStageExchange (compactSupportProjectionSquare f c))
      K K' L L' a b

end WeilConjectures
