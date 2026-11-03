/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteReductionPullbackSupplement
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProetaleSiteProperties
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt
import WeilConjectures.Algebra.Homology.System.SystemScalarGenerators
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearNaturalIsoAssembly
import all WeilConjectures.AlgebraicGeometry.SemilinearSystemModels

/-! # Normalized IntegralTowerOrdinaryPullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem coefficientPoint_mate
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
      ((upperStarFromPointComp f).app A).hom = condensedPushforwardHom A f := by
  rw [Adjunction.homEquiv_unit]
  rfl

private abbrev uniformizerScalar (s : Coefficients l E) (T : Scheme.{u}) (n : ℕ) :=
  (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((s.reduction T).coefficient.hom ≫
        completedIntegralCommRingProjectionUnrestricted l E T n)

private noncomputable local instance fixedCommRingSheafify (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} T

private theorem sheafification_extension_unit
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {D : Type*} [Category D] [HasWeakSheafify J D]
    (P : Cᵒᵖ ⥤ D) (F : Sheaf J D) (a : P ⟶ F.obj) :
    toSheafify J P ≫ (((sheafificationAdjunction J D).homEquiv P F).symm a).hom = a := by
  exact ((sheafificationAdjunction J D).homEquiv P F).apply_symm_apply a

private theorem sheafification_hom_ext
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    {D : Type*} [Category D] [HasWeakSheafify J D]
    (P : Cᵒᵖ ⥤ D) (F : Sheaf J D)
    (a b : (presheafToSheaf J D).obj P ⟶ F)
    (h : toSheafify J P ≫ a.hom = toSheafify J P ≫ b.hom) : a = b := by
  exact ((sheafificationAdjunction J D).homEquiv P F).injective h

attribute [local irreducible] sheafificationAdjunction in
private theorem direct_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : CommRingCat.{u + 1}) (V : Y.ProEtᵒᵖ) :
    (toSheafify (Scheme.ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app V ≫
        (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app V =
      (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
        ((Scheme.proEtaleBaseChange f).op.obj V) := by
  exact congrArg (fun a ↦ a.app V)
    (sheafification_extension_unit (Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj A)
      ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj A))
      (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A))))

attribute [local irreducible] sfbConstantRingAbIso finiteMate
  Scheme.proEtaleConstantDirectImageMap

private theorem finiteMate_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Type u) [CommRing R] :
    finiteMate f R =
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
          forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} R))) := by
  let A := CommRingCat.of (ULift.{u + 1} R)
  let cY := sfbConstantRingAbIso Y A
  apply (cancel_epi cY.inv).mp
  apply sheafification_hom_ext (Scheme.ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj (AddCommGrpCat.of A))
    ((f)_*[Ab.{u + 1}].obj (finiteAbSheaf X R))
  apply NatTrans.ext
  funext U
  ext r
  change (finiteMate f R).hom.app U
      (cY.inv.hom.app U
        ((toSheafify (Scheme.ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app U r)) = _
  have hy : cY.inv.hom.app U
      ((toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app U r) =
      ((toSheafify (Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj A)).app U r) := by
    rw [← constantRingAb_unit Y A U r]
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun t ↦ t.hom) cY.hom_inv_id) U) _
  change (finiteMate f R).hom.app U _ =
    (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A).hom.app U
      (cY.inv.hom.app U
        ((toSheafify (Scheme.ProEt.topology Y)
          ((Functor.const Y.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app U r))
  rw [hy, finiteMate_unit]
  exact (congrArg (fun k ↦ k r) (direct_unit f A U)).symm


private theorem uniformizerScalar_eq (s : Coefficients l E) (T : Scheme.{u}) (n : ℕ) :
    (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (uniformizerScalar l E s T n) =
    (spIntegralAbComparison l E T).hom ≫
      (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (limit.π (integralCoefficientSheafSystem l E T) (op n)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  ext x
  change (limit.π (integralCoefficientSheafSystem l E T) (op n)).hom.app U
      ((s.reduction T).coefficient.hom.hom.app U x) =
    (limit.π (integralCoefficientSheafSystem l E T) (op n)).hom.app U
      ((spIntegralAbComparison l E T).hom.hom.app U x)
  exact congrArg ((limit.π (integralCoefficientSheafSystem l E T) (op n)).hom.app U)
    ((s.reduction T).coefficient_normalized U x)


private abbrev canonicalProjection (T : Scheme.{u}) (n : ℕ) :=
  (spIntegralAbComparison l E T).hom ≫
    (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (limit.π (integralCoefficientSheafSystem l E T) (op n))

private theorem canonicalProjection_apply (T : Scheme.{u}) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((coefficientRing T (sfbCondensedIntegers l E)).X).obj.obj U) :
    (canonicalProjection l E T n).hom.app U x =
      (limit.π (integralCoefficientSheafSystem l E T) (op n)).hom.app U
        ((spIntegralAbComparison l E T).hom.hom.app U x) := by
  rfl


private abbrev comparisonProjection (T : Scheme.{u}) (n : ℕ)
    (e : (coefficientRing T (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E T) :=
  e.hom ≫ (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (limit.π (integralCoefficientSheafSystem l E T) (op n))

private theorem comparisonProjection_apply (T : Scheme.{u}) (n : ℕ)
    (e : (coefficientRing T (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E T)
    (U : T.ProEtᵒᵖ) (x : ((coefficientRing T (sfbCondensedIntegers l E)).X).obj.obj U) :
    (comparisonProjection l E T n e).hom.app U x =
      (limit.π (integralCoefficientSheafSystem l E T) (op n)).hom.app U
        (e.hom.hom.app U x) := by
  rfl


private theorem canonicalIntegralComparison (T : Scheme.{u}) :
    SfbIntegralComparison l E T (spIntegralAbComparison l E T) := by
  let H := sfb_integral_coefficient_limit l E T
  have h := H.choose_spec.choose_spec.choose_spec
  have he := h.2.2.2.2.2.choose_spec.1
  exact ⟨he.1, he.2.1, H.choose, H.choose_spec.choose,
    H.choose_spec.choose_spec.choose, h.1, h.2.1, he.2.2⟩


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 1600000 in
-- The finite-label coefficient presentations need additional kernel conversion steps.
private def ProjectionNaturality {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (eX : (coefficientRing X (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E X)
    (eY : (coefficientRing Y (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E Y)
    : Prop :=
  (f)^*[Ab.{u + 1}].map (comparisonProjection l E Y n eY) ≫
    (sfbFiniteCoefficientPullbackIso l E f n).hom =
      ((upperStarFromPointComp f).app (sfbCondensedIntegers l E).X).hom ≫
        comparisonProjection l E X n eX


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 1600000 in
-- The finite-label coefficient presentations need additional kernel conversion steps.
private theorem comparisonProjection_natural {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (eX : (coefficientRing X (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E X)
    (eY : (coefficientRing Y (sfbCondensedIntegers l E)).X ≅ sfbCompletedIntegersAb l E Y)
    (hX : SfbIntegralComparison l E X eX) (hY : SfbIntegralComparison l E Y eY) :
    ProjectionNaturality l E f n eX eY := by
  rcases hX.2.2 with ⟨aX, qX, jX, hjX, _, hnX⟩
  rcases hY.2.2 with ⟨aY, qY, jY, hjY, _, hnY⟩
  unfold ProjectionNaturality
  have hq : jY.hom ≫ qY.π.app (op n) = jX.hom ≫ qX.π.app (op n) := by
    ext x
    exact (hjY n x).trans (hjX n x).symm
  have hr := sfb_finite_reduction_pullback l E f n aX aY
    (jX.hom ≫ qX.π.app (op n)) (comparisonProjection l E X n eX)
    (comparisonProjection l E Y n eY)
    (fun S g ↦ (congrArg
      ((sfbIntegralFiniteRepresentation l E X aX n).hom.app
        (op ((profiniteToProEtOf X).obj S)))
      (comparisonProjection_apply l E X n eX (op ((profiniteToProEtOf X).obj S))
        (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
          (op S) (ULift.up g.hom.hom)))).trans (hnX S g n))
    (fun S g ↦ ((congrArg
      ((sfbIntegralFiniteRepresentation l E Y aY n).hom.app
        (op ((profiniteToProEtOf Y).obj S)))
      (comparisonProjection_apply l E Y n eY (op ((profiniteToProEtOf Y).obj S))
        (((sfbIntegralPointAdjunction Y).unit.app (sfbCondensedIntegers l E).X).hom.app
          (op S) (ULift.up g.hom.hom)))).trans (hnY S g n)).trans
      (congrArg (fun q ↦ ULift.up ((profiniteToProEtOf Y).map (g ≫ q))) hq))
  exact hr


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 1600000 in
-- The coefficient-limit normalizations require comparing the represented sections.
private theorem canonicalProjection_natural
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
      ((f)^*[Ab.{u + 1}].map (canonicalProjection l E Y n) ≫
        (sfbFiniteCoefficientPullbackIso l E f n).hom) =
      condensedPushforwardHom (spIntegralCondensed l E) f ≫
        (f)_*[Ab.{u + 1}].map (canonicalProjection l E X n) := by
  have h := comparisonProjection_natural l E f n (spIntegralAbComparison l E X)
    (spIntegralAbComparison l E Y) (canonicalIntegralComparison l E X)
    (canonicalIntegralComparison l E Y)
  unfold ProjectionNaturality at h
  exact (congrArg ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _) h).trans
    (((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv_naturality_right _ _).trans
      (congrArg (fun t ↦ t ≫ (f)_*[Ab.{u + 1}].map (canonicalProjection l E X n))
        (coefficientPoint_mate (spIntegralCondensed l E) f)))



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem projection_natural (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
      ((f)^*[Ab.{u + 1}].map
        ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (uniformizerScalar l E s Y n)) ≫
        (sfbFiniteCoefficientPullbackIso l E f n).hom) =
      condensedPushforwardHom (spIntegralCondensed l E) f ≫
        (f)_*[Ab.{u + 1}].map
          ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
            (uniformizerScalar l E s X n)) := by
  exact (congrArg (fun r ↦ (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _
      ((f)^*[Ab.{u + 1}].map r ≫ (sfbFiniteCoefficientPullbackIso l E f n).hom))
    (uniformizerScalar_eq l E s Y n)).trans
    ((canonicalProjection_natural l E f n).trans
      (congrArg (fun r ↦ condensedPushforwardHom (spIntegralCondensed l E) f ≫
        (f)_*[Ab.{u + 1}].map r) (uniformizerScalar_eq l E s X n).symm))



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem uniformizerSquare (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    uniformizerScalar l E s Y n ≫
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) =
      InternalModuleOperations.coefficientMap (spIntegralCondensed l E) f ≫
        ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (uniformizerScalar l E s X n) := by
  apply (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map_injective
  have h := projection_natural l E s f n
  have hm := (finiteCoefficient_mate l E f n).trans
    (finiteMate_eq f (Padic.coefficientExtensionRing l E (n + 1)))
  have he := (upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv_naturality_left
    ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (uniformizerScalar l E s Y n)) (sfbFiniteCoefficientPullbackIso l E f n).hom
  have he' := he.trans (congrArg
    (fun a ↦ ((sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (uniformizerScalar l E s Y n)) ≫ a) hm)
  have h := he'.symm.trans h
  ext U x
  have hh := congrArg (fun a ↦ a.hom.app U x) h
  change _ = ((uniformizerScalar l E s X n).hom.app
    (op ((Scheme.proEtaleBaseChange f).obj U.unop)))
      (((InternalModuleOperations.coefficientMap (spIntegralCondensed l E) f).hom.app U) x)
  exact hh.trans (congrArg
    ((uniformizerScalar l E s X n).hom.app
      (op ((Scheme.proEtaleBaseChange f).obj U.unop)))
    (InternalModuleOperations.coefficientMap_apply (spIntegralCondensed l E) f U x).symm)


private theorem constantDirect_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map a ≫
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} B =
    Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A ≫
      (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
        ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  apply (sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv _ _
    |>.injective
  dsimp only [constantSheaf, Functor.comp_map]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  erw [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply,
    Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  exact congrArg (fun k ↦ k.app ((Scheme.proEtaleBaseChange f).op.obj V))
    ((sheafificationAdjunction (Scheme.ProEt.topology X) CommRingCat.{u + 1}).unit.naturality
      ((Functor.const X.ProEtᵒᵖ).map a))

private abbrev scalarProjection (s : Coefficients l E) (T : Scheme.{u}) (n : ℕ) :=
  (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (spIntegralReductionScalar l E T (s.reduction T).coefficient n)



private def ellQuotientFactor (n k : ℕ)
    (hk : Padic.coefficientExtensionIdeal l E (k + 1) ≤ spEllIdeal l E ^ (n + 1)) :
    CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (k + 1))) ⟶
      CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n)) :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factor hk).comp ULift.ringEquiv.toRingHom))

private theorem ellProjection_factor (T : Scheme.{u}) (n k : ℕ)
    (hk : Padic.coefficientExtensionIdeal l E (k + 1) ≤ spEllIdeal l E ^ (n + 1)) :
    spCompletedEllCommProjection.{u} l E T n =
      completedIntegralCommRingProjectionUnrestricted.{u, u} l E T k ≫
        (constantSheaf.{u, u + 1, u + 1, u + 2}
          (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map
          (ellQuotientFactor.{u} l E n k hk) := by
  let F := sheafCompose (Scheme.ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  apply F.map_injective
  apply completedIntegralFiniteQuotientHom_ext.{u, u} l E T
    (spEllIdeal l E ^ (n + 1)) ⟨k, hk⟩
  · dsimp only [F, spCompletedEllCommProjection]
    try unfold spIntegralEllProjection
    rw [Functor.map_preimage]
    exact (sp_completed_coefficient_limit.{u, u} l E T).exists.choose_spec n
  · rw [Functor.map_comp, ← Category.assoc]
    change (integralConstantToCompletionOfUniverses.{u, u} l E T ≫
        limit.π (integralCoefficientSheafSystem.{u, u} l E T) (op k)) ≫ _ = _
    dsimp only [integralConstantToCompletionOfUniverses]
    erw [limit.lift_π]
    change integralConstantQuotientOfUniverses.{u, u} l E T k ≫ _ = _
    unfold integralConstantQuotientOfUniverses
    rw [← F.map_comp, ← Functor.map_comp]
    congr 2

private theorem ellSquare (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    scalarProjection l E s Y n ≫
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n)))) =
      InternalModuleOperations.coefficientMap (spIntegralCondensed l E) f ≫
        ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (scalarProjection l E s X n) := by
  obtain ⟨k, hk⟩ := (sp_coefficient_ideals_cofinal l E).2 (n + 1)
  have hk' : Padic.coefficientExtensionIdeal l E (k + 1) ≤
      spEllIdeal l E ^ (n + 1) := (Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk
  let a := ellQuotientFactor l E n k hk'
  have hp (T : Scheme.{u}) : scalarProjection l E s T n =
      uniformizerScalar l E s T k ≫
        (sheafCompose (Scheme.ProEt.topology T)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}).map a) := by
    change (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((s.reduction T).coefficient.hom ≫ spCompletedEllCommProjection l E T n) = _
    rw [ellProjection_factor l E T n k hk',
      ← Category.assoc, Functor.map_comp]
  rw [hp X, hp Y, Functor.map_comp]
  rw [Category.assoc]
  have hn := congrArg
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map)
    (constantDirect_naturality f a)
  simp only [Functor.map_comp] at hn
  rw [hn, ← Category.assoc, uniformizerSquare, Category.assoc]
  rfl
private abbrev scalarFunctor (s : Coefficients l E) (T : Scheme.{u}) (n : ℕ) :=
  DerivedChangeOfRingsCochainModel.E.{u + 1, u, u + 1, u + 2, u + 2}
    (scalar l E s T n).model

private abbrev finiteMap {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (Scheme.proEtaleRingDirectImageMap f (SpTowerShriek.B l E Y n)
        (SpTowerShriek.B l E X n)
        (Scheme.proEtaleConstantRingComparison f (SpTowerShriek.R l E n)))


private theorem finiteDirect_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    Scheme.proEtaleRingDirectImageMap f (Scheme.proEtaleConstantRing Y A)
      (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRingComparison f A) =
    Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of (ULift.{u + 1} A)) := by
  change (Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _
    (Scheme.proEtaleCoefficientInverseImageMap f A) = _
  unfold Scheme.proEtaleCoefficientInverseImageMap Scheme.proEtaleConstantInverseImageMap
  rw [← Adjunction.homEquiv_symm_apply, Equiv.apply_symm_apply]


private theorem finiteSquare (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    scalarProjection l E s Y n ≫ finiteMap l E f n =
      InternalModuleOperations.coefficientMap (spIntegralCondensed l E) f ≫
        ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (scalarProjection l E s X n) := by
  simpa only [finiteMap, SpTowerShriek.B, finiteDirect_eq] using ellSquare l E s f n


private def pushRestrictionIso
    {C : Type*} [Category C] {D : Type*} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    {R₀ R₁ : Sheaf K RingCat.{u + 1}} {S₀ S₁ : Sheaf J RingCat.{u + 1}}
    (qR : R₀ ⟶ R₁) (qS : S₀ ⟶ S₁)
    (φ₀ : S₀ ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R₀)
    (φ₁ : S₁ ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R₁)
    (h : qS ≫ φ₁ = φ₀ ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).map qR) :
    restrictScalars.{u + 1} qR ⋙ pushforward φ₀ ≅
      pushforward φ₁ ⋙ restrictScalars qS :=
  pushforwardComp (G := 𝟭 D) φ₀ qR ≪≫ pushforwardCongr h.symm ≪≫
    (pushforwardComp (F := 𝟭 C) qS φ₁).symm

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def sectionComparison (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (h : scalarProjection l E s Y n ≫ finiteMap l E f n =
      InternalModuleOperations.coefficientMap (spIntegralCondensed l E) f ≫
        ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (scalarProjection l E s X n)) :
    InternalModuleOperations.upperStar (spIntegralCondensed l E) f ⋙
      (scalarFunctor l E s X n) ≅
    (scalarFunctor l E s Y n) ⋙
      Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f := by
  let e := pushRestrictionIso
    (Scheme.proEtaleBaseChange f) (scalarProjection l E s X n) (scalarProjection l E s Y n)
    (InternalModuleOperations.coefficientMap (spIntegralCondensed l E) f)
    (finiteMap l E f n) h
  exact ((InternalModuleOperations.adjunction (spIntegralCondensed l E) f).comp
      (scalar l E s X n).ordinaryAdj).leftAdjointUniq
    (((scalar l E s Y n).ordinaryAdj.comp
      (Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f)).ofNatIsoRight
        e.symm)


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem sectionComparison_unit (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (h : scalarProjection l E s Y n ≫ finiteMap l E f n =
      InternalModuleOperations.coefficientMap (spIntegralCondensed l E) f ≫
        ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (scalarProjection l E s X n))
    (M : spIntegralSectionModules l E Y) (V : Y.ProEt) (x : M.val.obj (op V)) :
    ((sectionComparison l E s f n h).hom.app M).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V))
      (systemModelTmul (scalar l E s X n).model
        ((InternalModuleOperations.upperStar (spIntegralCondensed l E) f).obj M)
        (op ((Scheme.proEtaleBaseChange f).obj V)) 1
        (((InternalModuleOperations.adjunction (spIntegralCondensed l E) f).unit.app M).val.app
          (op V) x)) =
      (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
        ((scalarFunctor l E s Y n).obj M)).val.app (op V))
        (systemModelTmul (scalar l E s Y n).model M (op V) 1 x) := by
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    ((InternalModuleOperations.adjunction (spIntegralCondensed l E) f).comp
      (scalar l E s X n).ordinaryAdj)
    (((scalar l E s Y n).ordinaryAdj.comp
      (Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f)).ofNatIsoRight
        (pushRestrictionIso
          (Scheme.proEtaleBaseChange f) (scalarProjection l E s X n) (scalarProjection l E s Y n)
          (InternalModuleOperations.coefficientMap (spIntegralCondensed l E) f)
          (finiteMap l E f n) h).symm) M
  have hh := congrArg (fun k ↦ k.val.app (op V) x) hu
  with_unfolding_all change (((sectionComparison l E s f n h).hom.app M).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V))
      (((scalar l E s X n).ordinaryAdj.unit.app _).val.app _
        (((InternalModuleOperations.adjunction (spIntegralCondensed l E) f).unit.app M).val.app
          (op V) x)) =
      (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
        ((scalarFunctor l E s Y n).obj M)).val.app (op V))
        (((scalar l E s Y n).ordinaryAdj.unit.app M).val.app (op V) x)) at hh
  erw [(scalar l E s X n).unit_normalized, (scalar l E s Y n).unit_normalized] at hh
  exact hh


private theorem upperComparison_unit
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules l E Y) (V : Y.ProEt)
    (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)) :
    (((InternalModuleOperations.upperComparison (spIntegralCondensed l E) f).hom.app M).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V)))
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
        M).hom.hom.app (op V) x) =
      (((InternalModuleOperations.adjunction (spIntegralCondensed l E) f).unit.app
        ((spIntegralModuleEquivalence l E Y).functor.obj M)).val.app (op V) x) := by
  have hu := ((InternalModuleOperations.internal_module_operations_transport
    (spIntegralCondensed l E)).2.1 f).2.1 M
  have hh := congrArg (fun k ↦ k.val.app (op V) x) hu
  change (((InternalModuleOperations.upperComparison (spIntegralCondensed l E) f).hom.app M).val.app
    (op ((Scheme.proEtaleBaseChange f).obj V)))
    (((InternalModuleOperations.lowerComparison (spIntegralCondensed l E) f).hom.app
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M)).val.app (op V)
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
        M).hom.hom.app (op V) x)) = _ at hh
  have he := (InternalModuleOperations.lowerComparison_existsUnique
    (spIntegralCondensed l E) f).exists.choose_spec
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M) (op V)
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
        M).hom.hom.app (op V) x)
  exact (congrArg
    (((InternalModuleOperations.upperComparison (spIntegralCondensed l E) f).hom.app M).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V))) he.symm).trans hh


private def ordinaryFiniteComparison (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (h : scalarProjection l E s Y n ≫ finiteMap l E f n =
      InternalModuleOperations.coefficientMap (spIntegralCondensed l E) f ≫
        ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (scalarProjection l E s X n)) :
    CondensedRing.upperStar (spIntegralCondensed l E) f ⋙ ordinaryLevel l E s X n ≅
      ordinaryLevel l E s Y n ⋙
        Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (InternalModuleOperations.upperComparison (spIntegralCondensed l E) f) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sectionComparison l E s f n h) ≪≫
    (Functor.associator _ _ _).symm


private theorem ordinaryFiniteComparison_unit (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (h : scalarProjection l E s Y n ≫ finiteMap l E f n =
      InternalModuleOperations.coefficientMap (spIntegralCondensed l E) f ≫
        ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
            (scalarProjection l E s X n))
    (M : Modules l E Y) (V : Y.ProEt)
    (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)) :
    ((ordinaryFiniteComparison l E s f n h).hom.app M).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V))
      (systemModelTmul (scalar l E s X n).model
        ((spIntegralModuleEquivalence l E X).functor.obj
          ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
        (op ((Scheme.proEtaleBaseChange f).obj V)) 1
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          M).hom.hom.app (op V) x)) =
      (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
        ((ordinaryLevel l E s Y n).obj M)).val.app (op V))
        (systemModelTmul (scalar l E s Y n).model
          ((spIntegralModuleEquivalence l E Y).functor.obj M) (op V) 1 x) := by
  dsimp only [ordinaryFiniteComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id]
  change ((sectionComparison l E s f n h).hom.app
    ((spIntegralModuleEquivalence l E Y).functor.obj M)).val.app _
    (((scalarFunctor l E s X n).map
      ((InternalModuleOperations.upperComparison (spIntegralCondensed l E) f).hom.app M)).val.app
        _ _) = _
  have hm := systemScalarModel_map_tmul (scalar l E s X n)
    ((InternalModuleOperations.upperComparison (spIntegralCondensed l E) f).hom.app M)
    (op ((Scheme.proEtaleBaseChange f).obj V)) 1
    (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
      M).hom.hom.app (op V) x)
  refine (congrArg (((sectionComparison l E s f n h).hom.app
    ((spIntegralModuleEquivalence l E Y).functor.obj M)).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V))) hm).trans ?_
  have hu := upperComparison_unit l E f M V x
  exact (congrArg (fun y ↦
    ((sectionComparison l E s f n h).hom.app
      ((spIntegralModuleEquivalence l E Y).functor.obj M)).val.app
        (op ((Scheme.proEtaleBaseChange f).obj V))
        (systemModelTmul (scalar l E s X n).model
          ((InternalModuleOperations.upperStar (spIntegralCondensed l E) f).obj
            ((spIntegralModuleEquivalence l E Y).functor.obj M))
          (op ((Scheme.proEtaleBaseChange f).obj V)) 1 y)) hu).trans
    (sectionComparison_unit l E s f n h _ V x)


private abbrev transition (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  WeilConjectures.SemilinearSections.transition (Scheme.ProEt.topology T)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h

private abbrev restriction (T : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :=
  WeilConjectures.SemilinearSections.res
    (WeilConjectures.SemilinearSections.coefficientMap (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) h)

private def levelComparison (s : Coefficients l E) (e : Evaluation l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : ∀ n, CondensedRing.upperStar (spIntegralCondensed l E) f ⋙
      ordinaryLevel l E s X n ≅ ordinaryLevel l E s Y n ⋙
        Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f) (n : ℕ) :
    (CondensedRing.upperStar (spIntegralCondensed l E) f ⋙ ordinaryReduction l E s X) ⋙
      SpTowerShriek.ev l E X n ≅
    (ordinaryReduction l E s Y ⋙ (s.operations.geometry f).pull) ⋙
      SpTowerShriek.ev l E X n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ordinaryReductionEvaluation l E s e X n) ≪≫ b n ≪≫
    Functor.isoWhiskerRight (ordinaryReductionEvaluation l E s e Y n).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((s.operations.geometry f).ordinaryPullEvaluation n).symm ≪≫
    (Functor.associator _ _ _).symm


set_option maxHeartbeats 800000 in
-- Comparing the recorded module presentations requires additional reduction steps.
private theorem assembleComparison (s : Coefficients l E) (e : Evaluation l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : ∀ n, CondensedRing.upperStar (spIntegralCondensed l E) f ⋙
      ordinaryLevel l E s X n ≅ ordinaryLevel l E s Y n ⋙
        Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f)
    (ht : ∀ M {m n} (h : n ≤ m),
      (transition l E X h).app
          ((ordinaryReduction l E s X).obj
            ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M)) ≫
        (restriction l E X h).map ((levelComparison l E s e f b n).hom.app M) =
      (levelComparison l E s e f b m).hom.app M ≫
        (transition l E X h).app
          ((s.operations.geometry f).pull.obj ((ordinaryReduction l E s Y).obj M))) :
    ∃ q : OrdinaryPullComparison l E s f, ∀ M n,
      ordinaryPullLevelMap l E s e f q M n = (b n).hom.app M := by
  obtain ⟨q, hq⟩ :=
    WeilConjectures.SemilinearSections.naturalIsoOfEvaluation_exists.{u, u}
      (Scheme.ProEt.topology X) (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X)
      _ _ (levelComparison l E s e f b) ht
  refine ⟨q, ?_⟩
  intro M n
  unfold ordinaryPullLevelMap
  rw [hq M n]
  simp [levelComparison, Category.assoc]

set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
set_option maxHeartbeats 1600000 in
-- Comparing the recorded sheaf-module presentations requires additional reduction steps.
set_option synthInstance.maxHeartbeats 200000 in
-- Elaborating the fixed internal/section and sequence-site coordinates needs this budget.
private theorem scalar_geometric_hom_ext (s : Coefficients l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules l E Y) (n : ℕ)
    (N : Scheme.proEtaleRingModules X (SpTowerShriek.B l E X n))
    (a b : (ordinaryLevel l E s X n).obj
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M) ⟶ N)
    (h : ∀ (V : Y.ProEt)
      (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)),
      a.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (systemModelTmul ((s.towers X).scalar
          (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
          ((spIntegralModuleEquivalence l E X).functor.obj
            ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
          (op ((Scheme.proEtaleBaseChange f).obj V)) 1
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op V) x)) =
      b.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (systemModelTmul ((s.towers X).scalar
          (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
          ((spIntegralModuleEquivalence l E X).functor.obj
            ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
          (op ((Scheme.proEtaleBaseChange f).obj V)) 1
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op V) x))) : a = b := by
  let A := (s.towers X).scalar
    (spIntegralReductionScalar l E X (s.reduction X).coefficient n)
  apply (A.ordinaryAdj.homEquiv _ N).injective
  apply geometric_hom_ext l E f M
  intro V x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change a.val.app _ ((A.ordinaryAdj.unit.app _).val.app _ _) =
    b.val.app _ ((A.ordinaryAdj.unit.app _).val.app _ _)
  rw [A.unit_normalized]
  exact h V x

private theorem transition_formula (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n)
    (M : SpTowerShriek.S l E T) (U : T.ProEtᵒᵖ) :
    HEq (fun x ↦ ((transition l E T h).app M).val.app U x)
      (fun x : M.val.obj (op (n, U.unop)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) :=
  (WeilConjectures.SemilinearSections.transition_exists.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (SpTowerShriek.B l E T)
    (SpTowerShriek.tau l E T) h).exists.choose_spec M U

private theorem moduleHom_fun_heq {R : Type (u + 1)} [Ring R]
    {M M' N N' : ModuleCat.{u + 1} R} (hM : M = M') (hN : N = N')
    {f : M ⟶ N} {f' : M' ⟶ N'} (h : HEq f f') :
    HEq (fun x ↦ f x) (fun x ↦ f' x) := by
  subst M'
  subst N'
  cases h
  rfl

private theorem ofOpSequence_map_eq {C : Type*} [Category C]
    (F : ℕᵒᵖ ⥤ C) {m n : ℕ} (h : m ≤ n) :
    (Functor.ofOpSequence (X := fun k ↦ F.obj (op k))
      (fun k ↦ F.map (homOfLE (Nat.le_succ k)).op)).map
      (homOfLE h).op = F.map (homOfLE h).op := by
  let cmp : Functor.ofOpSequence (X := fun k ↦ F.obj (op k))
      (fun k ↦ F.map (homOfLE (Nat.le_succ k)).op) ⟶ F :=
    NatTrans.ofOpSequence (fun _ ↦ 𝟙 _) (by
      intro k
      simp only [Functor.ofOpSequence_map_homOfLE_succ, Category.id_comp,
        Category.comp_id])
  have hh := cmp.naturality (homOfLE h).op
  change _ ≫ 𝟙 _ = (𝟙 _) ≫ _ at hh
  exact (Category.comp_id _).symm.trans (hh.trans (Category.id_comp _))

private theorem native_rings_map (T : Scheme.{u}) {m n : ℕ} (h : m ≤ n) :
    (WeilConjectures.SemilinearSections.rings (Scheme.ProEt.topology T)
      (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)).map (homOfLE h).op =
      (spCoefficientCommRings l E T).map (homOfLE h).op :=
  ofOpSequence_map_eq (spCoefficientCommRings l E T) h

private theorem realization_strictTransition_fun_heq (s : Coefficients l E)
    (T : Scheme.{u}) (M : spCoefficientTowers l E T) {m n : ℕ}
    (h : m ≤ n) (U : T.ProEtᵒᵖ) :
    HEq (fun x ↦ ((s.base.realization T).functor.obj M).val.map
        (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
      (fun x ↦ (((s.towers T).equivalence.functor.obj M).transition h).val.app U x) := by
  have hB := s.base.restrictions T M (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
  have hD := (s.towers T).transitions M h U
  refine moduleHom_fun_heq
    (eq_of_heq ((s.base.sections T M n U).trans
      ((s.towers T).sections M n U).symm)) ?_ (hB.trans hD.symm)
  have hmap :
      ((WeilConjectures.SemilinearSections.ring
        (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (WeilConjectures.SemilinearSections.systemRing (Scheme.ProEt.topology T)
          (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))).obj.map
            (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op).hom =
      (((spCoefficientCommRings l E T).map (homOfLE h).op).hom.app U).hom := by
    have hh := WeilConjectures.SemilinearSections.horizontal_map'
      (WeilConjectures.SemilinearSections.rings (Scheme.ProEt.topology T)
        (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) ⋙
          sheafToPresheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}) h U
    exact (congrArg (fun q ↦
      ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map q).hom) hh).trans
      (congrArg (fun q ↦ ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        (q.hom.app U)).hom) (native_rings_map l E T h))
  exact congrArg₂ (fun r N ↦ (ModuleCat.restrictScalars r).obj N) hmap
    (eq_of_heq ((s.base.sections T M m U).trans
      ((s.towers T).sections M m U).symm))

private theorem strictTransitionSection_fun_heq (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (C : StrictRingSystem.{u + 1, u, u + 1} B) {m n : ℕ} (h : m ≤ n)
    (U : T.ProEtᵒᵖ) :
    HEq (fun x ↦ (C.transition h).val.app U x)
      (fun x ↦ spStrictTransitionSection T B C h U x) := by
  rfl

private theorem heq_apply {A A' : Type (u + 1)} {B B' : Type (u + 1)} {f : A → B} {g : A' → B'}
    (hB : B = B') (hf : HEq f g) {x : A} {y : A'} (hx : HEq x y) :
    HEq (f x) (g y) := by
  cases hB
  exact heq_of_eq (congr_heq hf hx)

private def sequenceTransitionSection (T : Scheme.{u})
    (B : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (tau : ∀ n, B (n + 1) ⟶ B n)
    (M : WeilConjectures.SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) B tau) {m n : ℕ} (h : m ≤ n) (U : T.ProEtᵒᵖ)
    (x : ((WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) B tau n).obj M).val.obj U) :
    ((WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) B tau m).obj M).val.obj U :=
  ((WeilConjectures.SemilinearSections.transition.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) B tau h).app M).val.app U x

private theorem sequenceTransitionSection_fun_heq (T : Scheme.{u})
    (B : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (tau : ∀ n, B (n + 1) ⟶ B n)
    (M : WeilConjectures.SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) B tau) {m n : ℕ} (h : m ≤ n) (U : T.ProEtᵒᵖ) :
    HEq (fun x ↦ sequenceTransitionSection T B tau M h U x)
      (fun x ↦ ((WeilConjectures.SemilinearSections.transition.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) B tau h).app M).val.app U x) := by
  rfl

private theorem sequenceTransitionSection_eq (T : Scheme.{u})
    (B : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (tau : ∀ n, B (n + 1) ⟶ B n)
    (M : WeilConjectures.SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) B tau) {m n : ℕ} (h : m ≤ n) (U : T.ProEtᵒᵖ)
    (x : ((WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) B tau n).obj M).val.obj U) :
    sequenceTransitionSection T B tau M h U x =
      ((WeilConjectures.SemilinearSections.transition.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) B tau h).app M).val.app U x := by
  rfl

private theorem evaluation_section_type (T : Scheme.{u})
    (B : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (tau : ∀ n, B (n + 1) ⟶ B n)
    (M : WeilConjectures.SemilinearSections.Systems.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) B tau) (n : ℕ) (U : T.ProEtᵒᵖ) :
    (((WeilConjectures.SemilinearSections.evaluation.{u + 1, u, u + 1}
      (Scheme.ProEt.topology T) B tau n).obj M).val.obj U : Type (u + 1)) =
      (M.val.obj (op (n, U.unop)) : Type (u + 1)) := by
  rfl

private def generator (s : Coefficients l E) (e : Evaluation l E s) (T : Scheme.{u})
    (M : Modules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj M).val.obj U) :
    ((SpTowerShriek.ev l E T n).obj ((ordinaryReduction l E s T).obj M)).val.obj U :=
  (((ordinaryReductionEvaluation l E s e T n).inv.app M).val.app U)
    (systemModelTmul ((s.towers T).scalar
      (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model
      ((spIntegralModuleEquivalence l E T).functor.obj M) U 1 x)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem generator_heq (s : Coefficients l E) (e : Evaluation l E s)
    (T : Scheme.{u}) (M : Modules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj M).val.obj U) :
    HEq (generator l E s e T M n U x)
      (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
        (s.reduction T).ordinary (s.reduction T).level
        ((spIntegralModuleEquivalence l E T).functor.obj M) n U 1 x) := by
  let P : spIntegralSectionModules l E T :=
    (spIntegralModuleEquivalence l E T).functor.obj M
  let C : spCoefficientTowers l E T := (s.reduction T).ordinary.obj P
  let z := spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
    (s.reduction T).ordinary (s.reduction T).level P n U 1 x
  have hgen : generator l E s e T M n U x =
      (((e.ordinary T n).inv.app C).val.app U) z := by
    dsimp only [P, C, z, generator, ordinaryReductionEvaluation, spReductionGenerator,
      Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
      NatTrans.comp_app, Functor.associator_inv_app]
    rfl
  have hi := congrArg (fun a ↦ a.val.app U z) ((e.ordinary T n).inv_hom_id_app C)
  have hs := e.sections T n C U (((e.ordinary T n).inv.app C).val.app U z)
  change HEq ((((e.ordinary T n).hom.app C).val.app U)
    ((((e.ordinary T n).inv.app C).val.app U) z)) _ at hs
  change ((((e.ordinary T n).hom.app C).val.app U)
    ((((e.ordinary T n).inv.app C).val.app U) z)) = z at hi
  exact (heq_of_eq hgen).trans (hs.symm.trans (heq_of_eq hi))


attribute [local irreducible] WeilConjectures.SemilinearSections.transition generator
  spReductionGenerator spStrictTransitionSection



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem realization_transition_section_heq (s : Coefficients l E)
    (T : Scheme.{u}) (C : spCoefficientTowers l E T) {m n : ℕ}
    (h : m ≤ n) (U : T.ProEtᵒᵖ) :
    HEq (fun x ↦ sequenceTransitionSection T (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T) ((s.base.realization T).functor.obj C) h U x)
      (fun x ↦ spStrictTransitionSection T (spCoefficientCommRings l E T)
        ((s.towers T).equivalence.functor.obj C) h U x) := by
  exact (sequenceTransitionSection_fun_heq T (SpTowerShriek.B l E T)
    (SpTowerShriek.tau l E T) ((s.base.realization T).functor.obj C) h U).trans
    ((transition_formula l E T h ((s.base.realization T).functor.obj C) U).trans
      ((realization_strictTransition_fun_heq l E s T C h U).trans
        (strictTransitionSection_fun_heq T (spCoefficientCommRings l E T)
          ((s.towers T).equivalence.functor.obj C) h U)))



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem realization_transition_section_apply_heq (s : Coefficients l E)
    (T : Scheme.{u}) (C : spCoefficientTowers l E T) {m n : ℕ}
    (h : m ≤ n) (U : T.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E T n).obj ((s.base.realization T).functor.obj C)).val.obj U)
    (y : (((s.towers T).equivalence.functor.obj C).level n).val.obj U)
    (hx : HEq x y) :
    HEq (sequenceTransitionSection T (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
        ((s.base.realization T).functor.obj C) h U x)
      (spStrictTransitionSection T (spCoefficientCommRings l E T)
        ((s.towers T).equivalence.functor.obj C) h U y) := by
  have hcod := (evaluation_section_type T (SpTowerShriek.B l E T)
    (SpTowerShriek.tau l E T) ((s.base.realization T).functor.obj C) m U).trans
      (congrArg (fun N : ModuleCat.{u + 1} _ ↦ (N : Type (u + 1)))
        (eq_of_heq ((s.base.sections T C m U).trans
          ((s.towers T).sections C m U).symm)))
  exact heq_apply hcod (realization_transition_section_heq l E s T C h U) hx



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem native_generator_transition_one (s : Coefficients l E) (T : Scheme.{u})
    (P : spIntegralSectionModules l E T) {m n : ℕ} (h : m ≤ n) (U : T.ProEtᵒᵖ)
    (x : P.val.obj U) :
    spStrictTransitionSection T (spCoefficientCommRings l E T)
      ((s.towers T).equivalence.functor.obj ((s.reduction T).ordinary.obj P)) h U
      (spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
        (s.reduction T).ordinary (s.reduction T).level P n U 1 x) =
      spReductionGenerator l E T (s.towers T) (s.reduction T).coefficient
        (s.reduction T).ordinary (s.reduction T).level P m U 1 x := by
  exact ((s.reduction T).transition P h U 1 x).trans
    (congrArg (fun c ↦ spReductionGenerator l E T (s.towers T)
      (s.reduction T).coefficient (s.reduction T).ordinary (s.reduction T).level P m U c x)
      (map_one (((spCoefficientCommRings l E T).map (homOfLE h).op).hom.app U).hom))



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 1600000 in
-- Comparing the recorded module presentations requires additional reduction steps.
private theorem generator_transition (s : Coefficients l E) (e : Evaluation l E s)
    (T : Scheme.{u}) (M : Modules l E T) {m n : ℕ} (h : m ≤ n) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj M).val.obj U) :
    sequenceTransitionSection T (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
      ((ordinaryReduction l E s T).obj M) h U
      (generator l E s e T M n U x) = generator l E s e T M m U x := by
  let P := (spIntegralModuleEquivalence l E T).functor.obj M
  have hh := realization_transition_section_apply_heq l E s T
    ((s.reduction T).ordinary.obj P) h U _ _ (generator_heq l E s e T M n U x)
  exact eq_of_heq (hh.trans ((heq_of_eq
    (native_generator_transition_one l E s T P h U x)).trans
      (generator_heq l E s e T M m U x).symm))




set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteModuleMate_apply (R : Type u) [CommRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (Scheme.proEtaleConstantRing Y R))
    (N : SemilinearSections.Mod.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (Scheme.proEtaleConstantRing X R))
    (a : (Scheme.proEtaleConstantRingPullback R f).obj M ⟶ N)
    (V : Y.ProEtᵒᵖ) (x : M.val.obj V) :
    (((Scheme.proEtaleConstantRingAdjunction R f).homEquiv M N a).val.app V) x =
      (a.val.app ((Scheme.proEtaleBaseChange f).op.obj V))
        ((((Scheme.proEtaleConstantRingAdjunction R f).unit.app M).val.app V) x) := by
  rw [Adjunction.homEquiv_unit]
  rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem moduleIso_hom_inv_apply (T : Scheme.{u})
    (B : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    {M N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology T) B}
    (e : M ≅ N) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    e.inv.val.app U (e.hom.val.app U x) = x := by
  have h := congrArg (fun k ↦ k.val.app U x) e.hom_inv_id
  exact h


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 1600000 in
-- The fixed ordinary pullback/evaluation presentations need additional conversion steps.
private theorem ordinary_unit_transition_sections
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : SpTowerShriek.S l E Y ⥤ SpTowerShriek.S l E X)
    (e : ∀ n, F ⋙ SpTowerShriek.ev l E X n ≅
      SpTowerShriek.ev l E Y n ⋙
        Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f)
    (ht : SpTowerShriek.OrdinaryUnitTransition l E f F e)
    (C : SpTowerShriek.S l E Y) {m n : ℕ} (h : m ≤ n) (V : Y.ProEt)
    (xn : ((SpTowerShriek.ev l E Y n).obj C).val.obj (op V))
    (xm : ((SpTowerShriek.ev l E Y m).obj C).val.obj (op V))
    (hx : sequenceTransitionSection Y (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y)
      C h (op V) xn = xm) :
    sequenceTransitionSection X (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X)
      (F.obj C) h
      (op ((Scheme.proEtaleBaseChange f).obj V))
      (((e n).inv.app
        C).val.app
        (op ((Scheme.proEtaleBaseChange f).obj V))
        ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
          ((SpTowerShriek.ev l E Y n).obj C)).val.app
          (op V)) xn)) =
    ((e m).inv.app
      C).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V))
      ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f).unit.app
        ((SpTowerShriek.ev l E Y m).obj C)).val.app
        (op V)) xm) := by
  let U := op ((Scheme.proEtaleBaseChange f).obj V)
  let z := sequenceTransitionSection X (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X)
    (F.obj C) h U
    (((e n).inv.app C).val.app U
      ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
        ((SpTowerShriek.ev l E Y n).obj C)).val.app (op V))
        xn))
  unfold SpTowerShriek.OrdinaryUnitTransition SpTowerShriek.OrdinaryUnitTransitionModel at ht
  have hh := eq_of_heq (ht C h (op V)
    xn xm
    (heq_of_eq ((sequenceTransitionSection_eq Y (SpTowerShriek.B l E Y)
      (SpTowerShriek.tau l E Y) C h (op V)
      xn).symm.trans
        hx)))
  rw [finiteModuleMate_apply] at hh
  change ((e m).hom.app C).val.app U z = _
    at hh
  have hi := moduleIso_hom_inv_apply X (SpTowerShriek.B l E X m)
    ((e m).app C) U z
  exact hi.symm.trans (congrArg
    (((e m).inv.app C).val.app U) hh)





set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 1600000 in
-- The fixed ordinary pullback/evaluation presentations need additional conversion steps.
private theorem pulled_generator_transition (s : Coefficients l E)
    (e : Evaluation l E s) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Modules l E Y) {m n : ℕ} (h : m ≤ n) (V : Y.ProEt)
    (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)) :
    sequenceTransitionSection X (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X)
      ((s.operations.geometry f).pull.obj ((ordinaryReduction l E s Y).obj M)) h
      (op ((Scheme.proEtaleBaseChange f).obj V))
      ((((s.operations.geometry f).ordinaryPullEvaluation n).inv.app
        ((ordinaryReduction l E s Y).obj M)).val.app
        (op ((Scheme.proEtaleBaseChange f).obj V))
        ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
          ((SpTowerShriek.ev l E Y n).obj ((ordinaryReduction l E s Y).obj M))).val.app
          (op V)) (generator l E s e Y M n (op V) x))) =
    (((s.operations.geometry f).ordinaryPullEvaluation m).inv.app
      ((ordinaryReduction l E s Y).obj M)).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V))
      ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f).unit.app
        ((SpTowerShriek.ev l E Y m).obj ((ordinaryReduction l E s Y).obj M))).val.app
        (op V)) (generator l E s e Y M m (op V) x)) := by
  exact ordinary_unit_transition_sections l E f (s.operations.geometry f).pull
    (s.operations.geometry f).ordinaryPullEvaluation
    (s.operations.geometry f).ordinaryUnitTransition ((ordinaryReduction l E s Y).obj M)
    h V (generator l E s e Y M n (op V) x) (generator l E s e Y M m (op V) x)
    (generator_transition l E s e Y M h (op V) x)



set_option maxHeartbeats 800000 in
-- Comparing the recorded module presentations requires additional reduction steps.
private theorem levelComparison_generator (s : Coefficients l E) (e : Evaluation l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : ∀ n, CondensedRing.upperStar (spIntegralCondensed l E) f ⋙
      ordinaryLevel l E s X n ≅ ordinaryLevel l E s Y n ⋙
        Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f)
    (hb : ∀ (M : Modules l E Y) (n : ℕ) (V : Y.ProEt)
      (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)),
      ((b n).hom.app M).val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (systemModelTmul ((s.towers X).scalar
          (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
          ((spIntegralModuleEquivalence l E X).functor.obj
            ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
          (op ((Scheme.proEtaleBaseChange f).obj V)) 1
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op V) x)) =
        (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
          ((ordinaryLevel l E s Y n).obj M)).val.app (op V))
          (systemModelTmul ((s.towers Y).scalar
            (spIntegralReductionScalar l E Y (s.reduction Y).coefficient n)).model
            ((spIntegralModuleEquivalence l E Y).functor.obj M) (op V) 1 x))
    (M : Modules l E Y) (n : ℕ) (V : Y.ProEt)
    (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)) :
    ((levelComparison l E s e f b n).hom.app M).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V))
      (generator l E s e X
        ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M) n
        (op ((Scheme.proEtaleBaseChange f).obj V))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          M).hom.hom.app (op V) x)) =
    (((s.operations.geometry f).ordinaryPullEvaluation n).inv.app
      ((ordinaryReduction l E s Y).obj M)).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V))
      ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
        ((SpTowerShriek.ev l E Y n).obj ((ordinaryReduction l E s Y).obj M))).val.app (op V))
        (generator l E s e Y M n (op V) x)) := by
  unfold generator
  let t := systemModelTmul ((s.towers Y).scalar
    (spIntegralReductionScalar l E Y (s.reduction Y).coefficient n)).model
    ((spIntegralModuleEquivalence l E Y).functor.obj M) (op V) 1 x
  have hn := congrArg (fun k ↦ k.val.app (op V) t)
    ((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.naturality
      ((ordinaryReductionEvaluation l E s e Y n).inv.app M))
  simp only [Functor.id_map, Functor.comp_map] at hn
  dsimp only [levelComparison, generator, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app]
  simp only [Category.id_comp, Category.comp_id]
  have hi := congrArg (fun k ↦ k.val.app
    (op ((Scheme.proEtaleBaseChange f).obj V))
    (systemModelTmul ((s.towers X).scalar
      (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
      ((spIntegralModuleEquivalence l E X).functor.obj
        ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
      (op ((Scheme.proEtaleBaseChange f).obj V)) 1
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
        M).hom.hom.app (op V) x)))
    ((ordinaryReductionEvaluation l E s e X n).inv_hom_id_app
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
  change _ = _ at hi
  change _ = _ at hn
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
    ConcreteCategory.id_apply] at hi hn ⊢
  erw [hi, hb]
  exact congrArg
    ((((s.operations.geometry f).ordinaryPullEvaluation n).inv.app
      ((ordinaryReduction l E s Y).obj M)).val.app
        (op ((Scheme.proEtaleBaseChange f).obj V))) hn.symm


private theorem restricted_map_apply (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1}} (q : R ⟶ S)
    {M N : SheafOfModules.{u + 1} S} (a : M ⟶ N) (U : T.ProEtᵒᵖ)
    (x : ((SheafOfModules.restrictScalars.{u + 1} q).obj M).val.obj U) :
    ((SheafOfModules.restrictScalars.{u + 1} q).map a).val.app U x = a.val.app U x := by
  rfl

set_option maxHeartbeats 1600000 in
-- Elaborating the two fixed presentations of ordinary modules needs this budget.
private theorem levelComparison_transition (s : Coefficients l E) (e : Evaluation l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : ∀ n, CondensedRing.upperStar (spIntegralCondensed l E) f ⋙
      ordinaryLevel l E s X n ≅ ordinaryLevel l E s Y n ⋙
        Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f)
    (hb : ∀ (M : Modules l E Y) (n : ℕ) (V : Y.ProEt)
      (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)),
      ((b n).hom.app M).val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (systemModelTmul ((s.towers X).scalar
          (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
          ((spIntegralModuleEquivalence l E X).functor.obj
            ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
          (op ((Scheme.proEtaleBaseChange f).obj V)) 1
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op V) x)) =
        (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
          ((ordinaryLevel l E s Y n).obj M)).val.app (op V))
          (systemModelTmul ((s.towers Y).scalar
            (spIntegralReductionScalar l E Y (s.reduction Y).coefficient n)).model
            ((spIntegralModuleEquivalence l E Y).functor.obj M) (op V) 1 x))
    (M : Modules l E Y) {m n : ℕ} (h : m ≤ n) :
    (transition l E X h).app
        ((ordinaryReduction l E s X).obj
          ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M)) ≫
      (restriction l E X h).map ((levelComparison l E s e f b m).hom.app M) =
    (levelComparison l E s e f b n).hom.app M ≫
      (transition l E X h).app
        ((s.operations.geometry f).pull.obj ((ordinaryReduction l E s Y).obj M)) := by
  apply (cancel_epi ((ordinaryReductionEvaluation l E s e X n).inv.app
    ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))).mp
  apply scalar_geometric_hom_ext l E s f M n
  intro V x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply]
  have hh : ((levelComparison l E s e f b m).hom.app M).val.app _
    (sequenceTransitionSection X (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X)
      ((ordinaryReduction l E s X).obj
        ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M)) h
      (op ((Scheme.proEtaleBaseChange f).obj V))
      (generator l E s e X
        ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M) n
        (op ((Scheme.proEtaleBaseChange f).obj V))
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          M).hom.hom.app (op V) x))) =
    sequenceTransitionSection X (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X)
      ((s.operations.geometry f).pull.obj ((ordinaryReduction l E s Y).obj M)) h
      (op ((Scheme.proEtaleBaseChange f).obj V))
      (((levelComparison l E s e f b n).hom.app M).val.app _
        (generator l E s e X
          ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M) n
          (op ((Scheme.proEtaleBaseChange f).obj V))
          (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
            M).hom.hom.app (op V) x))) := by
    have ht := generator_transition l E s e X
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M) h
      (op ((Scheme.proEtaleBaseChange f).obj V))
      (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
        M).hom.hom.app (op V) x)
    exact (congrArg (((levelComparison l E s e f b m).hom.app M).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V))) ht).trans
      ((levelComparison_generator l E s e f b hb M m V x).trans
        ((pulled_generator_transition l E s e f M h V x).symm.trans
          (congrArg (sequenceTransitionSection X (SpTowerShriek.B l E X)
            (SpTowerShriek.tau l E X)
            ((s.operations.geometry f).pull.obj ((ordinaryReduction l E s Y).obj M)) h
            (op ((Scheme.proEtaleBaseChange f).obj V)))
            (levelComparison_generator l E s e f b hb M n V x).symm)))
  dsimp only [restriction, WeilConjectures.SemilinearSections.res]
  erw [restricted_map_apply X _ ((levelComparison l E s e f b m).hom.app M)
    (op ((Scheme.proEtaleBaseChange f).obj V))]
  dsimp only [sequenceTransitionSection, generator, transition] at hh
  with_unfolding_all exact hh


/-- The ordinary scalar/pullback isomorphism, normalized on tensor generators.
Source: blueprint direct-image proof paragraphs (2)--(3).
Proof: the coefficient-limit normalization and finite-reduction pullback theorem give
naturality of every uniformizer scalarProjection. Cofinality factors an ell-power quotient
through one such scalarProjection, yielding the scalar square for that quotient. Uniqueness
of the scalar and geometric left adjoints gives its ordinary finite-level comparison;
the adjunction units show that it sends one tensor unit_f(x) to unit_f(one tensor x).
The fixed evaluation maps identify these generators with sections of the strict
reduction tower. Its specified transition formulas and ordinary pullback unit-transition
compatibility show that the finite comparisons commute with every transition. The
semilinear system assembly theorem then gives the required ordinary tower isomorphism,
and its evaluated formula is exactly OrdinaryPullNormalized. No invertibility of ell
or flatness of its quotient is used. The construction includes zero modules, the empty
scheme, identity morphisms, and level zero.
(blueprint: lem-sp-current-ordinary-pullback). -/
theorem ordinary_reduction_pullback_exists (s : Coefficients l E)
    (e : Evaluation l E s) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ q : OrdinaryPullComparison l E s f, OrdinaryPullNormalized l E s e f q := by
  let b := fun n ↦ ordinaryFiniteComparison l E s f n (finiteSquare l E s f n)
  have hb := fun M n V x ↦ ordinaryFiniteComparison_unit l E s f n
    (finiteSquare l E s f n) M V x
  obtain ⟨q, hq⟩ := assembleComparison l E s e f b
    (fun M m n h ↦ levelComparison_transition l E s e f b hb M h)
  refine ⟨q, ?_⟩
  intro M n V x
  rw [hq M n]
  exact hb M n V x


end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
