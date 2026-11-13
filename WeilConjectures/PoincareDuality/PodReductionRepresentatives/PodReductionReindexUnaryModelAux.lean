/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReductionRepresentatives.PodReindexingReductionTensorData
public import WeilConjectures.PoincareDuality.PodQuotientTransition.PodQuotientTransitionGenerators
import all WeilConjectures.TraceFormula.Integral.IntegralTowerInverseImageUnit
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import all WeilConjectures.PoincareDuality.Pod.Reindex.PodReindexReductionQuotientNormalization
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingGoodComplex

/-! # The ordinary quotient reindexing comparison

For an isomorphism `g`, the ordinary quotient system of a reindexed module is
compared with the sequence inverse image of the quotient system. The comparison
is the left-adjoint mate of the whole-tower tensor-unit isomorphism, and it is
fixed on every quotient unit generator.

Source: blueprint dual-Tate compatibility Steps 2 and 4; Stacks 03EL, 07A4 and 0941.
(blueprint: lem-pod-reduction-reindex-unary-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.PodReductionRepresentatives
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Inverse image commutes with the ordinary total limit of a quotient system.
Source: Stacks 03D6 and 0941. -/
private def towerLimitSquare {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    CompletionUnit.ordinaryLimit l E Y ⋙ inverseImageIntegralModules l E g ≅
      integralComparisonSequencePullback l E g ⋙ CompletionUnit.ordinaryLimit l E X :=
  letI : (inverseImageIntegralModules l E g).IsEquivalence :=
    isoReduction_equivalence.{u, u} g (inverseImageCompletedCoefficientMap l E g)
  letI : PreservesLimitsOfShape ℕᵒᵖ (inverseImageIntegralModules l E g) :=
    PreservesLimitsOfSize.preservesLimitsOfShape
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceRestriction l E Y)
      (preservesLimitNatIso (inverseImageIntegralModules l E g)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (integralTowerInverseImageUnit l E g) lim ≪≫
    Functor.associator _ _ _


-- The section calculation compares two presentations of the same finite quotient.
/-- The unit of an ordinary quotient model, projected to level `n`, is its unit generator.
Source: Stacks 06YY, 0941. -/
theorem unit_projection_section (W : Scheme.{u}) (M : CompletionUnit.OrdinaryModel l E W)
    (N : scalarReductionSource l E W) (n : ℕ) (U : W.ProEtᵒᵖ) (x : N.val.obj U) :
    ((M.adjunction.unit.app N ≫
        limit.π ((coefficientSequenceRestriction l E W).obj (M.tensor.obj N)) (op n)).val.app U)
        x =
      integralComparisonRestrictedSection l E W (M.tensor.obj N) n U
        (PodQuotientTransition.unitSection l E W M N n U x) := by
  let T := (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).app
      (M.tensor.obj N) ≪≫
    (scalarReductionRestriction l E W n).mapIso ((M.evaluation n).app N)
  have hinj : Function.Injective (fun z ↦ T.hom.val.app U z) := by
    intro y z h
    have hi (w) : T.inv.val.app U (T.hom.val.app U w) = w :=
      congrArg (fun k ↦ k.val.app U w) T.hom_inv_id
    exact (hi y).symm.trans ((congrArg (fun w ↦ T.inv.val.app U w) h).trans (hi z))
  apply hinj
  have hunit := M.unit_tensor N n U x
  change T.hom.val.app U _ = _ at hunit
  refine hunit.trans ?_
  dsimp only [T, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    PodQuotientTransition.unitSection]
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    restricted_section_cancel l E W (M.tensor.obj N) n U]
  exact (congrArg (fun f ↦ f.val.app U
    (unrestrictedIntegralTensorSection l E W n N U 1 x))
      ((M.evaluation n).app N).inv_hom_id).symm


/-- The tower limit square, projected to a quotient level, is the tower unit.
Source: Stacks 03D6 and 0941. -/
private theorem towerLimitSquare_π {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (M : coefficientSequenceModules l E Y) (n : ℕ) :
    (towerLimitSquare l E g).hom.app M ≫
        limit.π ((coefficientSequenceRestriction l E X).obj
          ((integralComparisonSequencePullback l E g).obj M)) (op n) =
      (inverseImageIntegralModules l E g).map
          (limit.π ((coefficientSequenceRestriction l E Y).obj M) (op n)) ≫
        ((integralTowerInverseImageUnit l E g).hom.app M).app (op n) := by
  let : (inverseImageIntegralModules l E g).IsEquivalence :=
    isoReduction_equivalence.{u, u} g (inverseImageCompletedCoefficientMap l E g)
  let : PreservesLimitsOfShape ℕᵒᵖ (inverseImageIntegralModules l E g) :=
    PreservesLimitsOfSize.preservesLimitsOfShape
  dsimp only [towerLimitSquare, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom]
  simp only [Category.id_comp, Category.assoc, lim_map]
  erw [preservesLimitNatIso_hom_app, limMap_π, preservesLimitIso_hom_π_assoc]


/-- Sections of the relabelled map are the original sections over the image site.
Source: Stacks 03D6. -/
private theorem inverseImage_map_section {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {M N : integralTowerModules l E Y} (h : M ⟶ N) (U : X.ProEt)
    (x : M.val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((inverseImageIntegralModules l E g).map h).val.app (op U) x =
      h.val.app (op ((proEtaleIsoPostcompose g).obj U)) x := rfl

set_option maxHeartbeats 1600000 in
-- The comparison is the left-adjoint mate of the tower unit; the unit generators are
-- traced through the actual limit projections.
private theorem reindex_normalized_aux {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (MY : CompletionUnit.OrdinaryModel l E Y) (MX : CompletionUnit.OrdinaryModel l E X) :
    ∃ β : MY.tensor ⋙ integralComparisonSequencePullback l E g ≅
        inverseImageIntegralModules l E g ⋙ MX.tensor,
      ∀ (N : scalarReductionSource l E Y) (n : ℕ) (U : X.ProEt)
        (x : N.val.obj (op ((proEtaleIsoPostcompose g).obj U))),
        (β.hom.app N).val.app (op (n, U))
            (((integralComparisonSequencePullback l E g).obj (MY.tensor.obj N)).val.map
              (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
              (integralComparisonSequenceGenerator l E g (MY.tensor.obj N) n
                ((proEtaleIsoPostcompose g).obj U)
                (PodQuotientTransition.unitSection l E Y MY N n
                  (op ((proEtaleIsoPostcompose g).obj U)) x))) =
          PodQuotientTransition.unitSection l E X MX
            ((inverseImageIntegralModules l E g).obj N) n (op U) x := by
  let : (inverseImageIntegralModules l E g).IsEquivalence :=
    isoReduction_equivalence.{u, u} g (inverseImageCompletedCoefficientMap l E g)
  let := towerSequenceDirectImage_equivalence l E g
  let : (integralComparisonSequencePullback l E g).IsEquivalence :=
    (Adjunction.ofIsRightAdjoint
      (integralComparisonSequenceDirectImage l E g)).isEquivalence_left_of_isEquivalence_right
  obtain ⟨e, he⟩ := adjointSquare (inverseImageIntegralModules l E g)
    (integralComparisonSequencePullback l E g) MY.adjunction MX.adjunction
    (towerLimitSquare l E g)
  refine ⟨e.symm, ?_⟩
  intro N n U x
  have hk := congrArg (· ≫ limit.π ((coefficientSequenceRestriction l E X).obj
    ((integralComparisonSequencePullback l E g).obj (MY.tensor.obj N))) (op n)) (he N)
  simp only [Category.assoc, towerLimitSquare_π] at hk
  have hk2 : MX.adjunction.unit.app ((inverseImageIntegralModules l E g).obj N) ≫
      limit.π ((coefficientSequenceRestriction l E X).obj
        (MX.tensor.obj ((inverseImageIntegralModules l E g).obj N))) (op n) ≫
      ((coefficientSequenceRestriction l E X).map (e.hom.app N)).app (op n) =
      (inverseImageIntegralModules l E g).map (MY.adjunction.unit.app N ≫
        limit.π ((coefficientSequenceRestriction l E Y).obj (MY.tensor.obj N)) (op n)) ≫
        ((integralTowerInverseImageUnit l E g).hom.app (MY.tensor.obj N)).app (op n) := by
    rw [Functor.map_comp, Category.assoc, ← hk]
    congr 1
    exact (limMap_π _ _).symm
  rw [← Category.assoc] at hk2
  have hs := congrArg (fun k ↦ k.val.app (op U) x) hk2
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app] at hs
  erw [ConcreteCategory.comp_apply, unit_projection_section l E X MX,
    restriction_map_section l E X, ConcreteCategory.comp_apply, inverseImage_map_section,
    unit_projection_section l E Y MY N n (op ((proEtaleIsoPostcompose g).obj U)) x,
    (integralTowerInverseImageUnit_existsUnique l E g).exists.choose_spec] at hs
  unfold integralComparisonRestrictedSection at hs
  rw [← (cast_inj _).mp hs]
  exact congrArg (fun k ↦ k.val.app (op (n, U))
    (PodQuotientTransition.unitSection l E X MX
      ((inverseImageIntegralModules l E g).obj N) n (op U) x)) (e.hom_inv_id_app N)


/-- Unit generators are compatible with an equality of modules.
Source: Stacks 06YY. -/
private theorem unitSection_eqToHom (W : Scheme.{u}) (M : CompletionUnit.OrdinaryModel l E W)
    {A B : scalarReductionSource l E W} (h : A = B) (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : A.val.obj U) (y : B.val.obj U) (hxy : HEq x y) :
    (M.tensor.map (eqToHom h)).val.app (op (n, U.unop))
        (PodQuotientTransition.unitSection l E W M A n U x) =
      PodQuotientTransition.unitSection l E W M B n U y := by
  subst h
  obtain rfl := eq_of_heq hxy
  simp

/-- The ordinary quotient system commutes with reindexing along an isomorphism, by a
comparison fixed on every quotient unit generator.
Source: blueprint dual-Tate compatibility Steps 2 and 4; Stacks 03D6, 03EL and 0941.
(blueprint: lem-pod-reduction-reindex-unary-model). -/
theorem reindexNormalized_exists {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (MY : CompletionUnit.OrdinaryModel l E Y) (MX : CompletionUnit.OrdinaryModel l E X) :
    ∃ β : MY.tensor ⋙ integralComparisonSequencePullback l E g ≅
        isoReductionIntegralInverse l E g ⋙ MX.tensor,
      PodQuotientTransition.ReindexNormalized l E g MY MX β := by
  have hF : isoReductionIntegralInverse l E g = inverseImageIntegralModules l E g := by
    simp only [isoReductionIntegralInverse, inverseImageIntegralModules,
      podCompletedCoefficientMap_eq]
  obtain ⟨β, hβ⟩ := reindex_normalized_aux l E g MY MX
  refine ⟨β ≪≫ Functor.isoWhiskerRight (eqToIso hF.symm) MX.tensor, ?_⟩
  intro N n U x
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, SheafOfModules.comp_val, PresheafOfModules.comp_app]
  erw [ConcreteCategory.comp_apply, hβ N n U x]
  rw [eqToIso.hom, eqToHom_app]
  exact unitSection_eqToHom l E X MX (Functor.congr_obj hF.symm N) n (op U) x x HEq.rfl


/-- The coefficient identification of a quotient level is the identity on sections.
Source: Stacks 0941. -/
private theorem evaluationRing_app (W : Scheme.{u}) (n : ℕ) (V : W.ProEt) :
    (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app (op V) = 𝟙 _ := by
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

set_option maxHeartbeats 1000000 in
-- Unfolding the pushforward module structure of a quotient level is slow.
/-- Scalars of a quotient level act through the sequence ring.
Source: Stacks 0941. -/
private theorem evaluation_smul (W : Scheme.{u}) (n : ℕ) (M : coefficientSequenceModules l E W)
    (V : W.ProEt) (r : (integralCoefficientSheaf l E W n).obj.obj (op V))
    (m : M.val.obj (op (n, V))) :
    r • @id (((coefficientSequenceEvaluation l E W n).obj M).val.obj (op V)) m =
      @id ((coefficientSequenceCommRingSheaf l E W).obj.obj (op (n, V))) r • m := by
  have h : r • @id (((coefficientSequenceEvaluation l E W n).obj M).val.obj (op V)) m =
      ((eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app (op V) r) • m :=
    rfl
  rw [h, evaluationRing_app]
  rfl

/-- The sequence inverse-image generator is semilinear.
Source: Stacks 03D6 and 0941. -/
private theorem generator_smul {X Y : Scheme.{u}} (g : X ⟶ Y)
    (N : coefficientSequenceModules l E Y) (n : ℕ) (V : Y.ProEt)
    (b : (coefficientSequenceCommRingSheaf l E Y).obj.obj (op (n, V)))
    (x : N.val.obj (op (n, V))) :
    integralComparisonSequenceGenerator l E g N n V (b • x) =
      integralComparisonSequenceRingComponent l E g (op (n, V)) b •
        (show ((integralComparisonSequencePullback l E g).obj N).val.obj
          (op (n, (proEtaleBaseChange g).obj V)) from
            integralComparisonSequenceGenerator l E g N n V x) :=
  (((Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage l E g)).unit.app N).val.app (op (n, V))).hom.map_smul
      b x

/-- Vertical restriction in the sequence ring is restriction in the quotient ring.
Source: Stacks 0941. -/
private theorem sequenceRing_vertical (W : Scheme.{u}) (n : ℕ) {U V : W.ProEt} (f : U ⟶ V)
    (r : (coefficientSequenceCommRingSheaf l E W).obj.obj (op (n, V))) :
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology W))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E W)).obj.map
        (Prod.mkHom (𝟙 n) f).op r =
      (integralCoefficientSheaf l E W n).obj.map f.op r := by
  have h := towerVerticalMap (coefficientSequenceCommRingSystem l E W ⋙
    sheafToPresheaf (ProEt.topology W) CommRingCat.{u + 1}) n f
  exact congrArg (fun k ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map k r) h

/-- Reindexing the constant quotient ring along the comma arrow is the constant map.
Source: Stacks 03D6. -/
private theorem sequenceRing_comma {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (n : ℕ)
    (U : X.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U))) :
    ((sheafCompose (coefficientSequenceTopology (ProEt.topology X))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (coefficientSequenceCommRingSheaf l E X)).obj.map
        (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
        (integralComparisonSequenceRingComponent l E g
          (op (n, (proEtaleIsoPostcompose g).obj U)) a) =
      (isoSectionwiseConstantMap.{u, u} g (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app (op U) a := by
  rw [sequenceRing_vertical]
  exact congrArg (fun f ↦ f.hom.app (op U) a) (towerFiniteCoefficientMap_eq l E g n)

set_option maxHeartbeats 1600000 in
-- Scalar linearity of every map involved, followed by the unit normalization.
/-- A unit-normalized reindexing comparison is fixed on every scalar tensor generator.
Source: Stacks 03D6, 06YY and 0941. -/
theorem reindexNormalized_tensor {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (MY : CompletionUnit.OrdinaryModel l E Y) (MX : CompletionUnit.OrdinaryModel l E X)
    (β : MY.tensor ⋙ integralComparisonSequencePullback l E g ≅
      isoReductionIntegralInverse l E g ⋙ MX.tensor)
    (hβ : PodQuotientTransition.ReindexNormalized l E g MY MX β)
    (N : scalarReductionSource l E Y) (n : ℕ) (U : X.ProEt)
    (a : (integralCoefficientCommRingSheaf l E Y n).obj.obj
      (op ((proEtaleIsoPostcompose g).obj U)))
    (x : N.val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (β.hom.app N).val.app (op (n, U))
        (((integralComparisonSequencePullback l E g).obj (MY.tensor.obj N)).val.map
          (Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (integralComparisonSequenceGenerator l E g (MY.tensor.obj N) n
            ((proEtaleIsoPostcompose g).obj U)
            (((MY.evaluation n).inv.app N).val.app (op ((proEtaleIsoPostcompose g).obj U))
              (unrestrictedTowerTensorSection l E Y n N
                (op ((proEtaleIsoPostcompose g).obj U)) a x)))) =
      ((MX.evaluation n).inv.app ((isoReductionIntegralInverse l E g).obj N)).val.app (op U)
        (unrestrictedTowerTensorSection l E X n ((isoReductionIntegralInverse l E g).obj N)
          (op U) ((isoSectionwiseConstantMap.{u, u} g (CommRingCat.of
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app
              (op U) a) x) := by
  have hsY := isoReduction_tensor_smul l E Y n N (op ((proEtaleIsoPostcompose g).obj U)) a x
  have hsX := isoReduction_tensor_smul l E X n ((isoReductionIntegralInverse l E g).obj N) (op U)
    ((isoSectionwiseConstantMap.{u, u} g (CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app (op U) a) x
  rw [hsY, hsX, map_smul, map_smul]
  erw [evaluation_smul l E Y n (MY.tensor.obj N), evaluation_smul l E X n]
  erw [generator_smul, PresheafOfModules.map_smul, map_smul, hβ N n U x,
    sequenceRing_comma]
  rfl

end WeilConjectures.PodReductionRepresentatives
