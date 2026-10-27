/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.Paper.SfExactPullbackCounitNormalization
public import Sheaf.Paper.CompletedPullback
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.PbcQbarCompletedPullback
public import Mathlib.CategoryTheory.Functor.OfSequence
import all Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.SfCompletedAugmentationAdjunct
import Sheaf.CategoryTheory.ExactTowerAugmentedCounitEvaluation

/-! # The actual completed-pullback comparison and the derived-limit mate

Source: blueprint localization returned Step 6, immersion-comparison Step 5;
Stacks Tag 099N (2),(5), with the native adjunction refinement
(blueprint: lem-sf-completed-pullback-mate-factorization).

All coefficient sheaves, quotient towers, units, projections and exact-pullback
identifications are the published constructions. Level `n` means exponent `n+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ExactPullbackNormalization

private theorem mate_augmentation
    {C D S U : Type*} [Category C] [Category D] [Category S] [Category U]
    (DX : C ⥤ S) (LX : S ⥤ C) (DY : D ⥤ U) (LY : U ⥤ D)
    (ax : DX ⊣ LX) (ay : DY ⊣ LY) (H : C ⥤ D) (T : S ⥤ U)
    (j : H ⋙ DY ⟶ DX ⋙ T) (K : C) (M : S) (i : DX.obj K ⟶ M) :
    ay.unit.app (H.obj K) ≫ LY.map (j.app K ≫ T.map i) =
      H.map (ax.unit.app K ≫ LX.map i) ≫
        (ay.unit.app (H.obj (LX.obj M)) ≫
          LY.map (j.app (LX.obj M) ≫ T.map (ax.counit.app M))) := by
  let h := ax.unit.app K ≫ LX.map i
  have hi : DX.map h ≫ ax.counit.app M = i := by
    dsimp only [h]
    rw [DX.map_comp, Category.assoc]
    have hn := ax.counit.naturality i
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [hn, ← Category.assoc]
    exact (congrArg (fun f ↦ f ≫ i) (ax.left_triangle_components K)).trans
      (Category.id_comp i)
  have hn := ay.unit.naturality (H.map h)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have hj := j.naturality h
  dsimp only [Functor.comp_map] at hj
  change _ = H.map h ≫ _
  symm
  rw [← Category.assoc, hn, Category.assoc, ← LY.map_comp]
  congr 1
  rw [← Category.assoc, hj, Category.assoc, ← T.map_comp, hi]
  rfl

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {X Y : Scheme.{u}} (g : Y ⟶ X) [IsIso (completedCoefficientMap g d)]
  [(moduleFunctor d g).Additive]
  [PreservesFiniteLimits (moduleFunctor d g)] [PreservesFiniteColimits (moduleFunctor d g)]

/-- The right mate of the inverse exact constant-tower identification `j`.
Source: localization returned Step 6, mate formula; Stacks 0941 and 099N
(blueprint: lem-sf-completed-pullback-mate-factorization).
Here `constantIso.hom` is `j` inverse, so the order is unit, inverse `j`, then counit. -/
def limitMate (M : DerivedCategory (pbcTowers X (pbcAdicCompletion X d))) :
    (moduleFunctor d g).mapDerivedCategory.obj ((completedTowerRlim d X).obj M) ⟶
      (completedTowerRlim d Y).obj ((towerFunctor d g).mapDerivedCategory.obj M) :=
  (d.constantRlimAdjunction Y).unit.app _ ≫
    (completedTowerRlim d Y).map
      ((constantIso d g).hom.app ((completedTowerRlim d X).obj M) ≫
        (towerFunctor d g).mapDerivedCategory.map
          ((d.constantRlimAdjunction X).counit.app M))

/-- Evaluation of the published strict quotient augmentation, with the canonical
exact-localization identification of evaluation of a constant tower with the input.
Source: localization returned Step 6, quotient augmentation; Stacks 099N
(blueprint: lem-sf-completed-pullback-mate-factorization). -/
def quotientAugmentation (n : ℕ)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    K ⟶ (pbcTowerEvaluation X (pbcAdicCompletion X d) n).obj
      ((completedReductionTower X d).obj K) :=
  (Functor.mapDerivedCategoryIdIso (pbcModules X (pbcAdicCompletion X d))).inv.app K ≫
    (Functor.mapDerivedCategoryNatIso
      (Functor.constCompEvaluationObj (D := pbcModules X (pbcAdicCompletion X d))
        (op n))).inv.app K ≫
    (Functor.mapDerivedCategoryCompIso (completedTowerConstant d X)
      ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X (pbcAdicCompletion X d))).obj
        (op n))).hom.app K ≫
    (pbcTowerEvaluation X (pbcAdicCompletion X d) n).map
      ((completedReductionTowerUnit d X).app K)

/-- The specified target limit projection, transported through exact evaluation.
Source: localization returned Step 6, evaluation paragraph; Stacks 0941
(blueprint: lem-sf-completed-pullback-mate-factorization). -/
def pulledProjection (n : ℕ)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :
    (completedTowerRlim d Y).obj ((towerFunctor d g).mapDerivedCategory.obj
      ((completedReductionTower X d).obj K)) ⟶
    (moduleFunctor d g).mapDerivedCategory.obj
      ((pbcTowerEvaluation X (pbcAdicCompletion X d) n).obj
        ((completedReductionTower X d).obj K)) :=
  (completedRlimProjection Y (pbcAdicCompletion Y d) n).app
      ((towerFunctor d g).mapDerivedCategory.obj ((completedReductionTower X d).obj K)) ≫
    (evaluationIso d g n).hom.app ((completedReductionTower X d).obj K)

/-- Every composite strict quotient transition, evaluated in the ambient coefficient category.
Source: localization returned Step 6, strict quotient transitions; Stacks 099N
(blueprint: lem-sf-completed-pullback-mate-factorization). -/
def quotientTransition (a b : ℕ) (h : a ≤ b)
    (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) :=
  (DerivedTowerPullback.derivedTransition
    (A := pbcModules X (pbcAdicCompletion X d)) a b h).app
      ((completedReductionTower X d).obj K)

private def limitComplexUnit (V : Scheme.{u}) :
    (lim : pbcTowers V (pbcAdicCompletion V d) ⥤
      pbcModules V (pbcAdicCompletion V d)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ completedTowerRlim d V where
  app I := (completedRlimUnit V (pbcAdicCompletion V d)).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj I)
  naturality _ _ f := (completedRlimUnit V (pbcAdicCompletion V d)).naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map f)

private instance limitComplexUnit_derived (V : Scheme.{u}) :
    (completedTowerRlim d V).IsRightDerivedFunctor (limitComplexUnit d V)
      (HomologicalComplex.quasiIso (pbcTowers V (pbcAdicCompletion V d)) (.up ℤ)) := by
  apply (CochainComplex.KInjectives.localizerMorphism _)
    |>.isRightDerivedFunctor_of_isRightDerivabilityStructure
  intro I
  have : I.obj.IsKInjective := I.property
  change IsIso ((completedRlimUnit V (pbcAdicCompletion V d)).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj I.obj))
  exact completedRlim_computation V _ I.obj

private theorem evaluation_counit (V : Scheme.{u}) (n : ℕ)
    (N : DerivedCategory (pbcTowers V (pbcAdicCompletion V d))) :
    (pbcTowerEvaluation V (pbcAdicCompletion V d) n).map
        ((d.constantRlimAdjunction V).counit.app N) =
      (ringedConstantTowerEvaluation (pbcModules V (pbcAdicCompletion V d)) (op n)).hom.app
        ((completedTowerRlim d V).obj N) ≫
      (completedRlimProjection V (pbcAdicCompletion V d) n).app N := by
  erw [← limitCounitProjection_eq d V n]
  change _ = _ ≫ (_ ≫ _)
  change _ = (constantEvaluationIso (reductionModules V (d.completedRing V))
    (op n)).hom.app _ ≫ (constantEvaluationIso _ (op n)).inv.app _ ≫ _
  rw [Iso.hom_inv_id_app_assoc]
  rfl

/-- Factorization of the actual normalized ambient comparison, with its finite projections,
all strict quotient transitions, their composites, and naturality in unbounded inputs.

Source: localization returned Step 6, old immersion-comparison Step 5; native
SfImmersionCompletedPullbackComparison ordinaryToCompleted_eq and
completedProjection_compatibility; Stacks Tag 099N (2),(5)
(blueprint: lem-sf-completed-pullback-mate-factorization).

The actual comparison after the universal-counit identifications is `exactAugmentation`,
by lem-sf-exact-pullback-counit-normalization. No completeness or product preservation
is imposed. The module functor transports scalars along the inverse of the specified
coefficient map, as in that dependency; its normalized tensor comparison identifies it
with the ordinary tensor pullback in the statement.

Proof:
1. The actual K-injective construction has components r_n F(P -> P_n), for the
flat-term K-flat representative P and a target K-injective tower resolution r.
The canonical constant/derived-limit adjunction sends the pulled strict augmentation
exactly to this map, by lem-coef-derived-tower-counit-projections and the unbounded
K-injective limit construction of lem-weil-pbc-ringed-strict-tower-homotopy-limit.
Counit normalization identifies it with exactAugmentation on the entire strict tower.
2. Expand limitMate and move F(comp_K) past the target unit by naturality. Move the
constant image of comp_K past constantIso by naturality. The remaining interior map
is F_tower(epsilon_X,M composed with Delta_X(comp_K)).
3. Expand comp_K as the source unit followed by L_X(i_K). Counit naturality for i_K
and the left triangle identity reduce epsilon_X,M composed with Delta_X(comp_K)
to i_K. Substitution gives the asserted equality before taking any evaluation.
4. The target counit evaluates to the specified limit projection by
lem-coef-derived-tower-counit-projections. Counit naturality and the triangle identity
show that its composite with Delta(alpha^F_K) is the pulled augmentation. Exact
normalized evaluation identifies its nth component with F(q_n,K).
5. The counit is a map of derived strict towers. Hence its evaluations commute with
every transition; the constant source has identity transitions. Exact evaluation
identifies the target transition with F(rho_b,a). Strict quotient functoriality gives
the identity and composite transition laws, including equal indices. Naturality of
i, the constant comparison, the units and counits gives naturality for every derived
map K -> K'. Neither comp_K invertibility nor preservation of products is used. -/
theorem completed_pullback_mate_factorization :
    (∀ K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)),
      exactAugmentation d g K =
        (moduleFunctor d g).mapDerivedCategory.map (d.completionUnit X K) ≫
          limitMate d g ((completedReductionTower X d).obj K)) ∧
    (∀ (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) (n : ℕ),
      exactAugmentation d g K ≫ pulledProjection d g n K =
        (moduleFunctor d g).mapDerivedCategory.map (quotientAugmentation d n K)) ∧
    (∀ (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
        (a b : ℕ) (h : a ≤ b),
      pulledProjection d g b K ≫
          (moduleFunctor d g).mapDerivedCategory.map (quotientTransition d a b h K) =
        pulledProjection d g a K) ∧
    (∀ (K : DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
        (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
      pulledProjection d g c K ≫
          (moduleFunctor d g).mapDerivedCategory.map (quotientTransition d b c hbc K) ≫
          (moduleFunctor d g).mapDerivedCategory.map (quotientTransition d a b hab K) =
        pulledProjection d g c K ≫ (moduleFunctor d g).mapDerivedCategory.map
          (quotientTransition d a c (hab.trans hbc) K)) ∧
    (∀ (K K' : DerivedCategory (pbcModules X (pbcAdicCompletion X d))) (f : K ⟶ K'),
      (moduleFunctor d g).mapDerivedCategory.map f ≫ exactAugmentation d g K' =
        exactAugmentation d g K ≫ (completedTowerRlim d Y).map
          ((towerFunctor d g).mapDerivedCategory.map ((completedReductionTower X d).map f))) := by
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} X
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} Y
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} X
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} Y
  let R := reductionModuleRing X (pbcAdicCompletion X d)
  let S := reductionModuleRing Y (pbcAdicCompletion Y d)
  have hR : ∀ (U : X.ProEtᵒᵖ) (a b : R.obj.obj U), a * b = b * a := by
    intro U a b
    exact @mul_comm ((pbcAdicCompletion X d).obj.obj U) _ a b
  have hS : ∀ (U : Y.ProEtᵒᵖ) (a b : S.obj.obj U), a * b = b * a := by
    intro U a b
    exact @mul_comm ((pbcAdicCompletion Y d).obj.obj U) _ a b
  have hEval := @ExactTowerAugmentedCounit.exact_tower_augmented_counit_evaluation.{
    u + 2, u + 2, u + 2, u + 2, u + 1, u, u + 1, u, u + 1, u + 1}
    X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
    Y.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
    (ProEt.topology X) (ProEt.topology Y)
    inferInstance inferInstance inferInstance inferInstance
    R S hR hS
    (proEtaleRingModules_hasDerivedCategory X (pbcAdicCompletion X d))
    (proEtaleRingModules_hasDerivedCategory Y (pbcAdicCompletion Y d))
    (pbcTowers_hasDerivedCategory X (pbcAdicCompletion X d))
    (pbcTowers_hasDerivedCategory Y (pbcAdicCompletion Y d))
    (moduleFunctor d g) inferInstance inferInstance inferInstance inferInstance
    (completedTowerRlim d Y) (limitComplexUnit d Y) (limitComplexUnit_derived d Y)
    (by
      intro I hI
      have := hI
      exact completedRlim_computation Y _ I)
    (d.constantRlimAdjunction Y)
    (by
      intro I _
      exact derivedCounit_unit constLimAdj I)
    (completedRlimProjection Y (pbcAdicCompletion Y d)) (evaluation_counit d Y)
  refine ⟨?_, ?_, ?_, ?_, (completed_augmentation_adjunct d g).2.1⟩
  · intro K
    rw [(completed_augmentation_adjunct d g).1 K]
    exact mate_augmentation _ _ _ _ (d.constantRlimAdjunction X)
      (d.constantRlimAdjunction Y) (moduleFunctor d g).mapDerivedCategory
      (towerFunctor d g).mapDerivedCategory (constantIso d g).hom K _
      ((completedReductionTowerUnit d X).app K)
  · intro K n
    rw [(completed_augmentation_adjunct d g).1 K]
    have h := (hEval.2.2.1 K ((completedReductionTower X d).obj K)
      ((completedReductionTowerUnit d X).app K)).2.2 n
    have hs :
        (Functor.mapDerivedCategoryNatIso
          (Functor.compConstIso ℕᵒᵖ (moduleFunctor d g)).symm).inv =
        (Functor.mapDerivedCategoryNatIso
          (Functor.compConstIso ℕᵒᵖ (moduleFunctor d g))).hom := by rfl
    simpa only [hs, ExactTowerAugmentedCounit.transpose,
      ExactTowerAugmentedCounit.augmentation, ExactTowerAugmentedCounit.projection,
      ExactTowerAugmentedCounit.level, pulledAugmentation, pulledProjection,
      quotientAugmentation, ringedConstantTowerEvaluation, ringedConstantTowerPullback,
      towerDerivedEvaluationInterchange, constantIso, evaluationIso,
      Functor.mapDerivedCategoryNatIso_refl, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, NatTrans.id_app,
      Category.id_comp, Category.comp_id, Category.assoc] using h
  · intro K a b h
    have ht := hEval.2.2.2.1 b a h ((completedReductionTower X d).obj K)
    simpa only [ExactTowerAugmentedCounit.projection, pulledProjection,
      quotientTransition, towerDerivedEvaluationTransition, DerivedTowerPullback.derivedTransition,
      towerDerivedEvaluationInterchange, evaluationIso,
      Functor.mapDerivedCategoryNatIso_refl, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, NatTrans.id_app, Category.id_comp, Category.assoc] using ht
  · intro K a b c hab hbc
    have ht := (hEval.2.2.2.2.1 c b a hbc hab ((completedReductionTower X d).obj K)).1
    simpa only [ExactTowerAugmentedCounit.projection, pulledProjection,
      quotientTransition, towerDerivedEvaluationTransition, DerivedTowerPullback.derivedTransition,
      towerDerivedEvaluationInterchange, evaluationIso,
      Functor.mapDerivedCategoryNatIso_refl, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, NatTrans.id_app, Category.id_comp, Category.assoc] using ht

end AlgebraicGeometry.Scheme.ExactPullbackNormalization
