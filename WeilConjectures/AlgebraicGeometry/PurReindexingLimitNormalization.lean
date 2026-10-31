/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurCompletedReindexingData
import WeilConjectures.AlgebraicGeometry.PurCompletedModuleReindexing
import all WeilConjectures.AlgebraicGeometry.ConstantTowerDirectImageNormalization
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # PurReindexingLimitNormalization

Source: Stacks Project and the extracted proof of
lem-pur-isomorphism-completed-reduction-reindexing.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] proEtaleRingModulePullback
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

private theorem reindexing_unit
    {C D E B : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    [Category E] [Abelian E] [HasDerivedCategory E]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (F : C ⥤ D) [F.Additive] (H : C ⥤ E) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (P : D ⥤ B) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (G : E ⥤ B) [G.Additive]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions E]
    [H.PreservesKInjectiveComplexes] (beta : F ⋙ P ≅ H ⋙ G) :
    let b := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F P).symm ≪≫
      Functor.rightDerivedFunctorNatIso beta ≪≫
      Functor.rightDerivedFunctorCompIso H G ≪≫
      Functor.isoWhiskerRight H.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor
    ∀ (I : CochainComplex C ℤ), I.IsKInjective →
      P.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I) ≫
        b.hom.app (DerivedCategory.Q.obj I) ≫
        G.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
      P.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) ≫
        G.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj I) := by
  intro b I hI
  have := hI
  have hn :=
    AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.squareComparison_normalized
      F H P G beta I
  change P.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ I) ≫
    b.hom.app (DerivedCategory.Q.obj I) ≫
    G.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) =
    P.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) ≫
      G.rightDerivedFunctorUnitQ ((H.mapHomologicalComplex (.up ℤ)).obj I)
  rw [Functor.rightDerivedFunctorUnitQ_eq, Functor.rightDerivedFunctorUnitQ_eq]
  apply (cancel_mono
    (G.rightDerivedFunctorObjQIso ((H.mapHomologicalComplex (.up ℤ)).obj I)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change b.hom.app (DerivedCategory.Q.obj I) ≫ _ ≫ _ =
    P.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).hom ≫
      P.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) at hn
  calc
    P.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).inv ≫
        (b.hom.app (DerivedCategory.Q.obj I) ≫
          G.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app I) ≫
          (G.rightDerivedFunctorObjQIso ((H.mapHomologicalComplex (.up ℤ)).obj I)).hom) =
        P.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).inv ≫
          (P.mapDerivedCategory.map (F.rightDerivedFunctorObjQIso I).hom ≫
            P.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I)) := by
              rw [hn]
    _ = P.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) := by
          simp only [← P.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id,
            CategoryTheory.Functor.map_id, Category.id_comp]

-- The ordinary mate simplification exposes the canonical projection equation.
set_option linter.flexible false in
/-- Reindexing commutes with the derived strict limit, preserving projections,
K-injective comparison units and the actual quotient augmentation.
Source: extracted proof, steps 3 and 5; Stacks Tags 0A07 and 099N.
(blueprint: lem-pur-reindexing-limit-unit-normalization).
Proof: the completed-module equivalence has exact reverse reindexing as left
adjoint. Its termwise tower functor therefore preserves K-injectives. Preservation
of limits supplies beta; its composites with the limit projections are the
reindexed original projections. Apply beta on K-injective tower resolutions to
obtain b. The right-derived universal property descends the comparison and its
inverse, and its unit equation is the displayed representative formula. For the
constant-tower unit, both routes factor the same compatible family of reindexed
resolution maps through the inverse limit; projection uniqueness makes them equal.
Naturality for the strict quotient augmentation then identifies its composite
with the specified ordinaryToCompleted, giving the last equation for every K.
This last step concerns the actual quotient augmentation, not its finite-level
images; no derived-completeness hypothesis is needed for that equality. -/
theorem purReindexingLimitNormalization
    {T' T : Scheme.{t}} (u : T' ⟶ T) [IsIso u] :
  (∃ beta : completedTowerLimit T (d.completedRing T) ⋙
      proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u) ≅
      d.towerModulePull u ⋙ completedTowerLimit T' (d.completedRing T'),
    (∀ (C : d.towers T) (n : ℕᵒᵖ),
      beta.hom.app C ≫ limit.π ((d.towerModulePull u).obj C) n =
        (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).map (limit.π C n)) ∧
    ∃ b : completedRlim T (d.completedRing T) ⋙ d.pull u ≅
      d.towerPull u ⋙ completedRlim T' (d.completedRing T'),
    (∀ I : CochainComplex (d.towers T) ℤ, I.IsKInjective →
      (d.pull u).map ((completedTowerLimit T (d.completedRing T)).rightDerivedFunctorUnitQ I) ≫
        b.hom.app (DerivedCategory.Q.obj I) ≫
        (completedRlim T' (d.completedRing T')).map
          ((d.towerModulePull u).mapDerivedCategoryFactors.hom.app I) =
      (proEtaleRingModulePullback u (d.completedRing T)
        (d.completedRing T') (d.integralRingIso u)).mapDerivedCategoryFactors.hom.app
          (((completedTowerLimit T (d.completedRing T)).mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex beta.hom (.up ℤ)).app I) ≫
        (completedTowerLimit T' (d.completedRing T')).rightDerivedFunctorUnitQ
          (((d.towerModulePull u).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∀ K : d.derived T,
      d.ordinaryToCompleted u K =
        (d.pull u).map (d.completionUnit T K) ≫
          b.hom.app ((completedReductionTower T d).obj K))) := by
  let P := proEtaleRingModulePullback u (d.completedRing T)
    (d.completedRing T') (d.integralRingIso u)
  obtain ⟨e, he, _⟩ := (purCompletedModuleReindexing d u).2
  have : P.IsEquivalence := by
    dsimp only [P]
    rw [← he]
    infer_instance
  let H := d.towerModulePull u
  let F := completedTowerLimit T (d.completedRing T)
  let G := completedTowerLimit T' (d.completedRing T')
  have : H.IsEquivalence := inferInstanceAs
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj P).IsEquivalence
  let beta : F ⋙ P ≅ H ⋙ G := preservesLimitNatIso P
  let b : F.rightDerivedFunctor ⋙ P.mapDerivedCategory ≅
      H.mapDerivedCategory ⋙ G.rightDerivedFunctor :=
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F P).symm ≪≫
      Functor.rightDerivedFunctorNatIso beta ≪≫
      Functor.rightDerivedFunctorCompIso H G ≪≫
      Functor.isoWhiskerRight H.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor
  refine ⟨beta, ?_, b, ?_, ?_⟩
  · intro C n
    exact preservesLimitIso_hom_π P C n
  · exact reindexing_unit F H P G beta
  · have hm : b.hom = (mateEquiv (d.constantRlimAdjunction T)
        (d.constantRlimAdjunction T')
        (TwoSquare.mk _ _ _ _ (d.derivedConstantPullbackIso u).inv)).natTrans := by
      have ho : (mateEquiv
          (constLimAdj : d.constantTower T ⊣ F)
          (constLimAdj : d.constantTower T' ⊣ G)
          (TwoSquare.mk _ _ _ _ (d.constantPullbackIso u).inv)).natTrans = beta.hom := by
        apply NatTrans.ext
        funext C
        apply limit.hom_ext
        intro n
        simp [beta, mateEquiv_apply, constLimAdj,
          AdicCoefficientDatum.constantPullbackIso, preservesLimitNatIso]
        exact (preservesLimitIso_hom_π P C n).symm
      have h :=
        AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.squareComparison_eq_mate
        F H P G (d.constantTower T) (d.constantTower T')
        constLimAdj constLimAdj (d.constantPullbackIso u).symm beta ho
      simpa [b, AdicCoefficientDatum.constantRlimAdjunction,
        AdicCoefficientDatum.derivedConstantPullbackIso, Iso.trans_inv,
        Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
        Category.assoc] using h
    intro K
    have hu := unit_mateEquiv (d.constantRlimAdjunction T)
      (d.constantRlimAdjunction T')
      (TwoSquare.mk _ _ _ _ (d.derivedConstantPullbackIso u).inv) K
    change P.mapDerivedCategory.map ((d.constantRlimAdjunction T).unit.app K) ≫
      (mateEquiv (d.constantRlimAdjunction T) (d.constantRlimAdjunction T')
        (TwoSquare.mk _ _ _ _ (d.derivedConstantPullbackIso u).inv)).natTrans.app
          ((d.derivedConstantTower T).obj K) =
      (d.constantRlimAdjunction T').unit.app ((d.pull u).obj K) ≫
        G.rightDerivedFunctor.map ((d.derivedConstantPullbackIso u).inv.app K) at hu
    rw [← hm] at hu
    unfold AdicCoefficientDatum.ordinaryToCompleted AdicCoefficientDatum.completionUnit
    change (d.constantRlimAdjunction T').unit.app (P.mapDerivedCategory.obj K) ≫
      G.rightDerivedFunctor.map ((d.derivedConstantPullbackIso u).inv.app K ≫
        H.mapDerivedCategory.map ((completedReductionAugmentation d T).app K)) =
      P.mapDerivedCategory.map ((d.constantRlimAdjunction T).unit.app K ≫
        F.rightDerivedFunctor.map ((completedReductionAugmentation d T).app K)) ≫
      b.hom.app ((completedReductionTower T d).obj K)
    simp only [Functor.map_comp, Category.assoc]
    have hn := b.hom.naturality ((completedReductionAugmentation d T).app K)
    change P.mapDerivedCategory.map
      (F.rightDerivedFunctor.map ((completedReductionAugmentation d T).app K)) ≫
      b.hom.app _ = b.hom.app _ ≫
        G.rightDerivedFunctor.map
          (H.mapDerivedCategory.map ((completedReductionAugmentation d T).app K)) at hn
    calc
      (d.constantRlimAdjunction T').unit.app ((d.pull u).obj K) ≫
          G.rightDerivedFunctor.map ((d.derivedConstantPullbackIso u).inv.app K) ≫
          G.rightDerivedFunctor.map
            (H.mapDerivedCategory.map ((completedReductionAugmentation d T).app K)) =
        (P.mapDerivedCategory.map ((d.constantRlimAdjunction T).unit.app K) ≫
          b.hom.app ((d.derivedConstantTower T).obj K)) ≫
          G.rightDerivedFunctor.map
            (H.mapDerivedCategory.map ((completedReductionAugmentation d T).app K)) := by
              rw [hu]
              simp only [Category.assoc]
      _ = P.mapDerivedCategory.map ((d.constantRlimAdjunction T).unit.app K) ≫
          P.mapDerivedCategory.map
            (F.rightDerivedFunctor.map ((completedReductionAugmentation d T).app K)) ≫
          b.hom.app ((completedReductionTower T d).obj K) := by
            simp only [Category.assoc]
            rw [← hn]



end AlgebraicGeometry.Scheme
