/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.PulledReductionComparisonData
public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.CompletedRlimFunctor
public import Sheaf.Paper.OrderedExchangeCoefficientComparison
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

import Sheaf.Paper.PulledReductionStrictModelDescent
import Sheaf.Paper.RestrictionLimitProjectionUnit
/-! # Augmented strict reduction tower comparison

Source: Stacks 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.PulledReduction
attribute [local instance] ordinaryReductionTarget_preservesZeroMorphisms
attribute [local instance] completedModulePullback_additive
attribute [local instance] completedTowerModulePullback_additive
attribute [local instance] completedReductionModuleTowerFunctor_additive
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

private theorem completion_unit_projection
    (K : OrderedExchange.D (A := A) X) (n : ℕ) :
    (OrderedExchange.unit d X).app K ≫
        (completedRlimProjection X (exchangeConstantRing X A) n).app
          ((OrderedExchange.reduction d X).obj K) =
      (OrderedExchange.diagonalAdjunction (A := A) X).unit.app K ≫
        (completedRlimProjection X (exchangeConstantRing X A) n).app
          ((OrderedExchange.diagonal (A := A) X).obj K) ≫
        (reductionTowerDerivedEvaluation X
          (reductionModuleRing X (exchangeConstantRing X A)) n).map
            ((OrderedExchange.augmentation d X).app K) := by
  change ((OrderedExchange.diagonalAdjunction (A := A) X).unit.app K ≫
    (OrderedExchange.rlim (A := A) X).map ((OrderedExchange.augmentation d X).app K)) ≫
      (completedRlimProjection X (exchangeConstantRing X A) n).app
        ((OrderedExchange.reduction d X).obj K) = _
  rw [Category.assoc, (completedRlimProjection X (exchangeConstantRing X A) n).naturality]

/-- The augmented strict reduction comparison, its canonical inverse-limit comparison,
and both projection and completion-unit normalizations, for arbitrary ambient inputs.

Source: Stacks Project, Tag 099N, proof of (5); current blueprint,
completed-pullback-reduction, paragraph 2
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison).

Proof: (1) Resolve K by a flat-term K-flat completed-coefficient complex P. Flatness
of the completed constant algebra makes its restriction K-flat with flat terms; exact
constant inverse image preserves this class. (2) The common finite quotients identify
its constant and completed reductions. The cochain pullback/tensor comparison identifies
the pulled constant reduction with the inverse image of the completed reduction.
(3) Let J have the source object and all quotient objects, with the augmentation
and quotient arrows. Resolve the coefficient diagram R[0] to S_n[0] by a single
objectwise flat-term K-flat diagram V_J. Put E_j = Tot(P tensor_R V_j). The complex
E_j is flat-term K-flat over B: rewrite it as P tensor_B (B tensor_R V_j), then
use change of rings and the total tensor K-flat lemma. Its comparison to P at the
source and to P tensor_B S_n at a quotient is a quasi-isomorphism since Res(P)
is K-flat over R. This resolves the augmented diagram, with all its arrows.
(4) Write U for inverse image, C = U(B), R' = U(R), and D for the target completed
ring. The pulled E_j is Tot(U(P) tensor_C (D tensor_R' U(V_j))). Exact inverse
image carries the coefficient augmentations to quasi-isomorphisms. Flatness of
D over R' and the common finite quotients identify their targets as D at the source
and S_n' at a quotient. Since U(P) is K-flat over C, tensoring these comparisons
with U(P) preserves quasi-isomorphisms. The finite targets are U(P tensor_B S_n)
by the same tensor balancing as in step 2. Thus one strict quasi-isomorphism of
augmented diagrams compares the pulled resolution with the ordinary pulled quotient
diagram and its scalar-insertion source. In particular targetCounit is invertible,
although finite quotient complexes need not be K-flat over B. No flatness of C to D
is used. (5) On pure tensors the strict isomorphism sends s tensor x to the same
pulled quotient class. Quotient transitions reduce s, and the source comparison inserts
1, so the entire augmented diagram commutes. (6) The formulas commute with chain maps
and resolving quasi-isomorphisms; the universal counits descend them uniquely to the
natural transformations and isomorphism asserted here. (7) Scalar restriction preserves
K-injective towers since its scalar-extension left adjoint is exact. The same restricted
K-injective resolution computes both limits; its projections give the existing lambda.
(8) Define rho by lambda followed by inverse Rlim(tau). Naturality of the actual derived
limit projections gives the displayed evaluation identity. (9) The strict augmented
identity identifies the pulled-back unit, after rho, with the quotient-completion unit.
Projecting that factorization gives the finite scalar-extension unit. Every construction
is natural in K; no completeness or boundedness assumption has been used. -/
theorem strictTowerComparison :
    ∃ (s : ordinarySource d g ⟶ completedModulePullback g d ⋙ res d X)
      (δ : source d g ⟶ completedOrdinaryPullback g d ⋙ (res d X).mapDerivedCategory)
      (e : ordinaryReductionSource d g ≅ ordinaryReductionTarget d g)
      (τ : source d g ⋙ OrderedExchange.reduction d X ≅
        tower d g ⋙ (tres d X).mapDerivedCategory),
      IsOrdinaryNormalized d g s ∧ IsStrictNormalized d g e ∧
      (∀ P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := d.completedRing Y) P →
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
          (R := d.completedRing Y) (P.X i)) →
        δ.app (DerivedCategory.Q.obj P) ≫
            (res d X).mapDerivedCategory.map (completedOrdinaryPullbackComplexCounit g d P) ≫
            (res d X).mapDerivedCategoryFactors.hom.app
              (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) =
          (ordinarySource d g).mapDerivedCategoryFactors.hom.app P ≫
            DerivedCategory.Q.map (ordinaryComplexComparison d g s P)) ∧
      (∀ P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ,
        CochainComplex.IsKFlatIndependentCoefficients.{t + 1, t, t + 1}
          (R := d.completedRing Y) P →
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite.{t + 1, t, t + 1, t + 1}
          (R := d.completedRing Y) (P.X i)) →
        IsIso (targetCounit d g P) ∧
        τ.hom.app (DerivedCategory.Q.obj P) ≫ targetCounit d g P =
          (OrderedExchange.reduction d X).map
              ((ordinarySource d g).mapDerivedCategoryFactors.hom.app P) ≫
            OrderedExchange.reductionComplexCounit d X
              (((ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)) ∧
      (∀ K : reductionDerivedCategory Y (d.completedRing Y),
        (OrderedExchange.augmentation d X).app ((source d g).obj K) ≫ τ.hom.app K =
          (OrderedExchange.diagonal (A := A) X).map (δ.app K) ≫
            (diagonalRes d X).hom.app ((completedOrdinaryPullback g d).obj K) ≫
            (tres d X).mapDerivedCategory.map (pulledAugmentation d g K)) ∧
      (∀ (K : reductionDerivedCategory Y (d.completedRing Y)) (n : ℕ),
        (res d X).mapDerivedCategory.map
            ((completedRlimProjection X (d.completedRing X) n).app ((tower d g).obj K)) =
          (limitComparison d g τ K).hom ≫
            (completedRlimProjection X (exchangeConstantRing X A) n).app
              ((OrderedExchange.reduction d X).obj ((source d g).obj K)) ≫
            (reductionTowerDerivedEvaluation X
              (reductionModuleRing X (exchangeConstantRing X A)) n).map (τ.hom.app K) ≫
            (evaluationRes d X n).hom.app ((tower d g).obj K)) ∧
      (∀ K : reductionDerivedCategory Y (d.completedRing Y),
        δ.app K ≫ (res d X).mapDerivedCategory.map (completedPullbackComparison g d K) ≫
            (limitComparison d g τ K).hom =
          (OrderedExchange.unit d X).app ((source d g).obj K)) ∧
      (∀ (K : reductionDerivedCategory Y (d.completedRing Y)) (n : ℕ),
        (OrderedExchange.unit d X).app ((source d g).obj K) ≫
            (completedRlimProjection X (exchangeConstantRing X A) n).app
              ((OrderedExchange.reduction d X).obj ((source d g).obj K)) =
          (OrderedExchange.diagonalAdjunction (A := A) X).unit.app ((source d g).obj K) ≫
            (completedRlimProjection X (exchangeConstantRing X A) n).app
              ((OrderedExchange.diagonal (A := A) X).obj ((source d g).obj K)) ≫
            (reductionTowerDerivedEvaluation X
              (reductionModuleRing X (exchangeConstantRing X A)) n).map
                ((OrderedExchange.augmentation d X).app ((source d g).obj K))) := by
  obtain ⟨s, δ, e, τ, hs, he, hδ, hτ, haug⟩ := strictModelComparison d g
  refine ⟨s, δ, e, τ, hs, he, hδ, hτ, haug, ?_, ?_, ?_⟩
  · intro K n
    have hLambda := (restrictionLimitNormalization d X).1 ((tower d g).obj K) n
    have hn := (completedRlimProjection X (exchangeConstantRing X A) n).naturality
      (τ.inv.app K)
    dsimp only [limitComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    simp only [Category.assoc]
    erw [reassoc_of% hn]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [(reductionTowerDerivedEvaluation X
      (reductionModuleRing X (exchangeConstantRing X A)) n).map_id, Category.id_comp]
    exact hLambda.symm
  · intro K
    let L := (completedOrdinaryPullback g d).obj K
    let a := pulledAugmentation d g K
    let R := (res d X).mapDerivedCategory
    let T := (tres d X).mapDerivedCategory
    let F := OrderedExchange.rlim (A := A) X
    have hn := (OrderedExchange.lambda d X).hom.naturality a
    have hu := (restrictionLimitNormalization d X).2 L
    have hd := (OrderedExchange.diagonalAdjunction (A := A) X).unit.naturality
      (δ.app K)
    change δ.app K ≫ (OrderedExchange.diagonalAdjunction (A := A) X).unit.app
      (R.obj L) = (OrderedExchange.diagonalAdjunction (A := A) X).unit.app
        ((source d g).obj K) ≫ F.map
          ((OrderedExchange.diagonal (A := A) X).map (δ.app K)) at hd
    have hF : R.map (completedPullbackComparison g d K) ≫
        (OrderedExchange.lambda d X).hom.app ((tower d g).obj K) =
      (OrderedExchange.diagonalAdjunction (A := A) X).unit.app (R.obj L) ≫
        F.map ((diagonalRes d X).hom.app L ≫ T.map a) := by
      change R.map ((completedConstantRlimUnit d X).app L ≫
        (completedRlim X (d.completedRing X)).map a) ≫ _ = _
      rw [Functor.map_comp, Category.assoc]
      erw [hn]
      rw [← Category.assoc]
      erw [hu]
      simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
      rfl
    change δ.app K ≫ R.map (completedPullbackComparison g d K) ≫
      ((OrderedExchange.lambda d X).hom.app ((tower d g).obj K) ≫
        F.map (τ.inv.app K)) = _
    calc
      _ = δ.app K ≫
          (OrderedExchange.diagonalAdjunction (A := A) X).unit.app (R.obj L) ≫
          F.map ((diagonalRes d X).hom.app L ≫ T.map a) ≫
          F.map (τ.inv.app K) := by
            rw [← Category.assoc _ _ (F.map _), hF]
            simp only [Category.assoc]
      _ = (OrderedExchange.diagonalAdjunction (A := A) X).unit.app
            ((source d g).obj K) ≫
          F.map ((OrderedExchange.diagonal (A := A) X).map (δ.app K)) ≫
          F.map ((diagonalRes d X).hom.app L ≫ T.map a) ≫
          F.map (τ.inv.app K) := by
            rw [← Category.assoc (δ.app K) _ _, hd]
            simp only [Category.assoc]
      _ = (OrderedExchange.diagonalAdjunction (A := A) X).unit.app
            ((source d g).obj K) ≫
          F.map (((OrderedExchange.diagonal (A := A) X).map (δ.app K) ≫
            (diagonalRes d X).hom.app L ≫ T.map a) ≫ τ.inv.app K) := by
              simp only [F.map_comp, Category.assoc]
      _ = (OrderedExchange.diagonalAdjunction (A := A) X).unit.app
            ((source d g).obj K) ≫
          F.map (((OrderedExchange.augmentation d X).app ((source d g).obj K) ≫
            τ.hom.app K) ≫ τ.inv.app K) := by rw [haug K]
      _ = _ := by
        simp only [Category.assoc, Iso.hom_inv_id_app]
        erw [Category.comp_id]
        rfl
  · intro K n
    exact completion_unit_projection d ((source d g).obj K) n

end AlgebraicGeometry.Scheme.PulledReduction
