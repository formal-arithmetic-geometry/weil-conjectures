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
import Sheaf.CategoryTheory.DerivedTowerCounitProjections
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

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
  sorry

end AlgebraicGeometry.Scheme.ExactPullbackNormalization
