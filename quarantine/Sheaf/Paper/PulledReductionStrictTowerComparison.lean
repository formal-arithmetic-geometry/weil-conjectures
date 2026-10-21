/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Paper.CompletedTowerPullback
public import Sheaf.Paper.CompletedRlimFunctor
public import Sheaf.Paper.OrderedExchangeCoefficientComparison
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage

import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Paper.RingedTopoiTensorSections
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Algebra.Homology.DiagramKFlatReplacements
import Sheaf.Paper.FlatCommonQuotientReductionTower
import Sheaf.Algebra.Homology.FlatScalarRestrictionKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Augmented strict reduction tower of ordinary pullback

Source: Stacks Project, Tag 099N, proof of (5), and current blueprint completed-pullback
reduction, paragraph 2 (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison).

## Main definitions

* `IsStrictNormalized` fixes the strict finite tensor comparison before localization.
* `limitComparison` is the specified inverse-limit isomorphism induced by a tower comparison.

## Main statements

* `strictTowerComparison` gives the augmented comparison, its projections and its unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.PulledReduction
attribute [local instance] completedModulePullback_additive
attribute [local instance] completedTowerModulePullback_additive
attribute [local instance] completedReductionModuleTowerFunctor_additive
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- Constant scalar restriction, on the original small site.
Source: Stacks 099L (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
abbrev res (T : Scheme.{t}) := proEtaleRingRestrictScalars (exchangeScalar d T)

/-- Exact inverse image of constant-coefficient modules.
Source: Stacks 099N(5) (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
abbrev pull := proEtaleRingModulePullback g (exchangeConstantRing Y A)
  (exchangeConstantRing X A) (exchangeConstantIso g A)

/-- Ordinary constant-coefficient pullback after restriction; its exact derived functor
is N in the statement. Source: Stacks 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
abbrev ordinarySource := res d Y ⋙ pull (A := A) g

/-- N, on all ambient objects, without a completeness or boundedness hypothesis.
Source: Stacks 099N(5) (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def source := (ordinarySource d g).mapDerivedCategory

/-- The pulled-back completed-coefficient strict reduction tower H.
Source: Stacks 099N(5) (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def tower := completedReductionTower Y d ⋙ completedTowerPullback g d

/-- Ordinary restriction on strict towers, retaining all transitions.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
abbrev tres (T : Scheme.{t}) := exchangeTowerModuleRes d T


/-- The ordinary strict source diagram, before localization.
Source: Stacks 099N(5) (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
abbrev ordinaryReductionSource := ordinarySource d g ⋙ OrderedExchange.reductionModule d X

/-- The ordinary strict pulled quotient diagram, before localization.
Source: Stacks 099N(5) (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
abbrev ordinaryReductionTarget := completedReductionModuleTowerFunctor Y d ⋙
  completedTowerModulePullback g d ⋙ tres d X

/-- Zero maps for the entire ordinary strict comparison.
Source: Stacks 03EL
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
local instance ordinaryReductionTarget_preservesZeroMorphisms :
    (ordinaryReductionTarget d g).PreservesZeroMorphisms where
  map_zero M N := by
    have h := Functor.map_zero (completedReductionModuleTowerFunctor Y d) M N
    have h' := Functor.map_zero (completedTowerModulePullback g d)
      ((completedReductionModuleTowerFunctor Y d).obj M)
      ((completedReductionModuleTowerFunctor Y d).obj N)
    have h'' := Functor.map_zero (tres d X)
      ((completedTowerModulePullback g d).obj ((completedReductionModuleTowerFunctor Y d).obj M))
      ((completedTowerModulePullback g d).obj ((completedReductionModuleTowerFunctor Y d).obj N))
    exact (congrArg (tres d X).map
      ((congrArg (completedTowerModulePullback g d).map h).trans h')).trans h''

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar-insertion section for completed module pullback. Apply the actual
model-site pullback adjunction unit at the transported object, then insert 1.
The up/down module transports preserve section carriers definitionally, so this
is the unit of the constructed inverse image, with no choice of an adjunction.
Source: Stacks 03EK, 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def insertion (M : reductionModules Y (d.completedRing Y))
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((completedModulePullback g d).obj M).val.obj ((proEtaleBaseChange g).op.obj U) := by
  letI : (proEtaleModelBaseChange g).IsContinuous
      (proEtaleModelTopology Y) (proEtaleModelTopology X) :=
    proEtaleModelBaseChange_isContinuous g
  exact reductionTensorSection X (completedCoefficientMap g d)
    ((proEtaleModuleInverseImage g (d.completedRing Y)).obj M)
    ((proEtaleBaseChange g).op.obj U) 1
    (((SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
      (F := proEtaleModelBaseChange g)
      (J := proEtaleModelTopology Y) (K := proEtaleModelTopology X)
      (proEtaleModelRingUnit g (d.completedRing Y))).unit.app
        ((proEtaleModuleToModel (reductionModuleRing Y (d.completedRing Y))).obj M)).val.app
          (AsSmall.up.op.obj U) x)

/-- Scalar insertion determines the ordinary comparison, including its augmentation.
Source: Stacks 03EK, 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def IsOrdinaryNormalized
    (s : ordinarySource d g ⟶ completedModulePullback g d ⋙ res d X) : Prop :=
  ∀ (M : reductionModules Y (d.completedRing Y)) (U : Y.ProEtᵒᵖ) (x : M.val.obj U),
    (s.app M).val.app ((proEtaleBaseChange g).op.obj U)
      (((proEtaleRingModuleAdjunction g (exchangeConstantRing Y A)
        (exchangeConstantRing X A) (exchangeConstantIso g A)).unit.app
          ((res d Y).obj M)).val.app U x) = insertion d g M U x

/-- Degreewise scalar insertion as a map of the actual pulled complexes.
The target is written as the successive two complex functors, retaining their
already fixed zero-map instances.
Source: Stacks 06YY
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def ordinaryComplexComparison
    (s : ordinarySource d g ⟶ completedModulePullback g d ⋙ res d X)
    (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
    ((ordinarySource d g).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ((res d X).mapHomologicalComplex (.up ℤ)).obj
        (((completedModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) where
  f i := s.app (P.X i)
  comm' i j _ := (s.naturality (P.d i j)).symm

/-- A strict diagram comparison is normalized on inverse images of pure tensors.
Its natural-transformation type includes every quotient transition. The scalar on the
right is inserted only after the finite quotient is formed on Y.
Source: Stacks 03EL, 07A4, 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def IsStrictNormalized (e : ordinaryReductionSource d g ≅ ordinaryReductionTarget d g) : Prop :=
  ∀ (M : reductionModules Y (d.completedRing Y)) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (d.finiteRing Y n).obj.obj U) (x : M.val.obj U),
    ((e.hom.app M).app (op n)).val.app ((proEtaleBaseChange g).op.obj U)
      (reductionTensorSection X (OrderedExchange.quotient d X n)
        ((ordinarySource d g).obj M) ((proEtaleBaseChange g).op.obj U)
        ((proEtaleRingDirectImageMap g (d.finiteRing Y n) (d.finiteRing X n)
          (d.finiteRingIso g n)).hom.app U s)
        (((proEtaleRingModuleAdjunction g (exchangeConstantRing Y A)
          (exchangeConstantRing X A) (exchangeConstantIso g A)).unit.app
            ((res d Y).obj M)).val.app U x)) =
      insertion d g ((completedReductionLevel Y d n).obj M) U
        (reductionTensorSection Y (d.projection Y n) M U s x)

/-- The comparison from H on a K-flat completed model to its ordinary pulled quotient
complex. Its invertibility is asserted only on the specified resolving class below.
Source: Stacks 06YY, 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def targetCounit (P : CochainComplex (reductionModules Y (d.completedRing Y)) ℤ) :
    ((tower d g) ⋙ (tres d X).mapDerivedCategory).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ordinaryReductionTarget d g).mapHomologicalComplex (.up ℤ)).obj P) :=
  (tres d X).mapDerivedCategory.map
      ((completedTowerPullback g d).map (completedReductionTowerComplexCounit Y d P) ≫
        completedTowerPullbackComplexCounit g d
          ((completedReductionComplexTowerFunctor Y d).obj P)) ≫
    (tres d X).mapDerivedCategoryFactors.hom.app
      (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj
        ((completedReductionComplexTowerFunctor Y d).obj P))

/-- Exact evaluation commutes with restriction of the entire strict diagram.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def evaluationRes (T : Scheme.{t}) (n : ℕ) :
    (tres d T).mapDerivedCategory ⋙
        reductionTowerDerivedEvaluation T (reductionModuleRing T (exchangeConstantRing T A)) n ≅
      reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n ⋙
        (res d T).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso
    (Iso.refl (tres d T ⋙ reductionTowerEvaluation T
      (reductionModuleRing T (exchangeConstantRing T A)) n))

/-- Exact restriction commutes with constant strict diagrams.
Source: Stacks 03D7 (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def diagonalRes (T : Scheme.{t}) :
    (res d T).mapDerivedCategory ⋙ OrderedExchange.diagonal (A := A) T ≅
      completedDerivedConstant d T ⋙ (tres d T).mapDerivedCategory :=
  (OrderedExchange.scalarDiagonal d T).symm

/-- The pulled strict quotient augmentation, before inverse limit.
Source: Stacks 099N(5) (blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def pulledAugmentation (K : reductionDerivedCategory Y (d.completedRing Y)) :
    (completedDerivedConstant d X).obj ((completedOrdinaryPullback g d).obj K) ⟶
      (tower d g).obj K :=
  (completedPullbackConstantIso g d).hom.app K ≫
    (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K)

/-- Rho is Rlim(tau) inverse after the specified restriction/limit comparison. This
uses the normalized K-injective limit comparison already recorded in the library.
Source: Stacks 0940, 099N(5)
(blueprint: lem-weil-pbc-pulled-reduction-strict-tower-comparison). -/
def limitComparison
    (τ : source d g ⋙ OrderedExchange.reduction d X ≅
      tower d g ⋙ (tres d X).mapDerivedCategory)
    (K : reductionDerivedCategory Y (d.completedRing Y)) :
    (res d X).mapDerivedCategory.obj
        ((completedRlim X (d.completedRing X)).obj ((tower d g).obj K)) ≅
      (OrderedExchange.completion d X).obj ((source d g).obj K) :=
  (OrderedExchange.lambda d X).app ((tower d g).obj K) ≪≫
    (OrderedExchange.rlim (A := A) X).mapIso (τ.app K).symm

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
  sorry

end AlgebraicGeometry.Scheme.PulledReduction
