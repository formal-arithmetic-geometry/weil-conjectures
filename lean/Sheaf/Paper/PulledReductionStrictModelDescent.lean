/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Paper.PulledReductionComparisonData

/-! # Descent of the augmented pulled reduction model

Source: Stacks 06YY, 07A4, and 099N(5).
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
attribute [local instance] ordinaryReductionTarget_preservesZeroMorphisms
attribute [local instance] completedModulePullback_additive
attribute [local instance] completedTowerModulePullback_additive
attribute [local instance] completedReductionModuleTowerFunctor_additive
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The augmented strict reduction comparison, with its scalar-insertion source
and its universal-counit normalizations, for arbitrary ambient inputs.

Source: Stacks Project, Tag 099N, proof of (5); current blueprint,
completed-pullback-reduction, paragraph 2
(blueprint: lem-weil-pbc-pulled-reduction-strict-model-descent).

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
natural transformations and isomorphism asserted here. Every construction is natural
in K; no completeness or boundedness assumption is used. -/
theorem strictModelComparison :
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
            (tres d X).mapDerivedCategory.map (pulledAugmentation d g K)) := by
  sorry

end AlgebraicGeometry.Scheme.PulledReduction
