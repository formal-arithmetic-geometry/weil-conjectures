/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Paper.SmoothPurityReductionTowerData


/-! # Invertibility of the specified reduction adjuncts

Source: blueprint latest, normalized-towers-reduction, normalization paragraph;
Stacks Tags 06YY, 0G7E.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The actual reduction morphisms supplied by D are invertible on strict derived
reduction. This is a compatibility assertion about D.reduction, not just existence
of unrelated isomorphisms between successive scalar extensions.

Source: blueprint latest, sec-smooth-purity, normalized-towers-reduction, normalization;
Stacks Tags 06YY and 0G7E
(blueprint: lem-sp-reduction-tower-adjunct-normalization).

Proof:
1. Resolve an arbitrary integral complex by a flat-term K-flat complex P. The counit
identifies its image under red with the degreewise strict tensor reduction of P.
2. For m <= n, D.reduction_rep describes the reduction on this representative as
derived scalar extension followed by the ordinary tensor adjunct of its transition.
The assumed pure-tensor transition formula and D.ordinaryReduction_eq identify that
ordinary adjunct with (x tensor c) tensor d mapping to x tensor quotient(c)*d.
Equality on pure tensors determines the sheafified tensor map.
3. Successive derived quotient normalization identifies this map with the canonical
invertible transitivity comparison. Its inverse inserts one in the middle factor.
The normalization of the scalar-extension units is precisely the adjunct relation
of step 2. Scalar-model uniqueness transports this computation to D.scalar's models.
4. Use the evaluation comparisons and the computation counits to conjugate this
isomorphism to D.reduction on red(Q P). Naturality conjugates it along a K-flat
representative isomorphism to red(M), proving the assertion for every M.
Equal indices use the tensor unitor, and three-index compatibility follows from
associativity of scalar multiplication. No qcqs, boundedness, flat coefficient map,
or constructibility assumption is used. The zero complex and empty site are included.
-/
theorem sp_reduction_tower_adjunct_normalization
    (D : SpCoefficientTowersAbelian l E T)
    (coefficient : spIntegralSectionRing l E T ≅
      WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (ordinary : spIntegralSectionModules l E T ⥤ spCoefficientTowers l E T)
    [ordinary.Additive]
    (level : spReductionOrdinaryLevels l E T D coefficient ordinary)
    (transition : IsSpReductionTransition l E T D coefficient ordinary level)
    (red : DerivedCategory (spIntegralSectionModules l E T) ⥤
      spDerivedCoefficientTowers l E T D)
    (counit : DerivedCategory.Q ⋙ red ⟶
      ordinary.mapHomologicalComplex (.up ℤ) ⋙ spTowerLocalization l E T D)
    (universal : red.IsLeftDerivedFunctor counit
      (HomologicalComplex.quasiIso (spIntegralSectionModules l E T) (.up ℤ)))
    (computes : ∀ P : CochainComplex (spIntegralSectionModules l E T) ℤ,
      CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E T) P →
        IsIso (counit.app P))
    (evaluation : spReductionDerivedEvaluations l E T D coefficient red) :
    ∀ M : DerivedCategory (spIntegralSectionModules l E T),
      IsSpNormalizedTower l E T D (red.obj M) := by sorry

end AlgebraicGeometry.ProEtale
