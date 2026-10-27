/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.Paper.PurReductionLimitShiftAdjunction
public import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Target shifts of the normalized enriched global adjunction

Source: Stacks 08J9, 08JC, 079P and 0941; the Hom-complex bookkeeping in
proof step 4 of lem-coef-integral-mapping-limit-projections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open SheafOfModules
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The specified lambda, with no choice of a lift from its finite projections.
Source: paragraph 2 of prop-coef-integral-exceptional-adjoint.proof.md
(blueprint: lem-coef-integral-mapping-limit-projections). -/
def integralMappingLimitMap (S : CoefficientDerivedSystemCalculus l E W)
    (P Q : DerivedCategory (scalarReductionSource l E W)) :=
  (coefficientIntegralGlobalHom l E W).map
      (Prod.mkHom (𝟙 (op P)) (S.adjunction.unit.app Q)) ≫
    (S.gamma l E W P (S.reduction.obj Q) (S.reduction_normalized Q)).hom

/-- The normalized target shift of global integral RHom.
Source: the same paragraph; Stacks 08JC, ordinary Hom-complex target reindexing
(blueprint: lem-coef-integral-mapping-limit-projections). -/
def integralMappingLimitSourceShift
    (P Q : DerivedCategory (scalarReductionSource l E W)) (r : ℤ) :=
  letI : IsGrothendieckAbelian.{max u (t+1)} (scalarReductionSource l E W) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{t+1,t,u}
      (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W)).1
  letI : (coefficientIntegralSections l E W).CommShift ℤ :=
    inferInstanceAs ((coefficientOrdinarySections.{u, t+1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).rightDerivedFunctor.CommShift ℤ)
  ((RingedHomUniverses.hom.{t+1, t, u, (max u (t+1))+1}
    (Scheme.ProEt.topology W) (completedIntegralCommRingSheafUnrestricted l E W) P ⋙
      coefficientIntegralSections l E W).commShiftIso r).hom.app Q

/-- The normalized target shift of the actual mapping-limit complex.
Source: the same paragraph; termwise reduction shift and Hom-complex target reindexing
(blueprint: lem-coef-integral-mapping-limit-projections). -/
def integralMappingLimitTargetShift (S : CoefficientDerivedSystemCalculus l E W)
    (sh : PurReductionLimitShiftData l E W S)
    (P Q : DerivedCategory (scalarReductionSource l E W)) (r : ℤ) :=
  coefficientMappingLimit.{max u (t+1)}.map
      ((coefficientSequenceGlobalHom l E W).map
        (Prod.mkHom (𝟙 (op (S.reduction.obj P)))
          ((sh.reduction_shift.commShiftIso r).hom.app Q))) ≫
    ((RingedHomUniverses.hom.{t+1, t, u, (max u (t+1))+1}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) (S.reduction.obj P) ⋙
      coefficientSequenceDerivedRestriction l E W ⋙
      (coefficientTowerSections l E W).rightDerivedFunctor ⋙
      coefficientMappingLimit.{max u (t+1)}).commShiftIso r).hom.app (S.reduction.obj Q)

/-- The enriched global reconstruction comparison respects the fixed target shift.
This is the Hom-complex calculation for arbitrary ambient inputs, without a
completeness or constructibility assumption.
Source: Stacks 08J9 (tensor-Hom adjunction), 08JC (target Hom shift), 079P and
0941 (simultaneous derived sections and limit);
(blueprint: lem-coef-enriched-global-shift).

Proof: choose a flat-term K-flat representative of P and simultaneous K-injective
representatives for the system input and its restriction. The uncurry_model fields
of integralTensorModel and systemTensorModel identify evaluation with ordinary
uncurrying on pure tensors. reduction_tensor_model identifies the reduction tensor
comparison with the strict quotient tensor comparison on those representatives.
Thus the enriched adjunction sends a homogeneous map to its scalar adjoint; target
reindexing commutes with this operation and has no additional sign. The differential
on both shifted Hom complexes is multiplied by (-1)^r. The RightNormalization
characterization of RingedHomUniverses.homCommShift descends this chain equality to
the fixed derived Hom shifts. The limit_shift_resolution equation identifies the
shift on the actual restricted total limit with the same shifted replacement j[r].
Finally globalLimit_model identifies the two global-section/limit comparisons with
the localization of the ordinary comparison on compatible families. That ordinary
comparison commutes with reindexing because its maps are characterized by each
ordinary limit projection. Cancel the representative isomorphisms to descend the
square. Naturality of the enriched comparison moves the reduction shift past it.
The supplied unit_shift equation then moves the actual reconstruction unit past
the limit shift; naturality of the integral Hom target shift gives the displayed
formula. The comparison need not be invertible for arbitrary Q. Negative and zero
shifts use the same calculation. No detection by finite derived projections is used.
-/
theorem coefficientEnrichedGlobalShift
    (S : CoefficientDerivedSystemCalculus l E W)
    (C : CoefficientDerivedSystemCoherence l E W S)
    (sh : PurReductionLimitShiftData l E W S)
    (P Q : DerivedCategory (scalarReductionSource l E W)) (r : ℤ) :
    integralMappingLimitMap l E W S P (Q⟦r⟧) ≫
        integralMappingLimitTargetShift l E W S sh P Q r =
      integralMappingLimitSourceShift l E W P Q r ≫
        (integralMappingLimitMap l E W S P Q)⟦r⟧' := by
  sorry

end WeilConjectures
