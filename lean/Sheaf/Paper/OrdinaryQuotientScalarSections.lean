/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.CompletionUnitModels
import Sheaf.Paper.CoefficientExtensionAssociationQuotientUnits
import all Sheaf.Paper.OrdinaryQuotientScalarSectionCasts

/-! # Sections and presentation units of ordinary quotient systems

Source: Stacks 03D7, 03EK and 0941, naturality of ordinary tensor adjunction units.
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted constantSheaf
attribute [local implicit_reducible] integralCoefficientCommRingSheaf
  SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  Functor.mapHomologicalComplex HomologicalComplex.complexOfFunctorsToFunctorToComplex

private theorem finiteUnit_eq (K : scalarReductionSource l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ) (x : K.val.obj U) :
    CoefficientExtensionAssociation.finiteUnitSection l E W K n U x =
      unrestrictedIntegralTensorSection l E W n K U 1 x := by
  unfold CoefficientExtensionAssociation.finiteUnitSection
    CoefficientExtensionAssociation.normalizedUnitSection
    CoefficientExtensionAssociation.quotientAdjunction
  exact (scalarReductionExtension_adjunction l E W n).choose_spec K U x

/-- The presentation inverse takes the kappa-inverse unit section to M's quotient unit.
Source: Stacks 03D7, naturality and normalization of the ordinary quotient unit.
(blueprint: lem-trf-ordinary-quotient-scalar-presentation-unit).
Proof: invert the presentation comparison equation, evaluate at degree i and
apply it to 1 tensor x. Evaluation commutes with the presentation inverse, and
its section casts are HEq to identity. The normalized quotient-adjunction unit
identifies the finite unit section with 1 tensor x, giving the stated formula. -/
private theorem presentationUnit
    (M : CompletionUnit.OrdinaryModel l E W)
    (P : CochainComplex (scalarReductionSource l E W) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (a : (M.quotient l E W).obj P ≅ C)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (hκ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
        κ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P)
    (n : ℕ) (i : ℤ) (U : W.ProEtᵒᵖ) (x : (P.X i).val.obj U) :
    (a.inv.f i).val.app (op (n, U.unop))
      (integralComparisonSequenceSection l E W (C.X i) n U
        (((κ n).inv.f i).val.app U
          (unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x))) =
      CoefficientExtensionAssociation.quotientUnitSection l E W M (P.X i) n U x := by
  let z := unrestrictedIntegralTensorSection l E W n (P.X i) U 1 x
  let w := integralComparisonSequenceSection l E W (C.X i) n U
    (((κ n).inv.f i).val.app U z)
  have hi := congrArg (fun b ↦ b.inv.f i) (hκ n)
  simp only [Iso.trans_inv, HomologicalComplex.comp_f, Functor.mapIso_inv,
    Functor.mapHomologicalComplex_map_f] at hi
  have hx := congrArg (fun b ↦ b.val.app U z) hi
  have hw : coefficientEvaluationSection l E W (C.X i) n U w =
      ((κ n).inv.f i).val.app U z :=
    eq_of_heq ((evaluation_section_heq l E (C.X i) n U w).trans
      (sequenceSection_heq l E W (C.X i) n U _))
  have hm := evaluation_map_section l E (a.inv.f i) n U w
  rw [hw] at hm
  change ((coefficientSequenceEvaluation l E W n).map (a.inv.f i)).val.app U
      (((κ n).inv.f i).val.app U z) =
    ((M.evaluation n).inv.app (P.X i)).val.app U z at hx
  rw [hx] at hm
  have he := evaluation_section_heq l E (M.tensor.obj (P.X i)) n U
    ((a.inv.f i).val.app (op (n, U.unop)) w)
  unfold CoefficientExtensionAssociation.quotientUnitSection
  rw [finiteUnit_eq l E W]
  exact eq_of_heq (he.symm.trans (heq_of_eq hm.symm))

end OrdinaryScalarTowerProof
end WeilConjectures
