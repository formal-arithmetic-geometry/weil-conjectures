/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurSequenceKFlatComparisonData

import WeilConjectures.AlgebraicGeometry.PurReductionLimitShiftAdjunction
import WeilConjectures.AlgebraicGeometry.PurSequenceReductionCounitShift

/-! # Descent of the specified quotient-sequence shifts

Source: Stacks 06YY, 0G7D and 012Z.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory
namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  coefficientSequenceEvaluation coefficientFiniteDerivedExtension scalarReductionExtension
  coefficientFiniteReductionModel purSequenceShiftIso

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The universal comparison preserves the specified ordinary shifts and the canonical
finite computation maps.
Source: Stacks, sites-cohomology.tex, Tags 06YY and 0G7D; homology.tex, Tag 012Z;
steps 6 and 7 of lem-pur-sequence-kflat-comparison-shifts.
(blueprint: lem-pur-sequence-reduction-shifts).

Proof: additive ordinary pullback commutes with cochain shifts by identity on reindexed
terms. Its shifted differential is (-1)^r times the original mapped differential.
The same computation applies to every finite scalar extension. Naturality of the
ordinary quotient transformations gives their shift squares before localization.
The tensor shift isomorphism shows that resolving complexes stay resolving under
shifts: tensor with a shifted K-flat complex is a shift of an acyclic tensor, flat
terms reindex, and shifted quasi-isomorphisms are quasi-isomorphisms.
Descend the identity-on-terms comparisons through this resolving class. Universal
uniqueness gives the shift structure on A.L and on S.reduction, characterized by their
counit squares. The comparison A.alpha satisfies that counit equation, so cancellation
on resolving representatives gives its shift square. Apply exact evaluation to those
squares and the finite normalization in A.representative: uniqueness gives the finite
resolution square and the reductionEvaluation shift square on all derived inputs.
At shift zero all term maps are identity; for a sum of shifts they are still identity,
and the differential signs multiply. Uniqueness extends the zero and addition equations
to the localization, giving CommShift (and hence inverse-shift coherence). -/
theorem purSequenceReductionShifts
    (F : FiniteFieldDatum.{t}) (hl : l ≠ F.p)
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (A : PurSequenceKFlatComparison l E W S O) :
    Nonempty (PurSequenceKFlatShiftComparison l E W S O A) := by
  obtain ⟨D⟩ := purReductionLimitShiftAdjunction l E W S hS
  let sR := D.reduction_shift
  letI : S.reduction.CommShift ℤ := sR
  let sF := D.finite_reduction_shift
  let sL : A.L.CommShift ℤ := Functor.CommShift.ofIso A.α.symm ℤ
  have hres := fun (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W)
        (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
      (flatQ : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
        (J := Scheme.ProEt.topology W)
        (R := completedIntegralCommRingSheafUnrestricted l E W) (Q.X i)) ↦
    purSequenceReductionCounitResolutionShift l E W S D O A Q r hQ flatQ
  have hred : NatTrans.CommShift A.reductionCounit ℤ := by
    simpa using purSequenceReductionCounitShift l E W S D O A hres
  letI := hred
  have hαinv := Functor.CommShift.ofIso_compatibility A.α.symm ℤ
  letI := hαinv
  have hα : NatTrans.CommShift A.α.hom ℤ := by
    exact NatTrans.CommShift.of_iso_inv A.α.symm ℤ
  letI := hα
  have heps : NatTrans.CommShift A.ε ℤ := by
    rw [A.comparison]
    infer_instance
  let x : PurSequenceKFlatShiftComparison l E W S O A := {
    left_shift := sL
    reduction_shift := sR
    finite_shift := sF
    comparison := by
      intro P r
      have h := Functor.CommShift.ofIso_compatibility A.α.symm ℤ
      letI := h
      letI : NatTrans.CommShift A.α.hom ℤ := NatTrans.CommShift.of_iso_inv A.α.symm ℤ
      simpa [purSequenceShiftIso, sL] using NatTrans.shift_app_comm A.α.hom r P
    left_resolution := by
      intro Q r
      simpa only [purSequenceShiftIso, Functor.commShiftIso_comp_hom_app, Category.assoc]
        using NatTrans.shift_app_comm A.ε r Q
    left_terms := by
      intros
      rfl
    finite_terms := by
      intros
      rfl
    left_differential := by
      intros
      simp
    finite_differential := by
      intros
      simp
    quotient_shifts := by
      intro m n h Q r
      simpa only [Functor.commShiftIso_comp_hom_app] using
        NatTrans.shift_app_comm
          (NatTrans.mapHomologicalComplex (coefficientOrdinaryQuotient l E W h) (.up ℤ)) r Q
    finite_resolution := by
      intros n Q r hQ hQr
      simpa [purSequenceShiftIso] using D.finite_shift_model n Q r hQ hQr
    finite_evaluation := by
      intro n P r
      letI := D.reduction_shift_evaluation n
      simpa only [purSequenceShiftIso, Functor.commShiftIso_comp_hom_app, Category.assoc] using
        (NatTrans.shift_app_comm (S.reductionEvaluation n).hom r P).symm
  }
  exact ⟨x⟩

end WeilConjectures
