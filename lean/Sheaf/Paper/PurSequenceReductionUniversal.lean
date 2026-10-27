/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J8
-/
module

public import Sheaf.Paper.PurSequenceKFlatComparisonData

import Sheaf.Algebra.Homology.StrictCoefficientTensorDescent
import Sheaf.Paper.RingedTopoiDerivedPullbackIndependent
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Universal normalized quotient-sequence reduction

Source: Stacks 06YY, 06YS, 0G7D.
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

/-- The ordinary quotient pullback and supplied reduction have the same normalized
universal left-derived pair.
Source: Stacks, sites-cohomology.tex, Tags 06YY, 06YS and 0G7D;
the first two steps of lem-pur-sequence-kflat-comparison-shifts.
(blueprint: lem-pur-sequence-reduction-universal).

Proof: the ordinary pullback has nth fiber Q tensor B_n by O.tensor; O.tensor_transition
identifies every horizontal map with the actual quotient map. Apply the ringed-topos
pullback theorem to the constant-system inverse image and quotient structural map.
Flat-term K-flat resolutions exist for all complexes. The strict tensor descent theorem
therefore computes this universal pair and the supplied reduction by the same resolving
functor. The reduction-model normalization in hS identifies its finite evaluations and
horizontal maps with O.tensor, on morphisms as well as on objects. Descent through the
resolving localization transports the universal counit to S.reduction; the counit is
invertible on resolving representatives and its finite squares are the recorded
CoefficientReductionPresentation. This proves the universal property directly for the
supplied functor, without choosing a second derived pair. No independent finite replacements
or transitions
are chosen. -/
theorem purSequenceReductionUniversal
    (F : FiniteFieldDatum.{t}) (hl : l ≠ F.p)
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S)
    (O : PurSequenceOrdinaryAdjoints l E W) :
    ∃ ε : DerivedCategory.Q ⋙ S.reduction ⟶
        O.pullback.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q,
      S.reduction.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (scalarReductionSource l E W) (.up ℤ)) ∧
      ∀ (Q : CochainComplex (scalarReductionSource l E W) ℤ)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients
          (J := Scheme.ProEt.topology W)
          (R := completedIntegralCommRingSheafUnrestricted l E W) Q),
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (J := Scheme.ProEt.topology W)
          (R := completedIntegralCommRingSheafUnrestricted l E W) (Q.X i)) →
        ∃ e : S.reduction.obj (DerivedCategory.Q.obj Q) ≅
            DerivedCategory.Q.obj ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q),
          ε.app Q = e.hom ∧
          CoefficientReductionPresentation l E W S.toCoefficientDerivedSystemReduction Q hQ
            ((O.pullback.mapHomologicalComplex (.up ℤ)).obj Q) e
            (fun n ↦ (NatIso.mapHomologicalComplex (O.tensor n) (.up ℤ)).app Q) := by sorry

end WeilConjectures
