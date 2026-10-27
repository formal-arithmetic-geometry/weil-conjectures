module

public import Sheaf.Paper.SfAmbientIntegralDirectImage
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Mathlib.CategoryTheory.Shift.CommShift

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Natural shifts of the ambient integral ordinary direct image

Source: latest blueprint, fix-cor-verdier-exchange.proof.md, Step 3, compatibility
with shifts of the second arrow of Step 2; Stacks 08TC and 0941
(blueprint: lem-sf-integral-direct-image-shift-comparison).

The functor is the actual reduction/direct-image/total-limit realization, on the
whole unbounded derived category of modules over completed coefficient sheaves.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory
namespace WeilConjectures

/-- Integer shifts commute naturally with the integral direct-image realization.
The zero comparison is the identity after the canonical identifications of [0]
with the identity functor. A natural isomorphism includes naturality for every
arrow of the ambient derived category, hence also inverse quasi-isomorphisms.
Source: latest blueprint, fix-cor-verdier-exchange.proof.md, Step 3, compatibility
with shifts of the second arrow of Step 2; Stacks 08TC and 0941
(blueprint: lem-sf-integral-direct-image-shift-comparison).

Proof:
1. The specified sequence limit is exact scalar restriction followed by the total
right-derived inverse limit on strict completed-coefficient towers. Exact functors
and unbounded right-derived additive functors have their standard CommShift
structures, so this sequence limit commutes naturally with every integer shift.
2. The recorded coefficient calculus supplies the actual adjunction from reduction
to that sequence limit. Transfer its right adjoint's CommShift structure to the
reduction functor by the adjunction mate construction. This uses the same reduction
functor, with all its strict quotient transitions, on the entire ambient category.
3. In sfAmbientIntegralDirectImage, compose that reduction comparison with those
of exact scalar restriction, the unbounded right-derived tower direct image, and
the total right-derived inverse limit. Functor composition supplies naturality for
all derived arrows, including inverse quasi-isomorphisms. The CommShift zero law
identifies the resulting zero comparison with CommShift.isoZero. No boundedness,
constructibility or completeness hypothesis is used. -/
theorem sfIntegralDirectImageShiftComparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : AlgebraicGeometry.Scheme.{t}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ θ : ∀ r : ℤ,
        shiftFunctor (DerivedCategory (scalarReductionSource l E X)) r ⋙
            sfAmbientIntegralDirectImage l E f ≅
          sfAmbientIntegralDirectImage l E f ⋙
            shiftFunctor (DerivedCategory (scalarReductionSource l E Y)) r,
      θ 0 = Functor.CommShift.isoZero (sfAmbientIntegralDirectImage l E f) ℤ := by
  classical
  let limitShift (W : AlgebraicGeometry.Scheme.{t}) :
      (coefficientConstantTowerLimit l E W).CommShift ℤ := by
    unfold coefficientConstantTowerLimit
    infer_instance
  let sequenceLimitShift : (coefficientSequenceLimit l E X).CommShift ℤ := by
    unfold coefficientSequenceLimit
    infer_instance
  let reductionShift :
      (coefficientDerivedSystemEvaluationCalculus l E X).choose.reduction.CommShift ℤ :=
    (coefficientDerivedSystemEvaluationCalculus l E X).choose.adjunction.leftAdjointCommShift ℤ
  let imageShift : (sfAmbientIntegralDirectImage l E f).CommShift ℤ := by
    unfold sfAmbientIntegralDirectImage
    infer_instance
  exact ⟨fun r ↦ (sfAmbientIntegralDirectImage l E f).commShiftIso r,
    (sfAmbientIntegralDirectImage l E f).commShiftIso_zero ℤ⟩

end WeilConjectures
