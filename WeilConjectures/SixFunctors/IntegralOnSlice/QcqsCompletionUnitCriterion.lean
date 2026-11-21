/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices

/-! # The specified completion unit detects derived completeness

## References

* [Stacks, Tag 099M]
* Bhatt–Scholze, *The pro-étale topology for schemes*, Definition 3.5.2
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice
/-- The specified quotient/Roos completion unit is invertible precisely on derived
complete objects, without a finiteness hypothesis on the scheme. -/
theorem canonicalCompletionUnitCriterion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (T : Scheme.{t}) :
    (∀ H : D l E T none,
      IsIso ((completionUnit l E T none).app H) ↔ IsComplete l E T none H)
 := by
  intro H
  obtain ⟨d, hd', _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  let := goodLocalization l E T none
  let := Localization.essSurj (qGood l E T none)
    ((HomologicalComplex.quasiIso (Mod l E T none) (.up ℤ)).inverseImage
      (Good l E T none).ι)
  let P := (qGood l E T none).objPreimage H
  let e : DerivedCategory.Q.obj P.obj ≅ H := (qGood l E T none).objObjPreimageIso H
  by_cases h : l = 2
  · subst l
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact (roosIntrinsicCompletenessEquivalence 3 2 (by decide) E T d hd' H P e).out 5 1
  · have : Fact (Nat.Prime 2) := ⟨by decide⟩
    exact (roosIntrinsicCompletenessEquivalence 2 l (Ne.symm h) E T d hd' H P e).out 5 1

end WeilConjectures.IntegralOnSlice
