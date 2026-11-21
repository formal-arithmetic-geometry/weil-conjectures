/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackSiteData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientCoefficientPullbackFiniteIso
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientCoefficientSequencePullbackIso

/-! # Components of ambient pullback coherence

## References

* [Stacks, Tag 03CB]
* [Stacks, Tag 03D3]
* [Stacks, Tag 03EL]
* [Stacks, Tag 07A4]
* [Stacks, Tag 04VG]
* [Stacks, Tag 0H7J]
* [Stacks, Tag 0941]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]
attribute [local irreducible] pull CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

/-- Inverse image preserves the actual coefficient ring, on the finite or sequence site. -/
theorem coefficientPullback_isIso {X Y : Scheme.{t}} (f : X ⟶ Y) (s : Option ℕ) :
    IsIso (ringMap ell E f s) := by
  cases s with
  | some n => exact coefficientPullback_some_isIso ell E f n
  | none => exact coefficientPullback_none_isIso ell E f

end WeilConjectures.AmbientPullbackTensor
