/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackOrdinaryCompositionLaws
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackDerivedCompositionLaws

/-! # Components of ambient pullback coherence

## References

* [Stacks, Tag 03CB]
* [Stacks, Tag 03D3]
* [Stacks, Tag 03EL]
* [Stacks, Tag 07A4]
* [Stacks, Tag 04VG]
* [Stacks, Tag 0B65]
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

/-- Associativity and the two unit laws for the specified pullback comparisons. -/
theorem pullback_compositionLaws (K : Scheme.{t}) (s : Option ℕ) :
    CompositionLaws ell E K s := by
  obtain ⟨ho₁, ho₂, ho₃⟩ := ordinary_pullback_compositionLaws ell E K s
  obtain ⟨hd₁, hd₂, hd₃⟩ := derived_pullback_compositionLaws ell E K s
  exact ⟨ho₁, ho₂, ho₃, hd₁, hd₂, hd₃⟩

end WeilConjectures.AmbientPullbackTensor
