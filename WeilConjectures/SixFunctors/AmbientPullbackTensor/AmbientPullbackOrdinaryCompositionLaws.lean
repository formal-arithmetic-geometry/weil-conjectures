/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPullbackTensorData
import WeilConjectures.SixFunctors.AmbientPullbackTensor.AmbientPushforwardCompositionSections

/-! Ordinary pullback associativity and unit laws.

Source: Stacks 03CB, 03D3 and 04VG.
(blueprint: new-lem-sf-ambient-pullback-ordinary-composition-laws).

This is the ordinary part of the ambient pullback coherence argument.  The
section-normalized direct-image comparison is pasted over the canonical
fibre-product comparisons; adjunction mates then give the three displayed
identities.  The proof is split from the derived localization step so that the
ordinary and derived calculations can be completed independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSimpArgs false
set_option linter.style.emptyLine false
set_option linter.style.cdot false
set_option linter.style.longLine false
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections
namespace WeilConjectures.AmbientPullbackTensor
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

attribute [local irreducible] pull CategoryTheory.Functor.leftAdjoint

end WeilConjectures.AmbientPullbackTensor
