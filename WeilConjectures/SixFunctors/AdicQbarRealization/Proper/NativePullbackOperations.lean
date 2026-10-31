/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackCoefficientMap
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackCounit
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackDerivedAdjunction

/-! # The actual normalized ambient native inverse-image operations

Source: Bhatt--Scholze Remark 6.8.15; Stacks Tags 03D7, 0DVC and 0FND.
(blueprint: lem-sf-native-pullback-operations)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper

/-- The native coefficient inverse image has its normalized ordinary and derived
adjunctions on the whole ambient module categories, before any constructibility claim.
Source: Bhatt--Scholze Remark 6.8.15; Stacks Tags 03D7, 0DVC and 0FND.
(blueprint: lem-sf-native-pullback-operations).

Proof: the coefficient inverse-image theorem gives the precomposition-normalized
coefficient isomorphism. Compose module inverse image with scalar extension to obtain
the unique ordinary adjunction whose unit inserts one. A left adjoint between these
additive categories is additive. Cancel the identity coefficient factor in the exact
inverse-image API to obtain the normalized derived computation counit. Since the
coefficient map is an isomorphism, ordinary pullback is exact. Its derived adjunction,
transported along the normalized counit, has exactly the cochain transpose formula.
The coefficient map, the two adjunctions and the counit with these proved equations
fill the fields of Operations. No assumption on properness or finite type is used. -/
theorem nativePullbackOperations (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) :
    Nonempty (Operations l p R S) := by
  obtain ⟨c, hc, hfunctions⟩ := nativePullbackCoefficientMap l p R S
  letI := hc
  obtain ⟨a, ha, _⟩ := nativePullbackModuleAdjunction l p R S c
  letI : (ContinuousRational.modulePull p c).Additive := a.left_adjoint_additive
  obtain ⟨δ, hδ⟩ := nativePullbackCounit p c
  obtain ⟨ad, ht⟩ := nativePullbackDerivedAdjunction p c a δ hδ
  exact ⟨{
    coefficient := c
    functions := hfunctions
    moduleAdjunction := a
    unit_sections := ha
    pullCounit := δ
    pull_normalized := hδ
    adjunction := ad
    transpose := ht }⟩

end WeilConjectures.AdicQbarRealization.Proper
