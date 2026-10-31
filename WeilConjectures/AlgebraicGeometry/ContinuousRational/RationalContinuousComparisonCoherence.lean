/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalRealizationData
import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousAmbientGeometricCoherence
import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousIntegralScalarTower
import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousMixedIntegralComponent

/-! # Coherence forced by normalized tensor and completion comparisons

Source: Bhatt--Scholze, Remark 6.8.15; Stacks 0D6D, 0A0E and 0A0G
(blueprint: lem-per-rational-continuous-comparison-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.ContinuousRational

private def realizationFullyFaithful (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X : Base.{u} l} (a : At l E X) :
    a.J.FullyFaithful where
  preimage {K L} f := (Equiv.ofBijective _ (a.fully_faithful K L)).symm f
  map_preimage f := (Equiv.ofBijective _ (a.fully_faithful _ _)).apply_symm_apply f
  preimage_map f := (Equiv.ofBijective _ (a.fully_faithful _ _)).symm_apply_apply f

end AlgebraicGeometry.Scheme.ContinuousRational
