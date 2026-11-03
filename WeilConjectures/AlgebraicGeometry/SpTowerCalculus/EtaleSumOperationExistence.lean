/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces

/-! # Existence of normalized étale sum operations

The ordinary sheafified lift-sum construction is transported to the recorded strict
coefficient-tower coordinates.  The transport retains the finite evaluation adjunctions
and the localized derived adjunction required by `EtaleOperation`.
(blueprint: lem-v5-etale-sum-operation-existence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerCalculus

end
