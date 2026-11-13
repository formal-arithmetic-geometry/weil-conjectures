/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # The adjunction for locally constant integer-valued functions

## Implementation details

The source module's private natural Hom equivalence is reused through `import all`.

## References

* Stacks Project, Tag 097D.
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- The locally constant integer algebra functor is a right adjoint (Stacks, Tag 097D). -/
theorem profiniteToCommRingCatOp_isRightAdjoint :
    profiniteToCommRingCatOp.{u}.IsRightAdjoint :=
  ⟨_, ⟨Adjunction.adjunctionOfEquivLeft profiniteLocallyConstantHomEquiv
    profiniteLocallyConstantHomEquiv_naturality⟩⟩

end AlgebraicGeometry.ProEtale
