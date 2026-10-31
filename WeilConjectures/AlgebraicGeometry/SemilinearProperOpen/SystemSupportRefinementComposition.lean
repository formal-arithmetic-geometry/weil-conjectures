/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SystemSupportRefinement
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
/-! # Composition of whole-system compact-support refinements

Source: Stacks Tags 0F7C and 07A7; latest blueprint,
`sk-prop-sf-comp-coherence`, composition of refinement comparisons.
(blueprint: lem-pur-system-support-refinement-composition). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.proofsInPublic true
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofHasKInjectiveResolutions _root_.instCategoryDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
attribute [local instance 2000] WeilConjectures.SemilinearSections.moduleAbelian derived
attribute [local irreducible] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] J R gamma sComp sId derived

end AlgebraicGeometry.ProEtale.SemilinearProperOpen
