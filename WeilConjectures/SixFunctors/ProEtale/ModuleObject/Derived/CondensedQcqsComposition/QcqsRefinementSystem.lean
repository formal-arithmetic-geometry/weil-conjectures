/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedQcqsComposition.CondensedQcqsCompositionDefs

/-! Coherent compactification system for one qcqs morphism.
(blueprint: new-p3-qcqs-refinement-system)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
open CompactSupportComposition
variable (ℓ : ℕ) [Fact ℓ.Prime]
def RefinementSystemData {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  Nonempty (System ℓ f)

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedQcqsComposition
