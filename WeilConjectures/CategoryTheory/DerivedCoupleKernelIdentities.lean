/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
set_option linter.privateModule false  -- prune: only private declarations remain

/-!
# Kernel and image identities for an exact-couple differential

Source: Stacks Project, Lemma 12.21.2 and Remark 12.21.5 (Tags 011R and 0AMJ).
-/

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

private theorem pullback_kernelSubobject
    {C : Type u} [Category.{v} C] [Abelian C] {A B T : C}
    (f : A ⟶ B) (g : B ⟶ T) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g) := by
  apply le_antisymm
  · apply Subobject.le_of_factors
    apply kernelSubobject_factors
    have hw := (Subobject.isPullback f (kernelSubobject g)).w
    rw [← Category.assoc, ← hw, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  · apply Subobject.le_of_factors
    apply pullback_factors
    apply kernelSubobject_factors
    rw [Category.assoc, kernelSubobject_arrow_comp]

end CategoryTheory.BigradedExactCouple
