/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transport of mates along comparison functors

Given two squares of adjunctions and comparison functors between them, compatible with the
left adjoints, a natural transformation compatible with the comparisons has a mate that is
compatible with the comparisons, the right adjoints being compared by the mates of the
left-adjoint comparisons.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8
(blueprint: thm-cbc-complete-proetale).
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory

variable {S V T W S' V' T' W' : Type*} [Category S] [Category V] [Category T] [Category W]
  [Category S'] [Category V'] [Category T'] [Category W']
  {L₁ : S ⥤ V} {R₁ : V ⥤ S} (adj₁ : L₁ ⊣ R₁) {L₂ : T ⥤ W} {R₂ : W ⥤ T} (adj₂ : L₂ ⊣ R₂)
  {L₁' : S' ⥤ V'} {R₁' : V' ⥤ S'} (adj₁' : L₁' ⊣ R₁')
  {L₂' : T' ⥤ W'} {R₂' : W' ⥤ T'} (adj₂' : L₂' ⊣ R₂')

end CategoryTheory
