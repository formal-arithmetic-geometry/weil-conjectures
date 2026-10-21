/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Monomorphisms after two functors

If `s` is an isomorphism and `Φ.map (H.map τ)` is a monomorphism, so is `Φ.map (H.map (τ ≫ s))`.
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- If `s` is an isomorphism and `Φ.map (H.map τ)` is a monomorphism, so is
`Φ.map (H.map (τ ≫ s))`. -/
lemma mono_map_map_comp_of_isIso (H : C ⥤ D) (Φ : D ⥤ E) {a b c : C} (τ : a ⟶ b) (s : b ⟶ c)
    [IsIso s] (hτ : Mono (Φ.map (H.map τ))) : Mono (Φ.map (H.map (τ ≫ s))) := by
  rw [H.map_comp, Φ.map_comp]
  infer_instance

end CategoryTheory.Functor
