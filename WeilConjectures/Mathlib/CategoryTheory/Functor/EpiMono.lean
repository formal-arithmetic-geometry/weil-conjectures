/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Monomorphisms after two functors

If `s` is an isomorphism and `Φ.map (H.map τ)` is a monomorphism, so is `Φ.map (H.map (τ ≫ s))`;
similarly for `Φ.map (τ ≫ H.map s) ≫ Φ.map (H.map t)` with `s`, `t` isomorphisms.

Squares under a functor can be checked after composing with a monomorphism
(`CategoryTheory.Functor.map_comp_eq_comp_of_mono`).
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

/-- If `s` and `t` are isomorphisms and `Φ.map τ` is a monomorphism, so is
`Φ.map (τ ≫ H.map s) ≫ Φ.map (H.map t)`. -/
lemma mono_map_comp_map_map_comp_map_map_of_isIso (H : C ⥤ D) (Φ : D ⥤ E) {a : D} {b c d : C}
    (τ : a ⟶ H.obj b) (s : b ⟶ c) (t : c ⟶ d) [IsIso s] [IsIso t] (hτ : Mono (Φ.map τ)) :
    Mono (Φ.map (τ ≫ H.map s) ≫ Φ.map (H.map t)) := by
  rw [Φ.map_comp]
  infer_instance

/-- If `L ≫ K = M`, `L' ≫ K' = M'` with `K'` a monomorphism, `F K ≫ v = b ≫ K'` and
`F M ≫ v = a ≫ M'`, then `F L ≫ b = a ≫ L'`. -/
theorem map_comp_eq_comp_of_mono (F : C ⥤ D) {A C₁ D₁ : C} {A' C' D' : D} {L : A ⟶ C₁}
    {K : C₁ ⟶ D₁} {M : A ⟶ D₁} {L' : A' ⟶ C'} {K' : C' ⟶ D'} {M' : A' ⟶ D'} {a : F.obj A ⟶ A'}
    {b : F.obj C₁ ⟶ C'} {v : F.obj D₁ ⟶ D'} [Mono K'] (hLK : L ≫ K = M) (hLK' : L' ≫ K' = M')
    (hK : F.map K ≫ v = b ≫ K') (hM : F.map M ≫ v = a ≫ M') :
    F.map L ≫ b = a ≫ L' := by
  rw [← cancel_mono K', Category.assoc, ← hK, ← F.map_comp_assoc, hLK, hM, ← hLK',
    Category.assoc]

end CategoryTheory.Functor
