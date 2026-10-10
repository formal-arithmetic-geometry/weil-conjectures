/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.EpiMono

/-!
# Faithfulness along a natural transformation with monomorphic components

If `α : F ⟶ G` is a natural transformation whose components are monomorphisms and `F` is
faithful, then `G` is faithful (`CategoryTheory.Functor.Faithful.of_mono_app`).
-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D]

/-- If `α : F ⟶ G` has monomorphic components and `F` is faithful, then `G` is faithful: if
`G.map φ = G.map ψ`, then `F.map φ ≫ α.app Y = F.map ψ ≫ α.app Y` by naturality. -/
lemma Faithful.of_mono_app {F G : C ⥤ D} [F.Faithful] (α : F ⟶ G)
    (hα : ∀ X, Mono (α.app X)) : G.Faithful where
  map_injective {_ Y} φ ψ hφψ := F.map_injective <| (cancel_mono (α.app Y)).1 <| by
    rw [α.naturality, α.naturality, hφψ]

end CategoryTheory.Functor
