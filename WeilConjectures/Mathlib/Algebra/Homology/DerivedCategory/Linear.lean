/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Torsion in the derived category

If an integer `N` kills every object of an abelian category `C`, then it kills every object of
the derived category `D(C)`.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If `N • 𝟙 M = 0` for every object `M` of `C`, then `N • 𝟙 K = 0` for every object `K` of
the derived category `D(C)`: `K` is the image under `Q` of a complex, which is killed by `N`
degreewise. -/
lemma nsmul_id_eq_zero_of_forall {N : ℕ} (h : ∀ M : C, N • 𝟙 M = 0) (K : DerivedCategory C) :
    N • 𝟙 K = 0 := by
  let e := Q.objObjPreimageIso K
  have hL : N • 𝟙 (Q.objPreimage K) = 0 := by
    ext n
    simp [h]
  have hQ : N • 𝟙 (Q.obj (Q.objPreimage K)) = 0 := by
    rw [← Q.map_id, ← Functor.map_nsmul, hL, Q.map_zero]
  rw [← cancel_epi e.hom, Preadditive.comp_nsmul, Category.comp_id, ← Category.id_comp e.hom,
    ← Preadditive.nsmul_comp, hQ, Limits.zero_comp, Limits.comp_zero]

end DerivedCategory
