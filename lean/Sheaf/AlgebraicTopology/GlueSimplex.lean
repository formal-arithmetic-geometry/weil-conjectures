/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Gluing a simplex to a simplicial subset
Source: literature/stacks-project/simplicial.tex,
Lemma 018R (blueprint: lem-weil-pbc-simplicial-set-glue-simplex)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Simplicial
universe u

namespace SSet

/-- Adding one simplex to a simplicial subset is a pushout along its boundary.
Source: Stacks Project, Lemma 018R (blueprint: lem-weil-pbc-simplicial-set-glue-simplex).
Proof:
1. The simplex `x` is nondegenerate: a lower-dimensional ancestor belongs to `U` by
   `hbelow`, contradicting `hx`. A non-surjective map to `[n]` factors through a missing
   face (lem-weil-pbc-simplex-face-factorization); that face of `x` lies in `U` by
   `hbelow`. Thus the simplex map restricts to a boundary map `b`. For `n = 0` the
   boundary is empty.
2. By unique nondegenerate decomposition
   (lem-weil-pbc-simplicial-set-nondegenerate-decomposition), every simplex outside `U`
   has a nondegenerate ancestor outside `U`. The ancestor cannot have degree below `n`
   by `hbelow`, or above `n` by `habove`; `hat` identifies it with `x`. Thus each new
   simplex is the image of `x` under a unique surjection. Such an image cannot lie in
   `U`, since an order-preserving section would then put `x` in `U`.
3. Given maps `g : U → Y` and `h : Δ[n] → Y` agreeing on the boundary, define the
   extension by `g` on `U` and by `h` on the unique surjections of step 2. Under a
   simplicial operator, a composite that remains surjective uses step 2; a composite
   that is not surjective uses step 1 and the boundary agreement. This proves naturality.
4. The same two cases show that the extension composed with the simplex map is `h`.
   Any extension agrees on `U` and on every degeneracy of `x`, so it is unique. This is
   the pushout universal property. When `n = 0`, all maps to `[0]` are surjective and
   the empty boundary makes this the coproduct `U ∐ Δ[0]`.
-/
theorem glue_simplex
    {X : SSet.{u}} (U V : X.Subcomplex) (hUV : U ≤ V)
    {n : ℕ}
    (x : (V.toSSet).obj (Opposite.op (SimplexCategory.mk n)))
    (hx : x.1 ∉ U.obj (Opposite.op (SimplexCategory.mk n)))
    (hbelow : ∀ i : ℕ, i < n →
      V.obj (Opposite.op (SimplexCategory.mk i)) = U.obj (Opposite.op (SimplexCategory.mk i)))
    (hat : V.obj (Opposite.op (SimplexCategory.mk n)) =
      U.obj (Opposite.op (SimplexCategory.mk n)) ∪ {x.1})
    (habove : ∀ j : ℕ, n < j → ∀ z : (V.toSSet).obj (Opposite.op (SimplexCategory.mk j)),
      z.1 ∉ U.obj (Opposite.op (SimplexCategory.mk j)) →
      z ∈ (V.toSSet).degenerate j) :
    ∃ b : (SSet.boundary n).toSSet ⟶ U.toSSet,
      b ≫ Subcomplex.homOfLE hUV = (SSet.boundary n).ι ≫ SSet.yonedaEquiv.symm x ∧
      IsPushout b (SSet.boundary n).ι (Subcomplex.homOfLE hUV)
        (SSet.yonedaEquiv.symm x) := by
  sorry

end SSet
