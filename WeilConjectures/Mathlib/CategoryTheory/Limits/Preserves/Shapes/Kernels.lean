/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The image of the inclusion of a kernel under a kernel preserving functor

If `G` preserves the kernel of `f`, the morphism `G.map (kernel.ι f)` is the inclusion of the
kernel of `G.map f`, read through the comparison isomorphism `PreservesKernel.iso`.

## Main results

* `CategoryTheory.Limits.map_kernelι_eq`: `G.map (kernel.ι f)` factors as
  `(PreservesKernel.iso G f).hom ≫ kernel.ι (G.map f)`.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  {M N : C} (f : M ⟶ N) [HasKernel f] (G : C ⥤ D) [G.PreservesZeroMorphisms]
  [HasKernel (G.map f)] [PreservesLimit (parallelPair f 0) G]

/-- A kernel preserving functor sends the inclusion of the kernel of `f` to the inclusion of the
kernel of `G.map f`, composed with the comparison isomorphism:

```
G (kernel f) --- G (kernel.ι f) ---> G M
     |                                ‖
PreservesKernel.iso                   ‖
     v                                v
kernel (G.map f) --- kernel.ι ---->  G M
```
-/
lemma map_kernelι_eq :
    G.map (kernel.ι f) = (PreservesKernel.iso G f).hom ≫ kernel.ι (G.map f) := by
  rw [← PreservesKernel.iso_inv_ι]
  simp

end CategoryTheory.Limits
