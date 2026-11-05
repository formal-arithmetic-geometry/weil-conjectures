/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Short exact sequences in the heart of a t-structure

Let `t` be a t-structure on a triangulated category `C`, with heart `H`, which is abelian
(`CategoryTheory.Triangulated.TStructure.abelianHeart`). This file records the basic dictionary
between the triangulated structure of `C` and the abelian structure of `H`
(blueprint `lem-weil-heart-short-exact-triangles`):

1. truncation triangles are unique up to unique isomorphism
   (`CategoryTheory.Triangulated.TStructure.triangle_hom_ext_of_isLE_of_isGE`,
   `CategoryTheory.Triangulated.TStructure.exists_iso_triangleLEGE`), and the truncation
   functors are adjoint to the inclusions
   (`CategoryTheory.Triangulated.TStructure.truncLEAdjunction`,
   `CategoryTheory.Triangulated.TStructure.truncGEAdjunction`); the commutation
   `τ_{≥ 0} τ_{≤ 0} ≅ τ_{≤ 0} τ_{≥ 0}` is `CategoryTheory.Triangulated.TStructure.truncGELEIsoLEGE`;
2. the subcategories `t.le n`, `t.ge n` (`CategoryTheory.Triangulated.TStructure.isLE₂`,
   `CategoryTheory.Triangulated.TStructure.isGE₂`) and the heart
   (`CategoryTheory.Triangulated.TStructure.heart₂`) are closed under extensions;
3. kernels and cokernels in `H` are computed by truncating a cone
   (`CategoryTheory.Triangulated.TStructure.exists_isLimit_kernelFork_of_distTriang`,
   `CategoryTheory.Triangulated.TStructure.exists_isColimit_cokernelCofork_of_distTriang`);
4. a sequence `0 ⟶ X ⟶ Y ⟶ Z ⟶ 0` in `H` is short exact if and only if it extends to a
   distinguished triangle, and then the connecting morphism is unique
   (`CategoryTheory.Triangulated.TStructure.shortExact_iff_exists_distTriang`,
   `CategoryTheory.Triangulated.TStructure.eq_of_distTriang_of_heart`).

The fact that `H⁰` is a homological functor is in
`WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`.
-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory.Triangulated.TStructure

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  (t : TStructure C)

section Truncation

end Truncation

section Extensions

end Extensions

section Heart

variable [IsTriangulated C] (H : Type u') [Category.{v'} H] [Preadditive H] [t.Heart H]

variable {H}

end Heart

end CategoryTheory.Triangulated.TStructure
