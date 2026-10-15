/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Triangulated.TStructure.AbelianSubcategory
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-!
# Abelian hearts and supplementary kernels of idempotents

Source: BBD, Theorem 1.3.6 and Proposition 1.2.4; Stacks Project, Tag 0H9Q
(blueprint: prop-weil-heart-abelian).
-/

@[expose] public section

universe u v u' v'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Triangulated.TStructure

/-- The heart is abelian; in any abelian category an idempotent is the projection onto
`ker(1-e)` in the decomposition `ker(e) ⊞ ker(1-e)`.
Source: BBD, Theorem 1.3.6 and Proposition 1.2.4; Stacks Project, Tag 0H9Q
(blueprint: prop-weil-heart-abelian).

Proof plan: extension closure (`lem-sbc-tstructure-extension-closure`) puts the zero
object and, using the split distinguished triangle
(`lem-sbc-biproduct-triangle-distinguished`), binary biproducts in the heart. The
inclusion is full, faithful and additive. Shift stability and orthogonality in
`def-weil-t-structure` imply that negative shifted Hom groups between heart objects
vanish. Complete a heart morphism to a distinguished triangle (`def-weil-triangulated-category`);
its cone lies in degrees [-1,0]. Truncate that cone at (-1,0), obtaining a triangle
`K[1] → S → Q → K[2]` with K and Q in the heart, by extension closure and shift
stability. Apply `lem-sbc-abelian-subcategory-criterion` to obtain abelianity
(`def-sp-abelian`); this is also the existing upstream `abelianHeart` theorem.

For the supplementary assertion put g = 1-e. The identities eg = ge = 0 give
maps p : A → ker(e) and q : A → ker(g), whose composites with the kernel
inclusions i and j are g and e. Monicity gives i ≫ p = 1, j ≫ q = 1 and the
cross composites zero. Thus the maps (i,j) and (p,q) are inverse, because
g+e=1. The identities i ≫ e = 0 and j ≫ e = j identify e with the second
projection. This applies in particular to the abelian heart. -/
theorem heart_abelian_and_idempotent_kernel_decomposition
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [Pretriangulated C] [IsTriangulated C] (t : TStructure C) :
    Nonempty (Abelian t.heart.FullSubcategory) ∧
      ∀ (D : Type u') [Category.{v'} D] [Abelian D] (A : D) (e : A ⟶ A),
        e ≫ e = e →
          ∃ φ : A ≅ (kernel e ⊞ kernel (𝟙 A - e)),
            φ.inv = biprod.desc (kernel.ι e) (kernel.ι (𝟙 A - e)) ∧
              φ.inv ≫ e ≫ φ.hom = biprod.snd ≫ biprod.inr := by
  sorry

end CategoryTheory.Triangulated.TStructure
