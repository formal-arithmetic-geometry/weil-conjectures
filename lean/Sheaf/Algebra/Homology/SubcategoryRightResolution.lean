/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Right resolutions with terms in a prescribed subset

Source: Stacks Project, Derived Categories, Lemma Tag 05T6, part (1)
(blueprint: lem-weil-pbc-subcategory-right-resolution-05T6).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex

/-- A bounded-below complex admits a degreewise monomorphic quasi-isomorphism to a complex
with the same lower bound and terms in any subset containing zero into which every object
embeds. Source: Stacks Project, Derived Categories, Lemma Tag 05T6, part (1)
(blueprint: lem-weil-pbc-subcategory-right-resolution-05T6).

Proof (the dual of Tag 05T7(1)):
1. For each `n ≥ a - 1`, build terms through degree `n`, differentials, and monomorphisms
   from `K`, commuting with differentials. Require isomorphisms on cohomology below `n`
   and a monomorphism on the cokernels of the differentials into degree `n`.
   Start at `a - 1` with zero objects, allowed by the zero-membership hypothesis.
2. Write `C_K` and `C_I` for these cokernels and form the pushout of `C_K → K.X (n + 1)`
   along the induced monomorphism `C_K → C_I`. Pushouts exist by
   `lem-weil-pbc-abelian-exact-epi-cokernel` and `def-weil-pbc-category-colimit`.
   Embed the pushout into a member of the subset. Its map from `K.X (n + 1)` is mono by
   `lem-weil-pbc-abelian-pushout-mono`, so the resulting component of the augmentation is
   mono. Define the new differential by composing `I.X n → C_I` with the pushout map
   and this embedding.
3. The pushout square gives commutation with differentials. The cokernel projection
   kills the preceding differential, so consecutive differentials compose to zero.
4. Identify degree-`n` cohomology with the kernel of the map out of the cokernel using
   `lem-weil-pbc-cohomology-kernel-on-cokernel`. The new embedding does not change kernels.
   The induced kernel map is an isomorphism by `lem-weil-pbc-pushout-kernel-iso`, giving
   the required cohomology isomorphism in degree `n`.
5. The map on cokernels in degree `n + 1` factors through the cokernel of the pushout map.
   Its first factor is an isomorphism by `lem-weil-pbc-pushout-cokernel-iso` and the second
   is mono by `lem-weil-pbc-cokernel-map-mono-of-mono`. This preserves the induction
   hypothesis in degree `n + 1` without changing the previously constructed data.
6. Ascending recursion gives a complex and a morphism from `K`, using
   `def-weil-abstract-derived-category`. All components are mono, all terms belong to the
   subset, and all terms below `a` are zero. Each cohomology map is an isomorphism by
   the induction hypothesis at the next degree, hence the morphism is a quasi-isomorphism.
-/
theorem exists_mono_quasiIso_in_subcategory
    (C : Type u) [Category.{v} C] [Abelian C]
    (𝓘 : Set C) (hzero : (0 : C) ∈ 𝓘)
    (hembed : ∀ X : C, ∃ (Y : C) (f : X ⟶ Y), Y ∈ 𝓘 ∧ Mono f)
    (a : ℤ) (K : CochainComplex C ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.X n)) :
    ∃ (I : CochainComplex C ℤ) (α : K ⟶ I),
      QuasiIso α ∧ (∀ n : ℤ, Mono (α.f n)) ∧
      (∀ n : ℤ, I.X n ∈ 𝓘) ∧ (∀ n : ℤ, n < a → IsZero (I.X n)) := by
  sorry

end CochainComplex
