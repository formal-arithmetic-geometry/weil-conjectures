/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

import Mathlib.CategoryTheory.Abelian.CommSq
import Sheaf.Algebra.Homology.SubcategoryRightResolutionSystem

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

private theorem quasiIsoAt_of_pushout_factorization
    {C : Type u} [Category.{v} C] [Abelian C]
    {K I : CochainComplex C ℤ} (α : K ⟶ I) (n : ℤ)
    [Mono (HomologicalComplex.opcyclesMap α n)]
    {P : C} (u : K.X (n + 1) ⟶ P) (v : I.opcycles n ⟶ P)
    (j : P ⟶ I.X (n + 1)) [Mono j]
    (sq : IsPushout (K.fromOpcycles n (n + 1)) (HomologicalComplex.opcyclesMap α n) u v)
    (hv : v ≫ j = I.fromOpcycles n (n + 1)) : QuasiIsoAt α n := by
  let f := K.fromOpcycles n (n + 1)
  let g := HomologicalComplex.opcyclesMap α n
  let k := kernel.map f v g u sq.w
  have : Epi k := Abelian.epi_kernel_map_of_isPushout sq
  have : Mono k := mono_of_mono_fac (show k ≫ kernel.ι v = kernel.ι f ≫ g by
    simp [k])
  have : IsIso k := isIso_of_mono_of_epi k
  let t : K.homology n ⟶ kernel f :=
    kernel.lift f (K.homologyι n) (K.homologyι_comp_fromOpcycles n (n + 1))
  let t' : kernel f ⟶ K.homology n :=
    (K.homologyIsKernel n (n + 1) (by simp)).lift (KernelFork.ofι (kernel.ι f)
      (kernel.condition f))
  have htι : t' ≫ K.homologyι n = kernel.ι f :=
    (K.homologyIsKernel n (n + 1) (by simp)).fac _ WalkingParallelPair.zero
  have ht : t ≫ t' = 𝟙 _ := by
    apply (cancel_mono (K.homologyι n)).1
    simp [t, htι, Category.assoc]
  have ht' : t' ≫ t = 𝟙 _ := by
    apply (cancel_mono (kernel.ι f)).1
    simp [t, htι, Category.assoc]
  have : IsIso t := ⟨t', ht, ht'⟩
  let l : kernel v ⟶ I.homology n :=
    (I.homologyIsKernel n (n + 1) (by simp)).lift (KernelFork.ofι (kernel.ι v) (by
      rw [← hv, ← Category.assoc, kernel.condition, zero_comp]))
  let l' : I.homology n ⟶ kernel v :=
    kernel.lift v (I.homologyι n) (by
      apply (cancel_mono j).1
      simp [Category.assoc, hv])
  have hlι : l ≫ I.homologyι n = kernel.ι v :=
    (I.homologyIsKernel n (n + 1) (by simp)).fac _ WalkingParallelPair.zero
  have hl : l ≫ l' = 𝟙 _ := by
    apply (cancel_mono (kernel.ι v)).1
    simp [l', hlι, Category.assoc]
  have hl' : l' ≫ l = 𝟙 _ := by
    apply (cancel_mono (I.homologyι n)).1
    simp [l', hlι, Category.assoc]
  have : IsIso l := ⟨l', hl, hl'⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have eq : HomologicalComplex.homologyMap α n = t ≫ k ≫ l := by
    apply (cancel_mono (I.homologyι n)).1
    simp [t, k, g, hlι, Category.assoc]
  rw [eq]
  infer_instance

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
  obtain ⟨I, α, hmono, hmem, hbound, hop, hsq⟩ :=
    exists_subcategory_right_resolution_system C 𝓘 hzero hembed a K hK
  refine ⟨I, α, ?_, hmono, hmem, hbound⟩
  rw [quasiIso_iff]
  intro n
  have : Mono (HomologicalComplex.opcyclesMap α n) := hop n
  obtain ⟨P, u, v, j, hj, sq, _, hv⟩ := hsq n
  have : Mono j := hj
  exact quasiIsoAt_of_pushout_factorization α n u v j sq hv

end CochainComplex
