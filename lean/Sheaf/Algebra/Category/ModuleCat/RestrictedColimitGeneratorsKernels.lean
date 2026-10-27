/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Restricted module colimits from generators and kernel capture

Source: Stacks Project, Algebra, Tag 059W (`lemma-ML-countable-colimit`),
final two proof paragraphs (blueprint: lem-trf-restricted-colimit-generators-kernels).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Generators represented in a directed subposet and eventual capture of all
transition kernels make the canonical restricted-colimit map an isomorphism.

Source: Stacks Project, Algebra, Tag 059W (`lemma-ML-countable-colimit`),
final two proof paragraphs (blueprint: lem-trf-restricted-colimit-generators-kernels).

Proof:
1. Express any target element as a finite linear combination of elements of `E`.
   Represent these generators at stages of `J`, and move the finitely many representatives
   to a common upper stage in `J`. For the empty sum, choose any stage using nonemptiness.
   This proves that every target element is represented at a stage in `J`.
2. If a stage element maps to zero in the target, the elementwise filtered-colimit
   description (lem-weil-pbc-filtered-colimit-modules-elementwise) gives a later stage
   in `I` killing it. Kernel capture gives a stage in `J` killing it, without requiring
   that this stage dominate the previously found stage in `I`.
3. Apply the filtered-module-colimit criterion
   (lem-weil-pbc-filtered-colimit-modules-criterion) to the restricted cocone. Step 1
   gives its representative condition; apply Step 2 to a difference for its equality
   condition. Thus the restricted cocone is colimiting.
4. The two colimit universal properties (def-weil-pbc-category-colimit) produce mutually
   inverse maps between its target and the chosen restricted colimit. Their composites
   are identities by uniqueness, so the specified `colimit.desc` is an isomorphism.
-/
theorem isIso_restrictedColimit_of_generators_kernel_capture
    (R : Type u) [CommRing R]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ ModuleCat.{max u v w} R) (c : Cocone F) (hc : IsColimit c)
    (J : Set I) [Nonempty J] [IsDirected J (· ≤ ·)]
    (E : Set c.pt) (hspan : Submodule.span R E = ⊤)
    (hrepresent : ∀ x ∈ E, ∃ (i : J) (y : F.obj i.val), c.ι.app i.val y = x)
    (hkernel : ∀ i : J, ∃ (j : J) (hij : i.val ≤ j.val),
      ∀ (k : I) (hik : i.val ≤ k),
        LinearMap.ker (F.map (homOfLE hik)).hom ≤
          LinearMap.ker (F.map (homOfLE hij)).hom) :
    IsIso (colimit.desc ((Subtype.mono_coe (· ∈ J)).functor ⋙ F)
      (c.whisker (Subtype.mono_coe (· ∈ J)).functor)) := by
  sorry

end ModuleCat
