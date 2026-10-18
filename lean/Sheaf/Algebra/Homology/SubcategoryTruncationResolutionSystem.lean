/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Compatible bounded-above resolutions from a quotient-generating class

Source: Stacks Project, Derived Categories, Tag 06XX, derived-lemma-special-direct-system
(statement and proof, including the strictification of the homotopy square and final
epicification).
(blueprint: lem-sfb-subcategory-truncation-resolution-system)

This module states the compatible resolution system for the good truncations of a
cochain complex. The proof follows the eight steps recorded in the node: the initial
resolution, the cone resolution, the shifted cone with split inclusion, the triangle
comparison, strictification, and the two-term identity-complex correction.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The canonical inclusion from the good truncation at `n` to that at `n + 1`.

Source: Stacks Project, Derived Categories, Tag 06XX, derived-lemma-special-direct-system.
(blueprint: lem-sfb-subcategory-truncation-resolution-system)
-/
noncomputable def subcategoryTruncationMap
    {C : Type u} [Category.{v} C] [Abelian C]
    (K : CochainComplex C ℤ) (n : ℤ) :
    K.truncLE n ⟶ K.truncLE (n + 1) := by
  have h : (K.truncLE n).IsStrictlyLE (n + 1) :=
    CochainComplex.isStrictlyLE_of_le _ n (n + 1) (by omega)
  exact inv ((K.truncLE n).ιTruncLE (n + 1)) ≫
    CochainComplex.truncLEMap (K.ιTruncLE n) (n + 1)

/--
Compatible bounded-above resolutions of all good truncations by a quotient-generating
subcategory.

Source: Stacks Project, Derived Categories, Tag 06XX, derived-lemma-special-direct-system.
(blueprint: lem-sfb-subcategory-truncation-resolution-system)

Proof:
1. By [lem-pur-homotopy-category-triangulated], the homotopy category is triangulated
   and its derived localization is exact. Use TR2 and TR3 of
   [def-weil-triangulated-category] to compare cone triangles.
2. Apply [lem-sfb-subcategory-left-resolution] to the first good truncation, which
   vanishes above degree 1, to obtain its bounded-above termwise epimorphic resolution.
3. Given the stages through `n`, form the cone of `j_n e_n`. Its terms are the
   biproducts of the next truncation and shifted terms of `E_n`, so it is bounded above.
   Resolve this cone by a bounded-above complex `Q` with terms in `P`, using
   [lem-sfb-subcategory-left-resolution].
4. Form the shifted cone of the composite `Q → Cone(j_n e_n) → E_n[1]`. Its terms are
   biproducts of those of `E_n` and `Q`; rotation gives a triangle whose first arrow
   is a degreewise split inclusion with cokernels isomorphic to the terms of `Q`.
5. TR3 gives a morphism of triangles with outer components the identity and the cone
   resolution. Exact localization and [lem-sf-triangle-morphism-iso] imply that its
   middle component is a quasi-isomorphism. Choose a chain representative `f`.
6. Lift the homotopy between `f u` and `j_n e_n` along the degreewise retraction of `u`.
   Subtract its boundary from `f` to obtain strict equality, preserving the chain-map
   condition and cohomology maps. The resulting map is already epic below degree `n`
   and above degree `n + 1`, where the target is zero.
7. Choose a cover `p : P₀ → K.X n` with `P P₀`. The identity disk on `P₀` in degrees
   `n` and `n + 1` maps to the next truncation by `p` and `d p`. Adding this map to `f`
   makes degree `n` epic. In degree `n + 1` its image contains the boundaries, and the
   image of `f` surjects onto cohomology, so the sum is epic there as well.
8. The disk is acyclic, so adding it preserves the quasi-isomorphism. Extend the
   transition by zero into the disk summand; strict compatibility is retained. Terms
   and transition cokernels remain in `P` by finite biproducts and isomorphism closure,
   and the new bound is the maximum of the preceding bound and `n + 1`. Induction
   constructs all stages. Cones, cohomology and quasi-isomorphisms use
   [def-weil-abstract-derived-category]; the ambient structure is [def-sp-abelian].
-/
theorem subcategory_truncation_resolution_system
    {C : Type u} [Category.{v} C] [Abelian C]
    (P : C → Prop)
    (hzero : ∀ X : C, IsZero X → P X)
    (hiso : ∀ {X : C} {Y : C}, CategoryTheory.Iso X Y → P X → P Y)
    (hbiprod : ∀ {X : C} {Y : C}, P X → P Y → P (X ⊞ Y))
    (hcover : ∀ X : C, ∃ (Y : C) (p : Y ⟶ X), P Y ∧ Epi p)
    (K : CochainComplex C ℤ) :
    ∃ (E : ℤ → CochainComplex C ℤ)
      (e : ∀ n : ℤ, E n ⟶ K.truncLE n)
      (u : ∀ n : ℤ, E n ⟶ E (n + 1)),
      (∀ n : ℤ, 1 ≤ n →
        u n ≫ e (n + 1) = e n ≫ subcategoryTruncationMap K n) ∧
        (∀ n : ℤ, 1 ≤ n →
          (∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i)) ∧
          (∀ i : ℤ, P ((E n).X i)) ∧
          (∀ i : ℤ, Epi ((e n).f i)) ∧
          QuasiIso (e n)) ∧
        (∀ n : ℤ, 1 ≤ n →
          (∀ i : ℤ, IsSplitMono ((u n).f i)) ∧
          (∀ i : ℤ, P (cokernel ((u n).f i)))) := by
  sorry

end CategoryTheory

end
