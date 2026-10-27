/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q63
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.Pi
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Order.Directed

/-!
# Uniform factorization from stabilization of Hom-product images

Source: Stacks Project, Algebra, Tag 059E, proof of (5) implies (3)
(blueprint: lem-trf-hom-product-stabilization-factorization).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Module

/-- If precomposition images into the product of all stages of a directed module
diagram stabilize, each stage has a later transition factoring through every
transition with that source. The product is the dependent function module
`∀ s : I, F.obj s`, with its componentwise operations. The functor laws supply
the identity and composition laws of the directed system. No finite-presentation
or countability hypothesis is required.

Source: Stacks Project, Algebra, Tag 059E, proof of (5) implies (3).
(blueprint: lem-trf-hom-product-stabilization-factorization)

Proof:
1. Fix i and choose j >= i from the image-stabilization hypothesis. Insert M_j
   into the j-th coordinate of the product, with zero in every other coordinate,
   obtaining a linear map e_j. The j-th projection pi_j is linear and
   pi_j composed with e_j is the identity, by evaluating each coordinate.
2. For each l >= j, the map e_j composed with f_ij belongs to the precomposition
   image from Hom(M_j, P). Equality of images supplies a_l : M_l to P with
   a_l composed with f_il equal to e_j composed with f_ij. Thus g_l = pi_j
   composed with a_l satisfies g_l composed with f_il equal to f_ij.
3. For any k >= i, directedness gives l >= j, k. Take h = g_l composed with f_kl.
   The system composition identity gives h composed with f_ik equal to f_ij.
   This includes k incomparable with j and uses neither finite presentation
   nor countability. -/
theorem exists_factorization_of_hom_product_images_stabilize
    (R : Type u) [CommRing R]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ ModuleCat.{w} R)
    (hstable : ∀ i : I, ∃ (j : I) (hij : i ≤ j), ∀ (k : I) (hjk : j ≤ k),
      Set.range (fun a : F.obj j →ₗ[R] (∀ s : I, F.obj s) ↦
        a.comp (F.map (homOfLE hij)).hom) =
      Set.range (fun a : F.obj k →ₗ[R] (∀ s : I, F.obj s) ↦
        a.comp (F.map (homOfLE (hij.trans hjk))).hom)) :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j), ∀ (k : I) (hik : i ≤ k),
      ∃ h : F.obj k →ₗ[R] F.obj j,
        (F.map (homOfLE hij)).hom = h.comp (F.map (homOfLE hik)).hom := by
  sorry

end Module
