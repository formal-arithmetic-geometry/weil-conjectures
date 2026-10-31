/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RingTheory.IsMittagLeffler
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
import WeilConjectures.RingTheory.FinitePresentationTensorProducts
import WeilConjectures.SecTraceFormula.TensorKernelFactorization

/-!
# Mittag-Leffler Hom systems from the tensor-product condition

Source: Stacks Project, Algebra, Tag 059M, implication (2) to (1), and Tag 059E,
condition (4) (blueprint: lem-trf-mittag-leffler-hom-systems).
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace Module

/-- For a directed system of finitely presented modules with Mittag-Leffler colimit,
the images of precomposition into any module eventually stabilize.

Source: Stacks Project, Algebra, Tags 059M and 059E (4).
(blueprint: lem-trf-mittag-leffler-hom-systems)

Proof:
1. Fix a stage i. Represent finitely presented modules by cokernels of finite matrices
   over R. Form the set of pairs (Q, z), where Q is such a representative and z is in
   the kernel of the map M_i tensor Q to M tensor Q. Take the product T of these Q.
   Finite presentations give a set of representatives, not a proper-class product
   (def-sc-finitely-presented-module).
2. Tensoring the finitely presented M_i with products is bijective
   (lem-trf-finite-presentation-tensor-products). Thus the family of all z lifts to
   an element of M_i tensor T. Its image in M tensor T has zero coordinates, hence
   is zero by the tensor-product Mittag-Leffler hypothesis
   (def-trf-mittag-leffler-module). The comparison square commutes on pure tensors
   (def-weil-pbc-module-tensor-product).
3. Tensor commutes with this colimit (lem-weil-pbc-tensor-commutes-with-colimits).
   The element becomes zero at some j >= i
   (lem-weil-pbc-filtered-colimit-modules-elementwise). Projecting to each factor
   shows, uniformly for every finitely presented Q, that the kernel of M_i tensor Q
   to M tensor Q is contained in the kernel of M_i tensor Q to M_j tensor Q.
   An isomorphism from any finite presentation to a representative transfers this
   inclusion, by functoriality of tensor products and their inverse maps.
4. For k >= j the kernel of M_i tensor Q to M_k tensor Q is therefore contained
   in the kernel of M_i tensor Q to M_j tensor Q. The cokernel of M_i to M_k is
   finitely presented: add lifts of the finitely many images of generators of M_i
   to the finite matrix presenting M_k (def-sc-finitely-presented-module).
5. Apply lem-trf-tensor-kernel-factorization to M_i to M_k and M_i to M_j.
   Obtain h_k : M_k to M_j whose composite with the former map is the latter.
6. For any target N, composing a : M_j to N with this factorization puts its
   restriction to M_i in the image from M_k. Conversely the system identity
   factors M_i to M_k through M_j, giving the reverse image inclusion. Thus the
   images are equal for every k >= j, as required, for every i and every N. -/
theorem hom_images_stabilize_of_isMittagLeffler
    (R : Type u) [CommRing R]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ ModuleCat.{max u v w} R)
    [∀ i : I, Module.FinitePresentation R (F.obj i)]
    (c : Cocone F) (hc : IsColimit c)
    (hM : Module.IsMittagLeffler.{u, max u v w, max u v w, 0} R c.pt)
    (N : Type t) [AddCommGroup N] [Module R N] :
    ∀ i : I, ∃ (j : I) (hij : i ≤ j), ∀ (k : I) (hjk : j ≤ k),
      Set.range (fun a : F.obj k →ₗ[R] N ↦
        a.comp (F.map (homOfLE (hij.trans hjk))).hom) =
      Set.range (fun a : F.obj j →ₗ[R] N ↦ a.comp (F.map (homOfLE hij)).hom) := by
  sorry

end Module
