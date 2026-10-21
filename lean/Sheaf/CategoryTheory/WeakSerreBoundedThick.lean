/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import Sheaf.Paper.CohomologyInWeakSerreSubcategory

/-!
# Bounded cohomology in a weak Serre class is thick

Source: Stacks Project, Tag 06UQ, `lemma-cohomology-in-serre-subcategory`, including
bounded versions; Homology, Tag 0754, `lemma-characterize-weak-serre-subcategory`
(blueprint: lem-sfb-weak-serre-bounded-thick).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Bounded derived objects with cohomology in a weak Serre class form a thick subcategory.
For each ambient retract, its cohomology inclusion is the kernel inclusion of one minus
its cohomological idempotent, and every interval bound passes to the retract unchanged.

Source: Stacks Project, Tag 06UQ, `lemma-cohomology-in-serre-subcategory` (bounded and
saturated versions), and Tag 0754, `lemma-characterize-weak-serre-subcategory`.
(blueprint: lem-sfb-weak-serre-bounded-thick)

Proof:
1. By def-weil-pbc-bounded-derived-subcategories, boundedness is finite cohomological
   support, equivalently vanishing outside an integer interval. The empty support is
   bounded by [0, 0]. Thus the object property is homologyProperty P intersected with
   the bounded property of the standard t-structure.
2. Apply lem-sbc-cohomology-in-weak-serre-subcategory and its bounded-intersection
   clause. This gives zero, every integer shift and triangle closure. Both factors are
   closed under isomorphisms. Rotation gives all three two-out-of-three cases, with
   inherited triangles as in def-weil-triangulated-subcategory.
3. Given i : L → K and r : K → L with i ≫ r = 1, fix n and put I = H^n(i), R = H^n(r).
   Functoriality (def-weil-abstract-derived-category) gives I ≫ R = 1. Set q = 1 - R ≫ I.
   Bilinearity (def-weil-preadditive-category) gives I ≫ q = 0. If u ≫ q = 0, then
   u = u ≫ R ≫ I, so u factors through I by u ≫ R. This factorization is unique since
   v ≫ I = u implies v = v ≫ I ≫ R = u ≫ R. This is the kernel universal property
   in the abelian category def-sp-abelian and gives the displayed isomorphism.
4. If K belongs to the property, H^n(K) belongs to P. Kernel closure applied to the
   endomorphism q, followed by isomorphism closure, puts H^n(L) in P. If H^n(K) is zero,
   the equality I ≫ R = 1 forces the identity of H^n(L) to be zero; thus H^n(L) is zero.
   In particular, every interval bound for K also bounds L, giving boundedness of L.
5. These give triangulated and ambient retract closure, hence thickness as in
   pur9-def-thick. Step 3 gives the kernel identification and step 4 the same bounds.
-/
lemma weakSerre_bounded_homology_thick
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions] :
    (DerivedCategory.homologyProperty P ⊓ DerivedCategory.TStructure.t.bounded).IsTriangulated ∧
    (DerivedCategory.homologyProperty P ⊓
      DerivedCategory.TStructure.t.bounded).IsStableUnderRetracts ∧
    (∀ (L K : DerivedCategory A) (i : L ⟶ K) (r : K ⟶ L), i ≫ r = 𝟙 L →
      (DerivedCategory.homologyProperty P ⊓ DerivedCategory.TStructure.t.bounded) K →
      (∀ n : ℤ, ∃ e : (DerivedCategory.homologyFunctor A n).obj L ≅
          kernel (𝟙 ((DerivedCategory.homologyFunctor A n).obj K) -
            (DerivedCategory.homologyFunctor A n).map r ≫
              (DerivedCategory.homologyFunctor A n).map i),
        e.hom ≫ kernel.ι (𝟙 ((DerivedCategory.homologyFunctor A n).obj K) -
          (DerivedCategory.homologyFunctor A n).map r ≫
            (DerivedCategory.homologyFunctor A n).map i) =
          (DerivedCategory.homologyFunctor A n).map i) ∧
      (∀ a b : ℤ,
        (∀ n : ℤ, n < a ∨ b < n → IsZero ((DerivedCategory.homologyFunctor A n).obj K)) →
        ∀ n : ℤ, n < a ∨ b < n → IsZero ((DerivedCategory.homologyFunctor A n).obj L))) := by
  sorry

end CategoryTheory
