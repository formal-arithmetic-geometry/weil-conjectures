/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Projections from fibres of split difference maps

Source: Stacks Project, Tag 08DG (lemma-glue), the split restriction calculation;
Tag 05RS (lemma-cohomology-homological)
(blueprint: lem-sp-derived-split-fibre-projections).

The arbitrary triangle `T` and specified isomorphisms `β` and `γ` include both the
literal biproduct triangles and their presentations by isomorphic vertices.
`Functor.biprodComparison` is the canonical cohomology identification with the biproduct
of the cohomology objects. Monicity together with the image equalities states that
cohomology of the first arrow identifies its source with the indicated graph kernel.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- Projections from the fibre of either signed split difference map, including
specified identifications of the middle and final vertices.

Source: Stacks Project, Tag 08DG (lemma-glue), split restriction calculation, and
Tag 05RS (lemma-cohomology-homological)
(blueprint: lem-sp-derived-split-fibre-projections).

Proof plan:
1. Cohomology is additive: cycles, boundaries, and their quotients commute with
   binary direct sums. Under `Functor.biprodComparison`, the two cohomology arrows have
   components `(H(p), H(q))` and `(H(h), -1)` or `(1, -H(r))`.
2. The second arrow has section `(0, -1)` in the first case and `(1, 0)` in the
   second. Its cohomology is therefore split epic in every integer degree.
   In the long exact sequence (`lem-sf-derived-homology-long-exact`), the connecting
   arrows in degrees n and n-1 vanish because they follow split epimorphisms.
   Exactness then makes the cohomology of the first arrow a kernel of the second.
3. The graph `(1, H(h))` is also a kernel of `(H(h), -1)`: a pair `(a, b)` killed
   by the latter satisfies b = H(h)a and factors uniquely through the graph via a.
4. Comparing these kernels gives an inverse to H(p). Cancelling the monic kernel
   inclusion verifies both inverse identities. Thus H(p) identifies H(G) with
   this graph, which is exactly its image subobject.
5. `lem-weil-pbc-unbounded-derived-iso-cohomology` makes p an isomorphism.
   The triangle identity f followed by d is zero
   (`lem-weil-pbc-hom-into-triangle-exact`) gives q = p followed by h in the
   derived category itself.
6. For `(1, -H(r))`, the graph `(H(r), 1)` is a kernel: a killed pair satisfies
   a = H(r)b and factors uniquely through the graph via b. Kernel comparison
   gives both inverse identities for H(q), and the asserted graph image.
7. Cohomological detection of isomorphisms makes q an isomorphism; the triangle
   identity gives p = q followed by r. Split epicity was established in step 2.
8. Conjugate by the specified vertex isomorphisms. The section becomes
   γ followed by the displayed section followed by β inverse. Cohomology carries
   these isomorphisms to isomorphisms, transporting the kernel and its inclusion
   to the computed graph. An identification α of the first vertex precomposes
   both projections with α and preserves their identities and invertibility.
-/
theorem split_fibre_projections
    (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (T : Triangle (DerivedCategory A)) (hT : T ∈ distTriang (DerivedCategory A))
    (X Y : DerivedCategory A) (β : T.obj₂ ≅ X ⊞ Y) :
    (∀ (h : X ⟶ Y) (γ : T.obj₃ ≅ Y),
      T.mor₂ ≫ γ.hom = β.hom ≫ biprod.desc h (-𝟙 Y) →
        IsIso (T.mor₁ ≫ β.hom ≫ biprod.fst) ∧
        T.mor₁ ≫ β.hom ≫ biprod.snd = (T.mor₁ ≫ β.hom ≫ biprod.fst) ≫ h ∧
        ∀ n : ℤ,
          IsSplitEpi ((homologyFunctor A n).map T.mor₂) ∧
          Mono ((homologyFunctor A n).map T.mor₁) ∧
          imageSubobject
              ((homologyFunctor A n).map (T.mor₁ ≫ β.hom) ≫
                Functor.biprodComparison (homologyFunctor A n) X Y) =
            kernelSubobject
              (biprod.desc ((homologyFunctor A n).map h)
                (-𝟙 ((homologyFunctor A n).obj Y))) ∧
          imageSubobject
              ((homologyFunctor A n).map (T.mor₁ ≫ β.hom) ≫
                Functor.biprodComparison (homologyFunctor A n) X Y) =
            imageSubobject
              (biprod.lift (𝟙 ((homologyFunctor A n).obj X))
                ((homologyFunctor A n).map h))) ∧
    (∀ (r : Y ⟶ X) (γ : T.obj₃ ≅ X),
      T.mor₂ ≫ γ.hom = β.hom ≫ biprod.desc (𝟙 X) (-r) →
        IsIso (T.mor₁ ≫ β.hom ≫ biprod.snd) ∧
        T.mor₁ ≫ β.hom ≫ biprod.fst = (T.mor₁ ≫ β.hom ≫ biprod.snd) ≫ r ∧
        ∀ n : ℤ,
          IsSplitEpi ((homologyFunctor A n).map T.mor₂) ∧
          Mono ((homologyFunctor A n).map T.mor₁) ∧
          imageSubobject
              ((homologyFunctor A n).map (T.mor₁ ≫ β.hom) ≫
                Functor.biprodComparison (homologyFunctor A n) X Y) =
            kernelSubobject
              (biprod.desc (𝟙 ((homologyFunctor A n).obj X))
                (-((homologyFunctor A n).map r))) ∧
          imageSubobject
              ((homologyFunctor A n).map (T.mor₁ ≫ β.hom) ≫
                Functor.biprodComparison (homologyFunctor A n) X Y) =
            imageSubobject
              (biprod.lift ((homologyFunctor A n).map r)
                (𝟙 ((homologyFunctor A n).obj Y)))) := by
  sorry

end DerivedCategory
