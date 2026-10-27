/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # Exact comparisons on approximations with connective tails

Source: Stacks Project, Tag 0A69, `lemma-internal-hom-evaluate-isomorphism-technical`,
the reduction following the truncation triangle, abstracted to exact functors.
(blueprint: lem-trf-exact-comparison-connective-approximations)
-/

@[expose] public section

set_option autoImplicit false

universe uT vT uA vA w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- An exact comparison is invertible on an object if it is invertible on approximations
whose two image tails have a uniform cohomological lower bound tending to infinity.
The conclusion also gives the comparison formula in each degree.

Source: Stacks Project, Tag 0A69, `lemma-internal-hom-evaluate-isomorphism-technical`,
the sentence after the truncation triangle.
(blueprint: lem-trf-exact-comparison-connective-approximations)

Proof:
1. Fix d and n with d + c ≤ n. Exactness of F and G sends the given triangle to
   distinguished triangles. For J = F and J = G, the long exact cohomology sequence
   (`lem-sf-derived-homology-long-exact`) has the segment
   H^(d-1)(J(E n)) → H^d(J(P n)) → H^d(J(K)) → H^d(J(E n)).
   Both outside terms vanish, since d-1 ≤ d ≤ n-c. Thus H^d(J(i n)) is mono and epi,
   hence invertible in the abelian category. Explicitly, a mono is a kernel of some b;
   its epimorphism property and b composed with it being zero force b = 0, so its kernel
   universal property identifies it with the identity kernel of the zero map.
2. Naturality gives F(i n) ≫ e_K = e_(P n) ≫ G(i n). Apply H^d and precompose with
   the inverse of H^d(F(i n)) to obtain the displayed formula. Its three factors are
   invertible: the middle one is the image of the given isomorphism e_(P n).
3. For each d choose n = d+c. Then H^d(e_K) is invertible. The unbounded derived
   cohomology criterion (`lem-weil-pbc-unbounded-derived-iso-cohomology`, represented
   by `DerivedCategory.isIso_iff`) implies that e_K is invertible. Each degree uses
   its own approximation; no transition maps, boundedness or infinite (co)limits enter. -/
theorem isIso_comparison_of_connective_approximations
    {T : Type uT} [Category.{vT} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    (F G : T ⥤ DerivedCategory A) [F.CommShift ℤ] [G.CommShift ℤ]
    [F.IsTriangulated] [G.IsTriangulated] (e : F ⟶ G) [NatTrans.CommShift e ℤ]
    (K : T) (P E : ℤ → T) (i : ∀ n : ℤ, P n ⟶ K)
    (p : ∀ n : ℤ, K ⟶ E n) (q : ∀ n : ℤ, E n ⟶ (P n)⟦(1 : ℤ)⟧)
    (hTriangle : ∀ n : ℤ, Triangle.mk (i n) (p n) (q n) ∈ distTriang T)
    (hApprox : ∀ n : ℤ, IsIso (e.app (P n))) (c : ℤ)
    (hTail : ∀ n r : ℤ, r ≤ n - c →
      IsZero ((DerivedCategory.homologyFunctor A r).obj (F.obj (E n))) ∧
        IsZero ((DerivedCategory.homologyFunctor A r).obj (G.obj (E n)))) :
    IsIso (e.app K) ∧
      ∀ d n : ℤ, d + c ≤ n →
        ∃ (hF : IsIso ((DerivedCategory.homologyFunctor A d).map (F.map (i n))))
          (_hG : IsIso ((DerivedCategory.homologyFunctor A d).map (G.map (i n)))),
          (DerivedCategory.homologyFunctor A d).map (e.app K) =
            @inv A _ _ _ ((DerivedCategory.homologyFunctor A d).map (F.map (i n))) hF ≫
              (DerivedCategory.homologyFunctor A d).map (e.app (P n)) ≫
              (DerivedCategory.homologyFunctor A d).map (G.map (i n)) := by
  sorry

end CategoryTheory
