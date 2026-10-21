/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.CategoryTheory.TruncationDescends
import WeilConjectures.CategoryTheory.TruncationTriangle

/-!
# Bounded dévissage for a bifunctor exact in each variable

Source: Stacks Project, `derived.tex`, Tag 08J5, applied successively in each variable
(blueprint: lem-sfb-bounded-bifunctor-devissage).
-/

@[expose] public section

universe uA vA wA uB vB wB uT vT

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- An exact bifunctor takes bounded pairs into a strictly full triangulated subcategory
when it takes pairs of degree-zero objects from the specified cohomology classes there.
Only nonzero cohomology objects must belong to those classes.

Source: Stacks Project, `derived.tex`, Tag 08J5, successive-cohomology triangles, applied
successively in both variables; Tags 014V and 05QM for exact functors and subcategories
(blueprint: lem-sfb-bounded-bifunctor-devissage).

Proof:
1. Exact functors are additive and take zero objects to zero objects
   (def-weil-triangulated-category). The subcategory contains zero and is closed under
   isomorphisms, integer shifts, and extensions (def-weil-triangulated-subcategory).
2. Canonical truncations have the same cohomology through the truncation degree and zero
   above it (lem-weil-pbc-truncation-descends). For cohomology supported in [a,b], the
   truncation through a-1 is zero and that through b is isomorphic to the original object:
   the corresponding quasi-isomorphisms become isomorphisms in the localization
   (def-weil-abstract-derived-category). Acyclic objects are zero by the same argument.
3. For every q the successive truncations fit into the distinguished triangle with third
   vertex H^q[-q] (lem-weil-pbc-truncation-triangle). Exactness carries this to a
   distinguished triangle with the other variable fixed.
4. Fix F in A₀ and a cohomological interval [c,d] for M. Induct over the finite sequence
   of truncations through c-1,c,...,d. The initial image is zero. At each step its third
   vertex is zero if H^q(M) is zero; otherwise the degree-zero hypothesis and shift
   closure place it in S. Extension closure gives the middle vertex. The endpoint gives
   the assertion for (F[0],M).
5. Fix this M and repeat the finite induction on truncations of K through a-1,a,...,b.
   Each third vertex is zero or a shift of a pair covered by step 4. Extension closure
   and the endpoint isomorphism give S(B(K,M)). Arbitrary integer intervals, gaps,
   acyclic inputs, and empty A₀ or B₀ are included without requiring zero in either class. -/
theorem bounded_bifunctor_devissage
    (A : Type uA) [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (B : Type uB) [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (T : Type uT) [Category.{vT} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
    (S : ObjectProperty T) [S.IsTriangulated] [S.IsClosedUnderIsomorphisms]
    (F : DerivedCategory A ⥤ DerivedCategory B ⥤ T)
    [∀ K : DerivedCategory A, (F.obj K).CommShift ℤ]
    [∀ K : DerivedCategory A, (F.obj K).IsTriangulated]
    [∀ M : DerivedCategory B, (F.flip.obj M).CommShift ℤ]
    [∀ M : DerivedCategory B, (F.flip.obj M).IsTriangulated]
    (A₀ : ObjectProperty A) (B₀ : ObjectProperty B)
    (h₀ : ∀ (X : A) (Y : B), A₀ X → B₀ Y →
      S ((F.obj ((singleFunctor A 0).obj X)).obj ((singleFunctor B 0).obj Y)))
    (K : DerivedCategory A) (M : DerivedCategory B)
    (hK : (TStructure.t (C := A)).bounded K)
    (hM : (TStructure.t (C := B)).bounded M)
    (hKA : ∀ q : ℤ, ¬ IsZero ((homologyFunctor A q).obj K) →
      A₀ ((homologyFunctor A q).obj K))
    (hMB : ∀ q : ℤ, ¬ IsZero ((homologyFunctor B q).obj M) →
      B₀ ((homologyFunctor B q).obj M)) :
    S ((F.obj K).obj M) := by
  sorry

end DerivedCategory
