/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions

/-!
# Finite-filtration devissage through a triangulated derived functor

Source: Stacks Project, Tags 0GKY, 06UQ, and 0152 (blueprint:
lem-weil-pbc-etale-lisse-filtration-devissage).
-/

@[expose] public section

universe v u v' u'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Finite-filtration dévissage for cohomology under a triangulated functor.

Source: Stacks Project, Tag 0GKY, label `lemma-loc-constant-shriek-rel-dim-1`,
proof final paragraph, using Tags 06UQ and 0152.
(blueprint: lem-weil-pbc-etale-lisse-filtration-devissage).

The proof proceeds by applying the weak-Serre cohomology triangulated-subcategory
lemma, taking the zero step as the base case, obtaining distinguished triangles
from the short exact sequences of successive filtration steps, and inducting on
`i` using closure under the middle vertex.  The argument permits `r = 0`, equal
successive subobjects, and zero quotients.
-/
theorem cohomology_mem_of_filtration
    {A : Type u} {B : Type u'} [Category.{v, u} A] [Category.{v', u'} B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (Φ : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Additive]
    (S : ObjectProperty B) [S.ContainsZero] [S.IsClosedUnderIsomorphisms]
    [S.IsClosedUnderKernels] [S.IsClosedUnderCokernels] [S.IsClosedUnderExtensions]
    (X : A) (r : ℕ) (F : Fin (r + 1) → Subobject X)
    (h₀ : F 0 = ⊥) (hᵣ : F (Fin.last r) = ⊤)
    (hF : ∀ i : Fin r, F i.castSucc ≤ F i.succ)
    (hQ : ∀ (i : Fin r) (q : ℤ),
      S ((DerivedCategory.Plus.homologyFunctor B q).obj
        (Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj
          (cokernel (Subobject.ofLE (F i.castSucc) (F i.succ) (hF i))))))) :
    ∀ q : ℤ, S ((DerivedCategory.Plus.homologyFunctor B q).obj
      (Φ.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))) := by
  sorry

end CategoryTheory
