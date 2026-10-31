/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.FinitePresentation

/-! # The universal surjective-flat locus in the base is open

Source: Stacks Project, Tag 05XC, `spaces-more-morphisms-lemma-where-surjective-flat`,
specialized to schemes. (blueprint: lem-sfb-universal-surjective-flat-open)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The base changes making a morphism between the specified families surjective and flat
are represented by an open subscheme of the base.

Source: Stacks Project, Tag 05XC, `spaces-more-morphisms-lemma-where-surjective-flat`.
(blueprint: lem-sfb-universal-surjective-flat-open)

Proof:
1. Apply lem-sfb-relative-flat-locus-base-change (Tag 05VK) to obtain the open flat locus
   U in A, whose formation commutes with every base change.
2. Define F = B minus p(A minus U). It is open because p is closed. If h lands in F,
   every point of A ×_B T projects into U, so the base-changed map is flat.
3. Conversely, if that map is flat, every pair a in A and t in T over the same point
   of B lifts to A ×_B T by lem-weil-pbc-base-change-image, applied to a singleton.
   Hence every a over h(t) belongs to U and h lands in F. The universal property of
   an open subscheme gives factorization through F.
4. Restrict to F. The map f_F is flat and locally of finite presentation: on affine
   charts apply lem-weil-pbc-finite-presentation-over-finite-type-algebra, namely
   Algebra.FinitePresentation.of_restrict_scalars_finitePresentation, since p is
   locally of finite presentation and q is locally of finite type. Thus f_F is open
   by lem-weil-pbc-flat-lfp-open, namely UniversallyOpen.of_flat. Put I = image(f_F).
5. The restriction q_F is closed: the image of D intersect q⁻¹(F) is q(D) intersect F
   for each closed D in C. Therefore V = F minus q_F(C_F minus I) is open in B.
6. If h factors through V, it factors through F, so f_T is flat. The square with
   f_T and f_F is cartesian: the pair of projections to A_F and T gives its inverse
   universal construction, and open immersions are monomorphisms. Every c_T maps
   into I, so lem-weil-pbc-base-change-image applied to a singleton lifts c_T to
   A ×_B T. Thus f_T is surjective.
7. If f_T is surjective and flat, Step 3 factors h through F. The square with
   C ×_B T, C_F, T and F is cartesian by factorization through the open C_F. For any
   c in C_F over h(t), lem-weil-pbc-base-change-image lifts (c,t) to C ×_B T.
   Surjectivity lifts this point to A ×_B T, so c lies in I. Thus h lands in V,
   and the open-subscheme factorization gives the required lift to V.
These arguments include arbitrary nonreduced and empty test schemes. -/
theorem exists_universalSurjectiveFlatOpen {B A C : Scheme.{u}}
    (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C) (hf : f ≫ q = p)
    [Flat p] [LocallyOfFinitePresentation p] (hp : IsClosedMap p)
    [LocallyOfFiniteType q] (hq : IsClosedMap q) :
    ∃ V : B.Opens, ∀ (T : Scheme.{u}) (h : T ⟶ B),
      (Surjective (pullback.map p h q h f (𝟙 T) (𝟙 B)
        (by simpa only [Category.comp_id] using hf.symm) (by simp)) ∧
       Flat (pullback.map p h q h f (𝟙 T) (𝟙 B)
        (by simpa only [Category.comp_id] using hf.symm) (by simp))) ↔
      ∃ l : T ⟶ V.toScheme, l ≫ V.ι = h := by
  sorry

end AlgebraicGeometry
