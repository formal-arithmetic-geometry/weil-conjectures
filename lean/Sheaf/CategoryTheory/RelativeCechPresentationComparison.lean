/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.CategoryTheory.FibredCechPresentation
import Mathlib.CategoryTheory.Limits.Final
import Sheaf.CategoryTheory.ContinuousCocontinuousToposAdjunctionForCoverings

/-! # Independence of the relative Cech presentation

Source: Stacks Project, Tags 06X3, 06X5, 06X7 and 06X9
(blueprint: lem-sfb-relative-cech-presentation-comparison).

The isomorphisms are between coefficient functors and commute with each coface,
not merely with the alternating sum. Their inverse is specified to be the canonical
restriction of compatible families. Sheafness makes these isomorphisms morphisms
in the full subcategory of abelian sheaves. Index `n` means integer degree `n - 1`;
both complexes have zero terms below degree -1.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

/-- Every iterated 2-product presentation gives the same augmented relative Cech
complex, naturally in its abelian coefficient sheaf, with all cofaces respected.

Source: Stacks 06X3, 06X5(2), 06X7 and 06X9(2), including the augmentation
(blueprint: lem-sfb-relative-cech-presentation-comparison).

Proof:
1. At `x` over `T`, choose cartesian lifts `x_t` for arrows `t : R → T`.
   Compatible families on tuples `(t, u_i, gamma_i : f(u_i) ≅ x_t)` form
   a limit, with componentwise abelian-group operations.
2. The test fibre of the common-target model has objects `(t, u_i, y, alpha_i, beta)`.
   Replace `alpha_i` by `beta alpha_i`. Its inverse uses `y = x_t` and `beta = id`;
   the natural isomorphism has target component `beta`. The coefficient comparison
   is `F(beta)`, with inverse `F(beta⁻¹)`, including for a singleton tuple.
3. Flatten a bracketed product recursively. For a vertex with root comparison
   `theta : r_L ≅ r_R`, take right root and multiply left leaf comparisons by theta.
   For a tuple over `x_t`, reconstruct that vertex by `theta = beta_R⁻¹ beta_L`.
   These constructions are inverse on objects and arrows; cancellation of beta_R
   proves the square for every arrow, including nonidentity base arrows.
4. The cone universal property identifies any representative of a binary 2-product
   with this explicit model, preserving roots, leaves and omission comparisons.
   Iteration gives precisely the equivalence recorded by `P.universal`.
5. An equivalence is initial on the opposite indexing categories: its comma
   categories have terminal objects supplied by a quasi-inverse and counit.
   Apply lem-weil-pbc-initial-functor-limit to restriction of compatible families.
   This proves that `P.comparison` is invertible, with the given coefficient transport.
6. For `x' → x`, cartesian factorization compares the chosen lifts by a unique
   vertical isomorphism. Family compatibility identifies both restrictions, and
   uniqueness proves composition compatibility. Thus the comparison is a presheaf
   isomorphism. The fibred-site continuity lemma and the continuous-cocontinuous
   topos adjunction show that the terms are sheaves; equivalently glue each component
   of a compatible family and apply uniqueness to every compatibility equation.
7. Deleting a leaf commutes with flattening by `P.omission`. If a root leaf changes,
   the root comparison is `gamma_i⁻¹ beta`; contravariance gives
   `F(gamma_i⁻¹ beta) F(gamma_i) = F(beta)`. Hence every coface commutes;
   multiplying by the signs and summing proves the differential equations.
8. In augmented degree -1 use the identity. Both augmentations send a section to
   its restriction at every test object, so they agree. All operations commute with
   every coefficient morphism by its naturality, as do their inverses.
9. Extend by zero below -1, using unique maps between zero objects. No covering,
   fullness or faithfulness hypothesis on `f` has been used. -/
theorem relativeCechPresentationComparison {S : AlgebraicGeometry.Scheme.{u}}
    {U X : BasedCategory.{v, max v w} (Over S)} (f : BasedFunctor U X)
    (hU : IsFibredInGroupoids U) (hX : IsFibredInGroupoids X)
    (P : FibredCechPresentation f) :
    (∀ (F : Sheaf (fibredBigEtaleTopology X) AddCommGrpCat.{max v w}) (n : ℕ),
      Presheaf.IsSheaf (fibredBigEtaleTopology X) ((P.term n).obj F.obj) ∧
      Presheaf.IsSheaf (fibredBigEtaleTopology X)
        (((fibredTupleCechPresentation f).term n).obj F.obj)) ∧
    ∃ phi : ∀ n : ℕ,
      sheafToPresheaf (fibredBigEtaleTopology X) AddCommGrpCat.{max v w} ⋙ P.term n ≅
        sheafToPresheaf (fibredBigEtaleTopology X) AddCommGrpCat.{max v w} ⋙
          (fibredTupleCechPresentation f).term n,
      (phi 0).hom = 𝟙 _ ∧
      (∀ n : ℕ, (phi n).inv = whiskerLeft
        (sheafToPresheaf (fibredBigEtaleTopology X) AddCommGrpCat.{max v w})
        (P.comparison n)) ∧
      (∀ (p : ℕ) (j : Fin (p + 2)),
        whiskerLeft (sheafToPresheaf (fibredBigEtaleTopology X) AddCommGrpCat.{max v w})
          (P.coface p j) ≫ (phi (p + 2)).hom =
        (phi (p + 1)).hom ≫ whiskerLeft
          (sheafToPresheaf (fibredBigEtaleTopology X) AddCommGrpCat.{max v w})
          ((fibredTupleCechPresentation f).coface p j)) ∧
      (∀ n : ℕ,
        whiskerLeft (sheafToPresheaf (fibredBigEtaleTopology X) AddCommGrpCat.{max v w})
          (P.differential n) ≫ (phi (n + 1)).hom =
        (phi n).hom ≫ whiskerLeft
          (sheafToPresheaf (fibredBigEtaleTopology X) AddCommGrpCat.{max v w})
          ((fibredTupleCechPresentation f).differential n)) ∧
      ∃ (hdP : ∀ n : ℕ,
          P.restrictedDifferential n ≫ P.restrictedDifferential (n + 1) = 0)
        (hdA : ∀ n : ℕ,
          (fibredTupleCechPresentation f).restrictedDifferential n ≫
            (fibredTupleCechPresentation f).restrictedDifferential (n + 1) = 0)
        (Phi : P.complex hdP ≅ (fibredTupleCechPresentation f).complex hdA),
        ∀ n : ℕ,
          ((P.nonnegativeComplex hdP).extendXIso
            (ComplexShape.embeddingUpIntGE (-1)) (i := n) rfl).inv ≫
          Phi.hom.f ((ComplexShape.embeddingUpIntGE (-1)).f n) ≫
          (((fibredTupleCechPresentation f).nonnegativeComplex hdA).extendXIso
            (ComplexShape.embeddingUpIntGE (-1)) (i := n) rfl).hom = (phi n).hom := by
  sorry

end CategoryTheory
