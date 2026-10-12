/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.HypercohomologyLeftEdge
public import Mathlib.Algebra.Homology.SingleHomology

/-! # Normalization of the hypercohomology left edge

Source: Stacks Project, derived.tex, Tag 015J.
-/

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]

/-- The left edge on a complex supported in a single degree is the identity, under the
canonical identifications of its cohomology with its sole term.
Source: Stacks Project, derived.tex, Tag 015J, second spectral sequence for a single complex.
(blueprint: lem-pc-hypercohomology-left-edge-single)

Proof: extend the single complex by zero. Its image in the derived category is the object
A placed in degree n. Its truncations in degrees below n are zero and those containing n
are the object itself, so both arrows defining the left edge are identities under the
canonical truncation isomorphisms. Express this object as A[0] shifted by minus n
and use shift compatibility to reduce the remaining composite to degree zero. The derived unit
on A[0], followed by the degree-zero right-derived
comparison and rightDerivedZeroIsoSelf, is the original functor applied to A, by the
normalization of the right derived unit. The extension, quotient, single-complex homology,
and shift comparisons are natural canonical isomorphisms and cancel in inverse pairs.
The degree-n cycle representative is the inverse of the single-complex term comparison;
its homology quotient is the inverse of the single-complex homology comparison. This
proves the identity displayed below, including n=0 and the zero object. -/
theorem cochainHypercohomologyLeftEdge_single (A : B) (n : ℕ) :
    (let S := (HomologicalComplex.single B (ComplexShape.up ℕ) n).obj A
     let T := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj S
     let c := T.liftCycles
       (G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) n A).inv)
       (n + 1) (by simp) (by
         change _ ≫ G.map (S.d n (n + 1)) = 0
         simp [S])
     c ≫ T.homologyπ n ≫ G.cochainHypercohomologyLeftEdge S n ≫
       G.map (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) n A).hom =
       𝟙 (G.obj A)) := by
  sorry

end CategoryTheory.Functor
