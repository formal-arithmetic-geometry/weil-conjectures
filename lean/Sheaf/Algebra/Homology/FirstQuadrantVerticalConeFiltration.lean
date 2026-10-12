/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Sheaf.CategoryTheory.DoubleComplexTotal
import Sheaf.CategoryTheory.Filtration

/-! # Horizontal filtration of the cone of a first-quadrant total map

Source: Stacks Project, Homology, Tag 012X, the first filtration of a total complex,
with the mapping-cone construction applied columnwise.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- The horizontal filtration of a total-map cone has column-map cones as its
nonnegative graded pieces and zero graded pieces in negative filtration degrees.
Source: Stacks Project, Homology, Tag 012X, first filtration and its graded complexes.
(blueprint: lem-sp-first-quadrant-vertical-cone-filtration)

Proof: in degree n, the cone is the sum of the source terms in total degree n+1
and the target terms in total degree n. Its p-th step is the sum of summands with
horizontal index at least p. Vertical differentials preserve that index, horizontal
differentials raise it, and the off-diagonal map preserves it. Thus these summands
are subcomplexes. Their inclusions define an antitone subobject filtration. Step 0
is the whole object. Step n+2 is zero: every source horizontal index is at most n+1,
and every target index is at most n. At n=-1 only the source degree-zero term
can remain; below n=-1 the cone is zero, so the bounds also hold for n+2<=0. The quotient
of step p by step p+1, for p >= 0, keeps exactly horizontal index p. Its source
summands are in vertical degree n+1-p, including vertical cone degree -1. Its
remaining differential is the vertical cone differential with the totalization
sign. Put k=n-p and e=(-1)^p. In this graded differential the source and target
vertical differentials are -e*d_A and e*d_B, and the off-diagonal map is f.
Multiply the source summand in degree n by e^(k+1), and the target summand by e^k.
These invertible scalars give a chain isomorphism to the column cone with degrees
reindexed by n-p: the scalars in successive degrees differ by e, and the source
scalar in degree n equals the target scalar in degree n+1. Thus the diagonal
blocks become -d_A and d_B and the off-diagonal block becomes f. Its homology in
degree n is the column cone's homology in degree n-p. If p < 0, successive steps are both
the whole complex, so their quotient and its homology are zero. No quasi-isomorphism
hypothesis enters this construction. -/
theorem firstQuadrant_vertical_cone_filtration
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) :
    ∃ F : DecreasingFiltration (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)),
      (∀ n : ℤ, F.complexStep 0 n = ⊤ ∧ F.complexStep (n + 2) n = ⊥) ∧
      (∀ p n : ℤ, p < 0 → IsZero ((F.gradedPiece p).homology n)) ∧
      (∀ p n : ℤ, 0 ≤ p → Nonempty ((F.gradedPiece p).homology n ≅
        (CochainComplex.mappingCone
          (HomologicalComplex.extendMap (f.f p.toNat) ComplexShape.embeddingUpNat)).homology
            (n - p))) := by
  sorry

end HomologicalComplex₂
