/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Algebra.Homology.ConeHorizontalStepStable
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # The graded complexes of the horizontal cone filtration

Source: Stacks Project, Homology, Tag 012X, first filtration and its graded complexes.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- The nonnegative graded complexes of the explicit horizontal cone filtration
are shifts of column cones.
Source: Stacks Project, Homology, Tag 012X, first filtration and graded complexes;
the sign correction is the columnwise-cone refinement in the parent node, step 3.
(blueprint: lem-sp-cone-horizontal-graded-iso)

Proof: evaluation preserves cokernels. The quotient of the sum with horizontal
indices at least p by the sum with indices at least p+1 retains exactly the
source and target summands of horizontal index p. Their diagonal inclusions
induce isomorphisms onto this quotient, because the diagonal coproduct is a
finite direct sum. The horizontal differential goes into the next step and
therefore disappears. Put k=n-p and e=(-1)^p. On these summands the differential
has source block -e*d_A, target block e*d_B and off-diagonal block f. The
column cone shifted by -p has source block -e*d_A, target block e*d_B and
off-diagonal block e*f. Multiply the source summand by e and leave the target
summand fixed. The diagonal blocks commute with these scalars, and the
source scalar times e*f equals f since e squared is one. These maps therefore
commute with the differentials. The same scalars give their inverses. Include
the source term at k=-1: it is essential at n=p-1.
For k<-1 both summands are zero, and the same construction uses their unique
maps. Thus the comparison is valid in every integer degree. -/
theorem coneHorizontal_graded_iso
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B)
    (F : DecreasingFiltration (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)))
    (hF : ∀ p n : ℤ, F.complexStep p n = coneHorizontalStep f p n)
    (p : ℤ) (hp : 0 ≤ p) :
    Nonempty (F.gradedPiece p ≅
      (CochainComplex.mappingCone
        (HomologicalComplex.extendMap (f.f p.toNat) ComplexShape.embeddingUpNat))⟦-p⟧) := by
  sorry

end HomologicalComplex₂
