module

public import Sheaf.Algebra.Homology.ConeHorizontalProjection
public import Sheaf.Algebra.Homology.ConeHorizontalStepStable
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- On the p-th tail the explicit signed column projection commutes with differentials.
Source: Stacks Project, Homology, Tag 012X, first-filtration graded differential;
column-cone sign calculation in the parent node's second proof step.
(blueprint: lem-sp-cone-horizontal-projection-differential)

Proof: test the two maps on the diagonal source and target inclusions generating
the tail. The total differential is the sum of the horizontal differential,
which raises the index, and (-1)^h times the vertical differential at index h.
For h>p both projections vanish, as do projections of the resulting terms.
For h=p the horizontal term goes to p+1 and is killed by the projection.
The cone source block is minus the total differential and its off-diagonal
block is f; the target block is the total differential. After projection the
blocks are -e*d_A, e*d_B and f, where e=(-1)^p. The shifted column cone has
blocks -e*d_A, e*d_B and e*f. Multiplying the source projection by e and
leaving the target projection fixed gives equality of the diagonal blocks;
the off-diagonal equality is e squared times f equals f. Extension by zero
handles the boundary n=p-1 (only source survives) and degrees below it.
Equality on all generators implies equality on the finite biproduct tail,
and hence on its representative subobject F.step (p : ℤ) via hF. -/
theorem coneHorizontal_projection_differential
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B)
    (F : DecreasingFiltration (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)))
    (hF : ∀ p n : ℤ, F.complexStep p n = coneHorizontalStep f p n)
    (p : ℕ) (n : ℤ) :
    ((F.step (p : ℤ)).arrow.f n ≫ coneHorizontalProjection f p n) ≫
      ((CochainComplex.mappingCone
        (HomologicalComplex.extendMap (f.f p)
          ComplexShape.embeddingUpNat))⟦-(p : ℤ)⟧).d n (n + 1) =
    (F.step (p : ℤ) : CochainComplex C ℤ).d n (n + 1) ≫
      (F.step (p : ℤ)).arrow.f (n + 1) ≫ coneHorizontalProjection f p (n + 1) := by
  sorry

end HomologicalComplex₂
