module

public import Sheaf.Algebra.Homology.ConeHorizontalProjection
import Sheaf.Algebra.Homology.ConeHorizontalProjectionGenerator
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

/- The two generator calculations are the only lengthy sign computation in this
   item.  They are isolated here so that the filtration argument below is
   completely explicit. -/
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
  let q := HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
    ComplexShape.embeddingUpNat
  let M := CochainComplex.mappingCone q
  let T := (CochainComplex.mappingCone
    (HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat))⟦-(p : ℤ)⟧
  let g : M.X n ⟶ T.X (n + 1) :=
    coneHorizontalProjection f p n ≫ T.d n (n + 1) -
      M.d n (n + 1) ≫ coneHorizontalProjection f p (n + 1)
  obtain ⟨hs, ht⟩ := coneHorizontal_projection_generator_vanishing f p n
  have hle : coneHorizontalStep f (p : ℤ) n ≤ kernelSubobject g := by
    apply Finset.sup_le
    intro h hh
    have hp : p ≤ h := by exact_mod_cast (Finset.mem_filter.mp hh).2
    apply sup_le
    · exact le_kernelSubobject g _ (imageSubobject_arrow_comp_eq_zero (hs h hp))
    · exact le_kernelSubobject g _ (imageSubobject_arrow_comp_eq_zero (ht h hp))
  have hz : (F.step (p : ℤ)).arrow.f n ≫ g = 0 := by
    have hf : (kernelSubobject g).Factors ((F.step (p : ℤ)).arrow.f n) := by
      apply Subobject.factors_of_le _ (show F.complexStep (p : ℤ) n ≤
        kernelSubobject g by rw [hF]; exact hle)
      simpa only [DecreasingFiltration.complexStep, Category.id_comp] using
        imageSubobject_factors_comp_self ((F.step (p : ℤ)).arrow.f n)
          (𝟙 ((F.step (p : ℤ) : CochainComplex C ℤ).X n))
    rw [← Subobject.factorThru_arrow _ _ hf, Category.assoc,
      kernelSubobject_arrow_comp, comp_zero]
  have he :
      ((F.step (p : ℤ)).arrow.f n ≫ coneHorizontalProjection f p n) ≫
        T.d n (n + 1) =
      (F.step (p : ℤ)).arrow.f n ≫ M.d n (n + 1) ≫
        coneHorizontalProjection f p (n + 1) := by
    apply sub_eq_zero.mp
    simpa only [g, Preadditive.comp_sub, Category.assoc] using hz
  exact he.trans
    ((F.step (p : ℤ)).arrow.comm_assoc n (n + 1) _)

end HomologicalComplex₂
