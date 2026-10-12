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

/-- The signed projection descends to an isomorphism on the consecutive quotient.
The construction is the objectwise cokernel calculation described in the source
node: identify the p-tail with the finite sum of source and target summands,
observe that the next tail is the sum of all strictly larger indices, and use
that the signed projection kills that next tail. The diagonal p-summand
inclusions provide a two-sided inverse.
(blueprint: lem-sp-cone-horizontal-quotient-iso-exists) -/
theorem coneHorizontal_quotient_iso_exists
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B)
    (F : DecreasingFiltration (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)))
    (hF : ∀ p n : ℤ, F.complexStep p n = coneHorizontalStep f p n)
    (p : ℕ) (n : ℤ) :
    ∃ a : (F.gradedPiece (p : ℤ)).X n ⟶
      ((CochainComplex.mappingCone
        (HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat))⟦-(p : ℤ)⟧).X n,
      IsIso a ∧
        (F.complexQuotientπ (p : ℤ) ((p : ℤ) + 1) (by omega)).f n ≫ a =
          (F.step (p : ℤ)).arrow.f n ≫ coneHorizontalProjection f p n := by
  sorry

end HomologicalComplex₂
