module

public import Sheaf.Algebra.Homology.ConeHorizontalProjection
public import Sheaf.Algebra.Homology.ConeHorizontalStepStable
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.Algebra.Homology.ConeHorizontalQuotientIsoExists

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- The explicit signed column projection induces a unique isomorphism of quotient objects.
Source: Stacks Project, Homology, Tag 012X, first-filtration graded objects,
with the source/target cone decomposition of the parent node's first step.
(blueprint: lem-sp-cone-horizontal-quotient-iso)

Proof: evaluation preserves cokernels. In degree n, the p-th tail is the finite
biproduct of source and target diagonal summands of horizontal index at least p.
The next tail consists of those of index strictly greater than p. Projection
onto column p kills the latter; its restriction therefore descends through the
evaluated cokernel. The diagonal inclusions at index p, composed with the
quotient projection, are an inverse to this descent. On the source summand
both directions are multiplied by (-1)^p; their composite is the identity
because this scalar squares to one. On the target summand both directions
are identities. The other summands vanish in the quotient. At n=p-1 only
the source summand survives; at n<p-1 both surviving objects are zero.
The same calculation proves invertibility there. Finally the quotient
projection is epi, so its composite specifies the descended map uniquely.
This is solely an objectwise quotient assertion, with no differential claim. -/
theorem coneHorizontal_quotient_iso
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B)
    (F : DecreasingFiltration (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)))
    (hF : ∀ p n : ℤ, F.complexStep p n = coneHorizontalStep f p n)
    (p : ℕ) (n : ℤ) :
    ∃! a : (F.gradedPiece (p : ℤ)).X n ⟶
      ((CochainComplex.mappingCone
        (HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat))⟦-(p : ℤ)⟧).X n,
      IsIso a ∧
        (F.complexQuotientπ (p : ℤ) ((p : ℤ) + 1) (by omega)).f n ≫ a =
          (F.step (p : ℤ)).arrow.f n ≫ coneHorizontalProjection f p n := by
  classical
  obtain ⟨a, ha, hcomp⟩ := coneHorizontal_quotient_iso_exists f F hF p n
  refine ⟨a, ⟨ha, hcomp⟩, ?_⟩
  intro b hb
  let π := F.complexQuotientπ (p : ℤ) ((p : ℤ) + 1) (by omega)
  have hπ : Epi (π.f n) := by
    dsimp only [π, DecreasingFiltration.complexQuotientπ]
    infer_instance
  apply (cancel_epi (π.f n)).1
  rw [hcomp, hb.2]

end HomologicalComplex₂
