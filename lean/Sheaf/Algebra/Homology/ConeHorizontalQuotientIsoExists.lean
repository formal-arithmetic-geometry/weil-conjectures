module

public import Sheaf.Algebra.Homology.ConeHorizontalProjection
public import Sheaf.Algebra.Homology.ConeHorizontalStepStable
public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
import Sheaf.Algebra.Homology.ConeHorizontalProjectionEpi
import Sheaf.Algebra.Homology.ConeHorizontalProjectionKernel

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
  let i := Subobject.ofLE (F.step ((p : ℤ) + 1)) (F.step (p : ℤ))
    (F.antitone_step (by omega))
  let g := (F.step (p : ℤ)).arrow.f n ≫ coneHorizontalProjection f p n
  have hk : imageSubobject (i.f n) = kernelSubobject g :=
    coneHorizontal_projection_kernel f F hF p n
  have hf : (kernelSubobject g).Factors (i.f n) := by
    rw [← hk]
    simpa only [Category.id_comp] using
      imageSubobject_factors_comp_self (i.f n) (𝟙 _)
  have hz : i.f n ≫ g = 0 := by
    rw [← Subobject.factorThru_arrow _ _ hf, Category.assoc,
      kernelSubobject_arrow_comp, comp_zero]
  let S := ShortComplex.mk (i.f n) g hz
  have he : S.Exact := (S.exact_iff_image_eq_kernel).2 hk
  have : Epi S.g := coneHorizontal_projection_epi f F hF p n
  let ev := HomologicalComplex.eval C (ComplexShape.up ℤ) n
  let hc := CokernelCofork.mapIsColimit _ (cokernelIsCokernel i) ev
  let e := IsColimit.coconePointUniqueUpToIso hc he.gIsCokernel
  refine ⟨e.hom, inferInstance, ?_⟩
  exact IsColimit.comp_coconePointUniqueUpToIso_hom hc he.gIsCokernel
    WalkingParallelPair.one

end HomologicalComplex₂
