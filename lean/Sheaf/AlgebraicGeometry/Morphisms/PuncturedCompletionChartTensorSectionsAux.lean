module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartSectionModules

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- Affine chart tensor comparison via a bijective structural-linear map.
Source: Stacks Project, Tags 01JO, 0BLH and 05EL.
(blueprint: new-sbc-punctured-completion-chart-tensor-sections-aux)

This is the affine fibre-product calculation transported through the overlap
isomorphism.  The bijectivity assertion is the underlying construction; the
public theorem upgrades this map to a linear equivalence.
-/
theorem exists_chart_tensor_sections_bijective
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} [IsAffine E] {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (f : A)
    (hf : PrimeSpectrum.basicOpen f ≤ U)
    (hV : IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen f)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let W := s ⁻¹ᵁ PrimeSpectrum.basicOpen (φ f)
    letI : Module C Γ(E, W) := Module.compHom _
      ((ΓSpecIso (.of C)).inv ≫ s.appTop ≫
        E.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
    let N := ModuleCat.of C Γ(E, W)
    ∃ e : FormalGlueing.extend φ
      (FormalGlueing.piece f (chartSectionModule (q ≫ U.ι) f)) →ₗ[C] N,
      Function.Bijective e := by
  sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
