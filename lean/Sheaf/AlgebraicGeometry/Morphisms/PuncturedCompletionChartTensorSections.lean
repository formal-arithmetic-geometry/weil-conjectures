module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionChartSectionModules
import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartTensorSectionsAux

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The affine pullback tensor formula transported through the given overlap isomorphism.
Source: Stacks Project, Tags 01JO (affine fibre products), 0BLH and 05EL, item (1).
(blueprint: new-sbc-punctured-completion-chart-tensor-sections)

Proof: let V = (q ≫ U.ι)⁻¹D(f). The hypothesis makes V affine; D(f) is
contained in U. Its pullback along Spec C → Spec A therefore lies in the
overlap on which D.overlapIso is defined. Restrict D.overlapIso to this
pullback. The equality D.over shows that the resulting isomorphism over
Spec C identifies it with s⁻¹D(φ(f)). The affine fibre-product formula gives
its section ring as Γ(V) tensor_A C; commute the factors to obtain
C tensor_A Γ(V). The A-action on Γ(V) is the one of chartSectionModule,
by chartSectionModule_smul. Taking sections of the restricted overlap
isomorphism and composing with the tensor formula gives a C-linear
equivalence with the section module on s⁻¹D(φ(f)). All the structural
maps are over Spec C, so the equivalence respects C-scalars. This argument
also covers the empty affine chart, whose section ring and tensor product
are zero. This statement involves no localization of Γ(E, ⊤). -/
theorem exists_chart_tensor_sections
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
    Nonempty (FormalGlueing.extend φ
      (FormalGlueing.piece f (chartSectionModule (q ≫ U.ι) f)) ≃ₗ[C] N) := by
  obtain ⟨e, he⟩ := exists_chart_tensor_sections_bijective D f hf hV
  exact ⟨LinearEquiv.ofBijective e he⟩

end AlgebraicGeometry.Scheme.CompletionGluingData
