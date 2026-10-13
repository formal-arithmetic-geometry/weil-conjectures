module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartSectionModules

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData
/-- Localization equivalences and scalar compatibility for completed chart sections.
Source: Stacks Project, Tags 0BLH and 05EL.
(blueprint: lem-sbc-punctured-completion-chart-completed-localizations-alpha)

Proof: identify the completed section module on the principal open D(f_i) with the
localization of its global sections, using the affine principal-open localization
formula. Identify the pullback chart with the scalar extension of the affine chart
module by the affine pullback tensor-product formula. The overlap isomorphism D and
the equality of the two structural maps identify these two descriptions. Composing
the resulting localization and tensor-product linear equivalences gives alpha i.
Both equivalences are induced by the same C-linear pullback map, so the universal
property of localization gives the displayed compatibility with the localized
C-action. This construction also covers empty principal opens, where both modules
are zero; no arbitrary witness is chosen. -/
theorem exists_chart_completed_localizations_alpha
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} [IsAffine E] {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let M' := completedSectionModule s
    let M := fun i ↦ chartSectionModule (q ≫ U.ι) (f i)
    ∃ alpha : ∀ i, FormalGlueing.localize (f i) (FormalGlueing.restrict φ M') ≃ₗ[A]
      FormalGlueing.restrict φ (FormalGlueing.extend φ (FormalGlueing.piece (f i) (M i))),
      ∀ i (z : C) (x : FormalGlueing.localize (f i) (FormalGlueing.restrict φ M')),
        alpha i ((FormalGlueing.localizedSModule φ (f i) M').smul z x) =
          z • (alpha i x : FormalGlueing.extend φ (FormalGlueing.piece (f i) (M i))) := by
  sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
