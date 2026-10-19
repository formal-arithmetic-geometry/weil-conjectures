module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedCompletionChartSectionModules
import Sheaf.AlgebraicGeometry.Morphisms.CompletedAffineSectionLocalization
import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartTensorSections

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
  classical
  dsimp only
  let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let φ := algebraMap A C
  let W := fun i ↦ s ⁻¹ᵁ PrimeSpectrum.basicOpen (φ (f i))
  let moduleN := fun i ↦ Module.compHom Γ(E, W i)
    ((ΓSpecIso (.of C)).inv ≫ s.appTop ≫
      E.presheaf.map (homOfLE (le_top : W i ≤ ⊤)).op).hom
  let N := fun i ↦ @ModuleCat.of C _ Γ(E, W i) _ (moduleN i)
  have hloc (i : Fin t) := exists_completed_affine_section_localization φ s (f i)
  have htensor (i : Fin t) := exists_chart_tensor_sections D (f i) (hf i) (hV i)
  choose e he using hloc
  let d (i : Fin t) := Classical.choice (htensor i)
  let dA (i : Fin t) : FormalGlueing.restrict φ
      (FormalGlueing.extend φ (FormalGlueing.piece (f i)
        (chartSectionModule (q ≫ U.ι) (f i)))) ≃ₗ[A] FormalGlueing.restrict φ (N i) :=
    { (d i).toEquiv with
      map_add' := (d i).map_add
      map_smul' := fun a x ↦ (d i).map_smul (φ a) x }
  refine ⟨fun i ↦ (e i).trans (dA i).symm, ?_⟩
  intro i z x
  change (d i).symm (e i
    ((FormalGlueing.localizedSModule φ (f i) (completedSectionModule s)).smul z x)) = _
  rw [he i]
  exact (d i).symm.map_smul z (e i x)

end AlgebraicGeometry.Scheme.CompletionGluingData
