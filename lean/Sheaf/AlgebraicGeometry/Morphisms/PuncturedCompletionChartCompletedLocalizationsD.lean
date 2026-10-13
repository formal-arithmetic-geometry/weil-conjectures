module

public import Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartSectionModules

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData
/-- Additive chart section identifications and generator formulas.
Source: Stacks Project, Tags 0BLH and 05EL.
(blueprint: lem-sbc-punctured-completion-chart-completed-localizations-d)

Proof: on each affine inverse image V_i, use the affine pullback tensor-product
formula to construct the additive equivalence d_i from C tensor_A M_i to sections
of the pullback. Its pure-tensor value is the pullback along the first projection,
and its C-scalar value is multiplication by the section induced by the second
projection. The principal-open localization formula and the overlap isomorphism
show that this d_i sends alpha_i of a completed section m/1 to the restriction of
D.toCompleted.appTop m. The same formulas prove all three displayed identities by
checking pure tensors and then using additivity and the localization universal
property. Thus d is constructed from the canonical affine maps, with no arbitrary
witness; empty charts give the zero equivalence. -/
theorem exists_chart_completed_localizations_d
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} [IsAffine E] {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)))
    (alpha : ∀ i, FormalGlueing.localize (f i)
      (FormalGlueing.restrict (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
        (completedSectionModule s)) ≃ₗ[A]
      FormalGlueing.restrict (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
        (FormalGlueing.extend (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
          (FormalGlueing.piece (f i) (chartSectionModule (q ≫ U.ι) (f i))))) :
    ∃ d : ∀ i, FormalGlueing.extend (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
      (FormalGlueing.piece (f i) (chartSectionModule (q ≫ U.ι) (f i))) ≃+
        Γ(pullback q (completionSpecMap A ∣_ U),
          (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
            ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))),
      (∀ i m, d i (alpha i (LocalizedModule.mk m 1)) =
        (pullback q (completionSpecMap A ∣_ U)).presheaf.map (homOfLE le_top).op
          (D.toCompleted.appTop m)) ∧
      (∀ i m, d i (TensorProduct.tmul A (1 : AdicCompletion (IsLocalRing.maximalIdeal A) A) m) =
        (pullback.fst q (completionSpecMap A ∣_ U)).app _ m) ∧
      (∀ i (z : AdicCompletion (IsLocalRing.maximalIdeal A) A) m, d i (z • m) =
        ((ΓSpecIso (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))).inv ≫
          (pullback.snd q (completionSpecMap A ∣_ U) ≫
            (completionSpecMap A ⁻¹ᵁ U).ι).appTop ≫
          (pullback q (completionSpecMap A ∣_ U)).presheaf.map
            (homOfLE (le_top : (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
              ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ≤ ⊤)).op).hom z * d i m) := by
  sorry
end AlgebraicGeometry.Scheme.CompletionGluingData
