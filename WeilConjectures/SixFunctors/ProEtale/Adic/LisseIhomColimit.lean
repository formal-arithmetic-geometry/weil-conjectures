/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorLeftFree
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom

/-!
# The internal hom out of a lisse sheaf commutes with colimits

For a lisse sheaf `F` of `ℚ̄_ℓ,X`-modules, `𝓗om(F, -)` commutes with colimits
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.preservesColimitsOfShape_ihom`): this can be
checked after pullback along the members of a pro-étale cover trivialising `F`
(`AlgebraicGeometry.ProEtale.preservesColimitsOfShape_of_cover`), where
`𝓗om(ℚ̄_ℓⁿ, -) ≅ - ⊗ ℚ̄_ℓⁿ` is a left adjoint.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

attribute [local instance] Abelian.hasFiniteBiproducts

/-- A functor to sheaves of `ℚ̄_ℓ,X`-modules preserves colimits of shape `J` if its composites with
the pullbacks along the members of a pro-étale cover do: a morphism of sheaves is an isomorphism
if its pullbacks along the members of the cover are. -/
lemma preservesColimitsOfShape_of_cover {D : Type*} [Category D] {J : Type (u + 1)}
    [SmallCategory J] [HasColimitsOfShape J D] (F : D ⥤ AdicSheaf l X) {ι : Type*}
    {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    (h : ∀ i, PreservesColimitsOfShape J (F ⋙ (g i)^*ᵃ[l])) : PreservesColimitsOfShape J F := by
  constructor
  intro K
  let φ := colimit.desc (K ⋙ F) (F.mapCocone (colimit.cocone K))
  have (i : ι) := (adicUpperStarLowerStarAdjunction l (g i)).leftAdjoint_preservesColimits
  have hφ (i : ι) : IsIso ((g i)^*ᵃ[l].map φ) := by
    have hc := isColimitOfPreserves (F ⋙ (g i)^*ᵃ[l]) (colimit.isColimit K)
    let ψ := colimit.desc (K ⋙ F ⋙ (g i)^*ᵃ[l]) ((F ⋙ (g i)^*ᵃ[l]).mapCocone (colimit.cocone K))
    have : IsIso ψ :=
      inferInstanceAs (IsIso ((colimit.isColimit _).coconePointUniqueUpToIso hc).hom)
    have h' : (g i)^*ᵃ[l].map φ = (preservesColimitIso (g i)^*ᵃ[l] (K ⋙ F)).hom ≫ ψ := by
      rw [← Iso.inv_comp_eq]
      apply colimit.hom_ext
      intro j
      rw [ι_preservesColimitIso_inv_assoc, ← Functor.map_comp]
      simp only [φ, ψ, colimit.ι_desc, Functor.mapCocone_ι_app, colimit.cocone_ι]
      erw [colimit.ι_desc]
      rfl
    rw [h']
    infer_instance
  have hk : IsZero (kernel φ) := AdicSheaf.isZero_of_isZero_upperStar g hg fun i ↦
    have := hφ i
    (isZero_kernel_of_mono ((g i)^*ᵃ[l].map φ)).of_iso (PreservesKernel.iso (g i)^*ᵃ[l] φ)
  have hc : IsZero (cokernel φ) := AdicSheaf.isZero_of_isZero_upperStar g hg fun i ↦
    have := hφ i
    (isZero_cokernel_of_epi ((g i)^*ᵃ[l].map φ)).of_iso (PreservesCokernel.iso (g i)^*ᵃ[l] φ)
  have := Preadditive.mono_of_isZero_kernel φ hk
  have := Preadditive.epi_of_isZero_cokernel φ hc
  have : IsIso φ := isIso_of_mono_of_epi φ
  exact preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
    (IsColimit.ofPointIso (colimit.isColimit (K ⋙ F)) (i := this))

/-- **The internal hom out of a lisse sheaf commutes with colimits**: after pullback along a
member `g` of a pro-étale cover trivialising `F`, it becomes `𝓗om(ℚ̄_ℓⁿ, -) ≅ - ⊗ ℚ̄_ℓⁿ`, a left
adjoint. -/
theorem IsAdicLisseSheaf.preservesColimitsOfShape_ihom {F : AdicSheaf l X}
    (hF : IsAdicLisseSheaf F) (J : Type (u + 1)) [SmallCategory J] :
    PreservesColimitsOfShape J (AdicSheaf.ihom F) := by
  obtain ⟨R, hR, hRF⟩ := hF
  obtain ⟨ι, V, g, rfl⟩ := R.exists_eq_ofArrows
  have (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hR (.mk i)
  refine preservesColimitsOfShape_of_cover _ g hR fun i ↦ ?_
  obtain ⟨n, ⟨e⟩⟩ := hRF (g i) (.mk i)
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (Mod.tensorLeft (⨁ fun _ : Fin n ↦ AdicSheaf.unit l (V i))) :=
    (Mod.ihomAdjunction _).leftAdjoint_preservesColimits
  have := (adicUpperStarLowerStarAdjunction l (g i)).leftAdjoint_preservesColimits
  exact preservesColimitsOfShape_of_natIso
    ((adicUpperStarIhomIso l (g i) F ≪≫
      Functor.isoWhiskerLeft _ ((Mod.ihomMapIso e).symm ≪≫ Mod.ihomIsoTensorLeftFree n)).symm)

end AlgebraicGeometry.ProEtale
