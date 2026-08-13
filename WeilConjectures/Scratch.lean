module
public import WeilConjectures.Compactification.FiniteTypeExtension
public import WeilConjectures.Blowup.Exceptional

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

variable {X : Scheme.{u}}

noncomputable def Scheme.IdealSheafData.blowupChart'
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    Spec (.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) a ha))) ⟶ I.blowup :=
  AffineBlowup.chart (I.ideal V) (reesX (I.ideal V) a ha)
    (reesX_mem (I.ideal V) a ha) ≫ I.blowupι V

noncomputable def Scheme.IdealSheafData.blowupChartSection'
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    Γ(X, V.1) ⟶ Γ(Spec (.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) a ha))), ⊤) :=
  CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (I.ideal V)
    (reesX (I.ideal V) a ha)) ≫ (Scheme.ΓSpecIso _).inv

lemma Scheme.IdealSheafData.blowupChart_comp_blowupMap'
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    I.blowupChart' V ha ≫ I.blowupMap =
      Spec.map (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (I.ideal V)
        (reesX (I.ideal V) a ha))) ≫ V.2.fromSpec :=
  chart_blowupι_comp_blowupMap I V a ha

set_option maxHeartbeats 6400000 in
lemma Scheme.IdealSheafData.ideal_comap_comap_blowupChart'
    (I K : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    ((K.comap I.blowupMap).comap (I.blowupChart' V ha)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (K.ideal V).map (I.blowupChartSection' V ha).hom := by
  have h1 : (K.comap I.blowupMap).comap (I.blowupChart' V ha) =
      K.comap (Spec.map (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (I.ideal V)
        (reesX (I.ideal V) a ha))) ≫ V.2.fromSpec) := by
    rw [← Scheme.IdealSheafData.comap_comp, I.blowupChart_comp_blowupMap' V ha]
  have hpre : (⊤ : (Spec (.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) a ha)))).Opens) ≤
      (Spec.map (CommRingCat.ofHom (AffineBlowup.awayAlgebraMap (I.ideal V)
        (reesX (I.ideal V) a ha))) ≫ V.2.fromSpec) ⁻¹ᵁ V.1 := by
    rw [Scheme.Hom.comp_preimage, V.2.fromSpec_preimage_self]
    exact le_rfl
  rw [h1, K.ideal_comap_specMap_fromSpec V (CommRingCat.ofHom
      (AffineBlowup.awayAlgebraMap (I.ideal V) (reesX (I.ideal V) a ha))) hpre,
    appLE_specMap_comp_fromSpec V (CommRingCat.ofHom
      (AffineBlowup.awayAlgebraMap (I.ideal V) (reesX (I.ideal V) a ha))) hpre]
  rfl

set_option maxHeartbeats 6400000 in
lemma Scheme.IdealSheafData.ideal_comap_comap_blowupChart_self'
    (I : X.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    ((I.comap I.blowupMap).comap (I.blowupChart' V ha)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {(I.blowupChartSection' V ha).hom a} := by
  rw [I.ideal_comap_comap_blowupChart' I V ha]
  sorry

end AlgebraicGeometry
