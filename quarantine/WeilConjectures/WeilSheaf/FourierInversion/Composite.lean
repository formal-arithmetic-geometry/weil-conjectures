/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier
public import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierInversion.UpperStar
public import WeilConjectures.WeilSheaf.FourierInversion.Vanishing
public import WeilConjectures.WeilSheaf.FourierTraceAux

/-!
# Fourier inversion: the composite of two Fourier transforms

`FT_{ψ⁻¹} ∘ FT_ψ` computed on the triple product `𝔸³` (blueprint `lem-fd-kernel-composition`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The Fourier kernel `μ^* ℒ_ψ` is the Artin–Schreier sheaf `ℒ_ψ(x y)` of the function `x y`. -/
theorem nonempty_iso_fourierKernel_artinSchreierOf (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (fourierKernel ψ ≅ artinSchreierOf ψ
      ((affinePlane.fst k₀).appTop (AffineSpace.coord _ PUnit.unit) *
        (affinePlane.snd k₀).appTop (AffineSpace.coord _ PUnit.unit))) := by
  rw [fourierKernel, artinSchreierOf_eq]
  exact ⟨(WeilSheaf.upperStarCongr affinePlane.mul_eq_homOfSection).app _⟩

/-- **`FT_{ψ⁻¹} ∘ FT_ψ` on the triple product** (blueprint `lem-fd-kernel-composition`,
`sk-lem-kernel-composition`, without forming the convolution kernel). On `𝔸³` with points
`(x, ξ, y)`,

`FT_{ψ⁻¹} FT_ψ (K) ≅ Rr₃₀!(ℒ_ψ((x - y) ξ) ⊗ r₁^* K)[1][1]`

naturally in `K`, with `r₁ = r₁₃ ≫ pr₁` and `r₃ = r₁₃ ≫ pr₂`. It follows from compact-support
base change along `pr₁ : (ξ, y) ↦ ξ`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerShriek_upperStar`), the projection
formula for `r₂₃` and the composition `R(r₂₃ ≫ pr₂)₀! ≅ Rpr₂₀! Rr₂₃₀!`, together with
`ℒ_ψ(x ξ) ⊗ ℒ_{ψ⁻¹}(ξ y) ≅ ℒ_ψ((x - y) ξ)` (blueprint `lem-fd-as-lisse`). -/
theorem nonempty_iso_fourierTransform_comp_fourierTransform_inv
    (ψ : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (fourierTransform (l := l) ψ ⋙ fourierTransform ψ⁻¹ ≅
      WeilComplex.upperStar (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.fst k₀) ⋙
        WeilComplex.tensorLisse (artinSchreierOf ψ
          ((affineTripleProduct.proj₁₃ k₀).appTop
              ((AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))).appTop
                (AffineSpace.coord _ PUnit.unit)) *
            (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop
              (AffineSpace.coord _ PUnit.unit))) (isLisse_artinSchreierOf ψ _) ⋙
        WeilComplex.derivedLowerShriek k₀ l (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.snd k₀) ⋙
        shiftFunctor _ (1 : ℤ) ⋙ shiftFunctor _ (1 : ℤ)) := by
  have : QuasiCompact (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) := by
    have : QuasiCompact (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
    exact inferInstanceAs (QuasiCompact (affinePlane.fst k₀ ≫ _))
  have : QuasiSeparated (affinePlane k₀ ↘ Spec (CommRingCat.of k₀)) := by
    have : QuasiSeparated (affinePlane.fst k₀) := MorphismProperty.pullback_fst _ _ inferInstance
    exact inferInstanceAs (QuasiSeparated (affinePlane.fst k₀ ≫ _))
  have h₁₂₃ : affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.fst k₀ =
      affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀ :=
    pullback.condition.symm
  have : (affineTripleProduct.proj₁₂ k₀).IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : (affineTripleProduct.proj₂₃ k₀).IsOver (Spec (CommRingCat.of k₀)) :=
    ⟨by
      rw [← comp_over (affinePlane.fst k₀) (Spec (CommRingCat.of k₀)), reassoc_of% h₁₂₃,
        comp_over (affinePlane.snd k₀)]
      rfl⟩
  have : IsSeparated (affineTripleProduct.proj₂₃ k₀) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFiniteType (affineTripleProduct.proj₂₃ k₀) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiCompact (affineTripleProduct.proj₂₃ k₀) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  -- the functions `x ξ` on `𝔸²` and `(x - y) ξ` on `𝔸³`
  let X₁ := AffineSpace.coord (Spec (CommRingCat.of k₀)) PUnit.unit
  let m : Γ(affinePlane k₀, ⊤) :=
    (affinePlane.fst k₀).appTop X₁ * (affinePlane.snd k₀).appTop X₁
  have hring : -(affineTripleProduct.proj₂₃ k₀).appTop m +
      (affineTripleProduct.proj₁₂ k₀).appTop m =
      (affineTripleProduct.proj₁₃ k₀).appTop
          ((AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))).appTop X₁) *
        (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop X₁ := by
    have e₁ : (affineTripleProduct.proj₁₃ k₀).appTop
        ((AffineSpace.sub PUnit.{u + 1} (Spec (CommRingCat.of k₀))).appTop X₁) =
        (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.fst k₀).appTop X₁ -
          (affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.snd k₀).appTop X₁ := by
      rw [AffineSpace.sub_appTop_coord, map_sub]
      exact congrArg₂ (· - ·)
        (congrArg (fun f ↦ Scheme.Hom.appTop f X₁) (pullback.tripleProj₁₃_fst _ _ _))
        (congrArg (fun f ↦ Scheme.Hom.appTop f X₁) (pullback.tripleProj₁₃_snd _ _ _))
    have e₂ : (affineTripleProduct.proj₂₃ k₀).appTop m =
        (affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.fst k₀).appTop X₁ *
          (affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.snd k₀).appTop X₁ :=
      map_mul _ _ _
    have e₃ : (affineTripleProduct.proj₁₂ k₀).appTop m =
        (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.fst k₀).appTop X₁ *
          (affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.snd k₀).appTop X₁ :=
      map_mul _ _ _
    rw [e₁, e₂, e₃, h₁₂₃]
    ring
  -- the kernels as Artin–Schreier sheaves, and their pullbacks to `𝔸³`
  obtain ⟨eF⟩ := nonempty_iso_fourierKernel_artinSchreierOf (l := l) ψ
  obtain ⟨eF'⟩ := nonempty_iso_fourierKernel_artinSchreierOf (l := l) ψ⁻¹
  obtain ⟨eK⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso eF (isLisse_fourierKernel ψ)
    (isLisse_artinSchreierOf ψ m)
  obtain ⟨eK'⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso eF' (isLisse_fourierKernel ψ⁻¹)
    (isLisse_artinSchreierOf ψ⁻¹ m)
  obtain ⟨eG₁⟩ := nonempty_iso_upperStar_artinSchreierOf (affineTripleProduct.proj₁₂ k₀) ψ m
  obtain ⟨eG₂⟩ := nonempty_iso_upperStar_artinSchreierOf (affineTripleProduct.proj₂₃ k₀) ψ⁻¹ m
  obtain ⟨eInv⟩ := nonempty_iso_artinSchreierOf_inv ψ ((affineTripleProduct.proj₂₃ k₀).appTop m)
  obtain ⟨eMul⟩ := nonempty_iso_tensorObj_artinSchreierOf ψ
    (-(affineTripleProduct.proj₂₃ k₀).appTop m) ((affineTripleProduct.proj₁₂ k₀).appTop m)
  obtain ⟨eT₁⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso eG₁
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreierOf ψ m))
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨eT₂⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso (eG₂ ≪≫ eInv)
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreierOf ψ⁻¹ m))
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨eT₁₂⟩ := WeilComplex.nonempty_iso_tensorLisse_comp
    (artinSchreierOf ψ (-(affineTripleProduct.proj₂₃ k₀).appTop m))
    (artinSchreierOf ψ ((affineTripleProduct.proj₁₂ k₀).appTop m))
    (isLisse_artinSchreierOf ψ _) (isLisse_artinSchreierOf ψ _)
  obtain ⟨eT⟩ := WeilComplex.nonempty_iso_tensorLisse_of_iso
    (eMul ≪≫ eqToIso (congrArg (artinSchreierOf ψ) hring))
    (ProEtale.IsAdicLisseSheaf.ihom (isLisse_artinSchreierOf ψ _).dual
      (isLisse_artinSchreierOf ψ _))
    (isLisse_artinSchreierOf ψ _)
  -- the functorial isomorphisms
  obtain ⟨eBC⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    (affinePlane.snd k₀) (affinePlane.fst k₀) (affineTripleProduct.proj₂₃ k₀)
    (affineTripleProduct.proj₁₂ k₀) (IsPullback.of_hasPullback _ _)
  obtain ⟨eTA⟩ := WeilComplex.nonempty_iso_tensorLisse_comp_upperStar (k₀ := k₀)
    (affineTripleProduct.proj₁₂ k₀) (artinSchreierOf (l := l) ψ m) (isLisse_artinSchreierOf ψ m)
  obtain ⟨eP⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse (k₀ := k₀)
    (affineTripleProduct.proj₂₃ k₀) (artinSchreierOf (l := l) ψ⁻¹ m)
    (isLisse_artinSchreierOf ψ⁻¹ m)
  obtain ⟨eA₁⟩ := WeilComplex.nonempty_iso_upperStar_comp (k₀ := k₀) (l := l)
    (affineTripleProduct.proj₁₂ k₀) (affinePlane.fst k₀)
  obtain ⟨eA₂⟩ := WeilComplex.nonempty_upperStar_iso_of_eq (k₀ := k₀) (l := l)
    (f := affineTripleProduct.proj₁₂ k₀ ≫ affinePlane.fst k₀)
    (g := affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.fst k₀)
    (pullback.tripleProj₁₃_fst _ _ _).symm
  obtain ⟨eC₁⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_comp (k₀ := k₀) (l := l)
    (affineTripleProduct.proj₂₃ k₀) (affinePlane.snd k₀)
  obtain ⟨eC₂⟩ := WeilComplex.nonempty_iso_derivedLowerShriek_of_eq (k₀ := k₀) (l := l)
    (f := affineTripleProduct.proj₂₃ k₀ ≫ affinePlane.snd k₀)
    (g := affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.snd k₀)
    (pullback.tripleProj₁₃_snd _ _ _).symm
  -- the functors involved
  let A := WeilComplex.upperStar (k₀ := k₀) (l := l) (affinePlane.fst k₀)
  let A₁₂ := WeilComplex.upperStar (k₀ := k₀) (l := l) (affineTripleProduct.proj₁₂ k₀)
  let A₁₃ := WeilComplex.upperStar (k₀ := k₀) (l := l)
    (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.fst k₀)
  let T := WeilComplex.tensorLisse (fourierKernel (l := l) ψ) (isLisse_fourierKernel ψ)
  let T' := WeilComplex.tensorLisse (fourierKernel (l := l) ψ⁻¹) (isLisse_fourierKernel ψ⁻¹)
  let Tm := WeilComplex.tensorLisse (artinSchreierOf (l := l) ψ m) (isLisse_artinSchreierOf ψ m)
  let T'm := WeilComplex.tensorLisse (artinSchreierOf (l := l) ψ⁻¹ m)
    (isLisse_artinSchreierOf ψ⁻¹ m)
  let T₁ := WeilComplex.tensorLisse (artinSchreierOf ψ ((affineTripleProduct.proj₁₂ k₀).appTop m))
    (isLisse_artinSchreierOf ψ _)
  let T₂ := WeilComplex.tensorLisse
    (artinSchreierOf ψ (-(affineTripleProduct.proj₂₃ k₀).appTop m)) (isLisse_artinSchreierOf ψ _)
  let C := WeilComplex.derivedLowerShriek k₀ l (affinePlane.snd k₀)
  let C₂₃ := WeilComplex.derivedLowerShriek k₀ l (affineTripleProduct.proj₂₃ k₀)
  let D := WeilComplex.derivedLowerShriek k₀ l
    (affineTripleProduct.proj₁₃ k₀ ≫ affinePlane.snd k₀)
  let S₁ := shiftFunctor (WeilComplex k₀ l (affineLine k₀)) (1 : ℤ)
  -- the chain of isomorphisms, all composites associated to the right
  have e₀ : fourierTransform (l := l) ψ ⋙ fourierTransform ψ⁻¹ ≅
      A ⋙ T ⋙ C ⋙ S₁ ⋙ A ⋙ T' ⋙ C ⋙ S₁ :=
    Iso.refl _
  have e₁ := Functor.isoWhiskerLeft A (Functor.isoWhiskerRight eK (C ⋙ S₁ ⋙ A ⋙ T' ⋙ C ⋙ S₁))
  have e₂ := Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft Tm (Functor.isoWhiskerLeft C
    (Functor.isoWhiskerLeft S₁ (Functor.isoWhiskerLeft A
      (Functor.isoWhiskerRight eK' (C ⋙ S₁))))))
  have s₁ := Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft Tm (Functor.isoWhiskerLeft C
    ((Functor.associator _ _ (T'm ⋙ C ⋙ S₁)).symm ≪≫
      Functor.isoWhiskerRight (A.commShiftIso (1 : ℤ)) (T'm ⋙ C ⋙ S₁) ≪≫
      Functor.associator _ _ (T'm ⋙ C ⋙ S₁))))
  have s₂ := Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft Tm (Functor.isoWhiskerLeft C
    (Functor.isoWhiskerLeft A
      ((Functor.associator _ _ (C ⋙ S₁)).symm ≪≫
        Functor.isoWhiskerRight (T'm.commShiftIso (1 : ℤ)) (C ⋙ S₁) ≪≫
        Functor.associator _ _ (C ⋙ S₁)))))
  have s₃ := Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft Tm (Functor.isoWhiskerLeft C
    (Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft T'm
      ((Functor.associator _ _ S₁).symm ≪≫
        Functor.isoWhiskerRight (C.commShiftIso (1 : ℤ)) S₁ ≪≫
        Functor.associator _ _ S₁)))))
  have s₄ := Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft Tm
    ((Functor.associator _ _ (T'm ⋙ C ⋙ S₁ ⋙ S₁)).symm ≪≫
      Functor.isoWhiskerRight eBC (T'm ⋙ C ⋙ S₁ ⋙ S₁) ≪≫
      Functor.associator _ _ (T'm ⋙ C ⋙ S₁ ⋙ S₁)))
  have s₅ := Functor.isoWhiskerLeft A
    ((Functor.associator _ _ (C₂₃ ⋙ T'm ⋙ C ⋙ S₁ ⋙ S₁)).symm ≪≫
      Functor.isoWhiskerRight eTA (C₂₃ ⋙ T'm ⋙ C ⋙ S₁ ⋙ S₁) ≪≫
      Functor.associator _ _ (C₂₃ ⋙ T'm ⋙ C ⋙ S₁ ⋙ S₁))
  have s₆ := Functor.isoWhiskerLeft A (Functor.isoWhiskerLeft A₁₂
    (Functor.isoWhiskerRight eT₁ (C₂₃ ⋙ T'm ⋙ C ⋙ S₁ ⋙ S₁)))
  have s₇ := (Functor.associator A A₁₂ (T₁ ⋙ C₂₃ ⋙ T'm ⋙ C ⋙ S₁ ⋙ S₁)).symm ≪≫
    Functor.isoWhiskerRight (eA₁.symm ≪≫ eA₂) (T₁ ⋙ C₂₃ ⋙ T'm ⋙ C ⋙ S₁ ⋙ S₁)
  have s₈ := Functor.isoWhiskerLeft A₁₃ (Functor.isoWhiskerLeft T₁
    ((Functor.associator _ _ (C ⋙ S₁ ⋙ S₁)).symm ≪≫
      Functor.isoWhiskerRight eP (C ⋙ S₁ ⋙ S₁) ≪≫
      Functor.associator _ _ (C ⋙ S₁ ⋙ S₁)))
  have s₉ := Functor.isoWhiskerLeft A₁₃ (Functor.isoWhiskerLeft T₁
    (Functor.isoWhiskerRight eT₂ (C₂₃ ⋙ C ⋙ S₁ ⋙ S₁)))
  have s₁₀ := Functor.isoWhiskerLeft A₁₃ (Functor.isoWhiskerLeft T₁ (Functor.isoWhiskerLeft T₂
    ((Functor.associator C₂₃ C (S₁ ⋙ S₁)).symm ≪≫
      Functor.isoWhiskerRight (eC₁.symm ≪≫ eC₂) (S₁ ⋙ S₁))))
  have s₁₁ := Functor.isoWhiskerLeft A₁₃
    ((Functor.associator T₁ T₂ (D ⋙ S₁ ⋙ S₁)).symm ≪≫
      Functor.isoWhiskerRight (eT₁₂ ≪≫ eT) (D ⋙ S₁ ⋙ S₁))
  exact ⟨e₀ ≪≫ e₁ ≪≫ e₂ ≪≫ s₁ ≪≫ s₂ ≪≫ s₃ ≪≫ s₄ ≪≫ s₅ ≪≫ s₆ ≪≫ s₇ ≪≫ s₈ ≪≫ s₉ ≪≫ s₁₀ ≪≫ s₁₁⟩

end AlgebraicGeometry
