/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.WeilFourierTransform
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Subtraction
public import WeilConjectures.WeilSheaf.FourierInversion.UpperStar
public import WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
public import WeilConjectures.WeilSheaf.LowerShriekOperations
public import WeilConjectures.WeilSheaf.OpenClosedTriangle
public import WeilConjectures.WeilSheaf.UpperStarId

/-!
# Composition of two Fourier transforms on affine space

On the triple product `𝔸ⁿ ×_{k₀} 𝔸ⁿ ×_{k₀} 𝔸ⁿ` with points `(x, ξ, y)` and projections `r₁₂`,
`r₂₃`, `r₁₃`, the composite of the Fourier transforms of Weil complexes for the characters `ψ`
and `ψ'` is

`FT_{ψ'} FT_ψ (K) ≅ R(r₁₃ ≫ pr₂)₀!(ℒ_{ψ'}(⟨ξ, y⟩) ⊗ ℒ_ψ(⟨x, ξ⟩) ⊗ (r₁₃ ≫ pr₁)^* K)[r][r]`

naturally in `K`
(`AlgebraicGeometry.WeilComplex.nonempty_iso_affineFourierTransform_comp_affineFourierTransform`).

## Implementation details

The proof uses compact-support base change along `pr₁ : (ξ, y) ↦ ξ`, the projection formula for
`r₂₃` and the composition laws of pullbacks and compact-support direct images. The bookkeeping
of the natural isomorphisms is done for abstract functors, which keeps elaboration fast.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

open AffineSpace

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (n : Type u) [Finite n]

set_option hygiene false in
/-- The base `Spec k₀`. -/
local notation "S₀" => Spec (CommRingCat.of k₀)

set_option hygiene false in
/-- The structure morphism of `𝔸ⁿ` over `Spec k₀`. -/
local notation "πV" => 𝔸(n; S₀) ↘ S₀

set_option hygiene false in
/-- The projection `(x, ξ) ↦ x` of the affine plane. -/
local notation "pr₁" => pullback.fst πV πV

set_option hygiene false in
/-- The projection `(x, ξ) ↦ ξ` of the affine plane. -/
local notation "pr₂" => pullback.snd πV πV

set_option hygiene false in
/-- The triple product `𝔸ⁿ ×_{k₀} 𝔸ⁿ ×_{k₀} 𝔸ⁿ`. -/
local notation "T₃" => pullback pr₂ pr₁

set_option hygiene false in
/-- The projection `r₁₂ : (x, ξ, y) ↦ (x, ξ)`. -/
local notation "r₁₂" => pullback.fst pr₂ pr₁

set_option hygiene false in
/-- The projection `r₂₃ : (x, ξ, y) ↦ (ξ, y)`. -/
local notation "r₂₃" => pullback.snd pr₂ pr₁

set_option hygiene false in
/-- The projection `r₁₃ : (x, ξ, y) ↦ (x, y)`. -/
local notation "r₁₃" => pullback.tripleProj₁₃ πV πV πV

instance isOver_fst_affineSpace : (pr₁).IsOver S₀ := ⟨pullback.condition⟩

instance isOver_snd_affineSpace : (pr₂).IsOver S₀ := ⟨rfl⟩

instance : LocallyOfFiniteType (pullback πV πV ↘ S₀) :=
  inferInstanceAs (LocallyOfFiniteType (pr₂ ≫ πV))

instance : QuasiCompact (pullback πV πV ↘ S₀) := inferInstanceAs (QuasiCompact (pr₂ ≫ πV))

instance : IsSeparated (pullback πV πV ↘ S₀) := inferInstanceAs (IsSeparated (pr₂ ≫ πV))

noncomputable instance : (T₃).Over S₀ := ⟨r₁₂ ≫ pullback πV πV ↘ S₀⟩

instance isOver_tripleFst_affineSpace : (r₁₂).IsOver S₀ := ⟨rfl⟩

instance isOver_tripleSnd_affineSpace : (r₂₃).IsOver S₀ :=
  ⟨by
    change r₂₃ ≫ pr₂ ≫ πV = r₁₂ ≫ pr₂ ≫ πV
    rw [pullback.condition_assoc, pullback.condition]⟩

instance isOver_tripleProj₁₃_affineSpace : (r₁₃).IsOver S₀ :=
  ⟨by
    change r₁₃ ≫ pr₂ ≫ πV = r₁₂ ≫ pr₂ ≫ πV
    rw [← pullback.condition, pullback.tripleProj₁₃_fst_assoc, pullback.condition]⟩

instance : LocallyOfFiniteType (T₃ ↘ S₀) :=
  inferInstanceAs (LocallyOfFiniteType (r₁₂ ≫ pullback πV πV ↘ S₀))

instance : IsSeparated (r₁₃) :=
  MorphismProperty.of_isPullback (isPullback_tripleProj₁₃ n S₀).flip inferInstance

instance : LocallyOfFiniteType (r₁₃) :=
  MorphismProperty.of_isPullback (isPullback_tripleProj₁₃ n S₀).flip inferInstance

instance : QuasiCompact (r₁₃) :=
  MorphismProperty.of_isPullback (isPullback_tripleProj₁₃ n S₀).flip inferInstance

/-- The Fourier transform of affine space as a composite of the operations on Weil complexes. -/
theorem affineFourierTransform_eq [Fintype n] (ψ : AddChar k₀ (PadicAlgCl l)) :
    affineFourierTransform k₀ l n ψ = upperStar pr₁ ⋙
      tensorLisse (artinSchreierOf ψ (stdPairing n S₀)) (isLisse_artinSchreierOf ψ _) ⋙
      derivedLowerShriek k₀ l pr₂ ⋙ shiftFunctor _ (Fintype.card n : ℤ) :=
  rfl

omit [Finite n] in
/-- The bookkeeping of the composition of two kernel transforms, for abstract functors. -/
private theorem nonempty_iso_comp_of_kernel {CV CP CT : Type*} [Category CV] [Category CP]
    [Category CT] {U₁ : CV ⥤ CP} {T T' : CP ⥤ CP} {D₂ : CP ⥤ CV} {S : CV ⥤ CV}
    {SP : CP ⥤ CP} {U₁₂ U₁₃ : CP ⥤ CT} {D₂₃ D₁₃ : CT ⥤ CP} {TA TB : CT ⥤ CT}
    (sU : S ⋙ U₁ ≅ U₁ ⋙ SP) (sT : SP ⋙ T' ≅ T' ⋙ SP) (sD : SP ⋙ D₂ ≅ D₂ ⋙ S)
    (bc : D₂ ⋙ U₁ ≅ U₁₂ ⋙ D₂₃) (tA : T ⋙ U₁₂ ≅ U₁₂ ⋙ TA) (pf : D₂₃ ⋙ T' ≅ TB ⋙ D₂₃)
    (u : U₁ ⋙ U₁₂ ≅ U₁ ⋙ U₁₃) (d : D₂₃ ⋙ D₂ ≅ D₁₃ ⋙ D₂) :
    Nonempty ((U₁ ⋙ T ⋙ D₂ ⋙ S) ⋙ (U₁ ⋙ T' ⋙ D₂ ⋙ S) ≅
      U₁ ⋙ U₁₃ ⋙ TA ⋙ TB ⋙ D₁₃ ⋙ D₂ ⋙ S ⋙ S) := by
  have c₁ : (U₁ ⋙ T ⋙ D₂ ⋙ S) ⋙ (U₁ ⋙ T' ⋙ D₂ ⋙ S) ≅
      (U₁ ⋙ T ⋙ D₂) ⋙ U₁ ⋙ (SP ⋙ T') ⋙ D₂ ⋙ S :=
    Functor.isoWhiskerLeft (U₁ ⋙ T ⋙ D₂) (Functor.isoWhiskerRight sU (T' ⋙ D₂ ⋙ S))
  have c₂ : (U₁ ⋙ T ⋙ D₂) ⋙ U₁ ⋙ (SP ⋙ T') ⋙ D₂ ⋙ S ≅
      (U₁ ⋙ T ⋙ D₂) ⋙ U₁ ⋙ T' ⋙ (SP ⋙ D₂) ⋙ S :=
    Functor.isoWhiskerLeft ((U₁ ⋙ T ⋙ D₂) ⋙ U₁) (Functor.isoWhiskerRight sT (D₂ ⋙ S))
  have c₃ : (U₁ ⋙ T ⋙ D₂) ⋙ U₁ ⋙ T' ⋙ (SP ⋙ D₂) ⋙ S ≅
      (U₁ ⋙ T) ⋙ (D₂ ⋙ U₁) ⋙ T' ⋙ D₂ ⋙ S ⋙ S :=
    Functor.isoWhiskerLeft ((U₁ ⋙ T ⋙ D₂) ⋙ U₁ ⋙ T') (Functor.isoWhiskerRight sD S)
  have c₄ : (U₁ ⋙ T) ⋙ (D₂ ⋙ U₁) ⋙ T' ⋙ D₂ ⋙ S ⋙ S ≅
      U₁ ⋙ (T ⋙ U₁₂) ⋙ (D₂₃ ⋙ T') ⋙ D₂ ⋙ S ⋙ S :=
    Functor.isoWhiskerLeft (U₁ ⋙ T) (Functor.isoWhiskerRight bc (T' ⋙ D₂ ⋙ S ⋙ S))
  have c₅ : U₁ ⋙ (T ⋙ U₁₂) ⋙ (D₂₃ ⋙ T') ⋙ D₂ ⋙ S ⋙ S ≅
      (U₁ ⋙ U₁₂) ⋙ TA ⋙ TB ⋙ (D₂₃ ⋙ D₂) ⋙ S ⋙ S :=
    Functor.isoWhiskerLeft U₁ (Functor.isoWhiskerRight tA ((D₂₃ ⋙ T') ⋙ D₂ ⋙ S ⋙ S) ≪≫
      Functor.isoWhiskerLeft (U₁₂ ⋙ TA) (Functor.isoWhiskerRight pf (D₂ ⋙ S ⋙ S)))
  have c₆ : (U₁ ⋙ U₁₂) ⋙ TA ⋙ TB ⋙ (D₂₃ ⋙ D₂) ⋙ S ⋙ S ≅
      U₁ ⋙ U₁₃ ⋙ TA ⋙ TB ⋙ D₁₃ ⋙ D₂ ⋙ S ⋙ S :=
    Functor.isoWhiskerRight u (TA ⋙ TB ⋙ (D₂₃ ⋙ D₂) ⋙ S ⋙ S) ≪≫
      Functor.isoWhiskerLeft (U₁ ⋙ U₁₃ ⋙ TA ⋙ TB) (Functor.isoWhiskerRight d (S ⋙ S))
  exact ⟨c₁ ≪≫ c₂ ≪≫ c₃ ≪≫ c₄ ≪≫ c₅ ≪≫ c₆⟩

/-- **Composition of two Fourier transforms on affine space.** On the triple product with
points `(x, ξ, y)`, `FT_{ψ'} FT_ψ (K)` is the compact-support integral along `r₁₃ ≫ pr₂` of
`ℒ_{ψ'}(⟨ξ, y⟩) ⊗ ℒ_ψ(⟨x, ξ⟩) ⊗ (r₁₃ ≫ pr₁)^* K`, shifted twice by the rank, naturally in
`K`. -/
theorem nonempty_iso_affineFourierTransform_comp_affineFourierTransform [Fintype n]
    (ψ ψ' : AddChar k₀ (PadicAlgCl l)) :
    Nonempty (affineFourierTransform k₀ l n ψ ⋙ affineFourierTransform k₀ l n ψ' ≅
      upperStar pr₁ ⋙ upperStar r₁₃ ⋙
        tensorLisse (artinSchreierOf ψ ((r₁₂).appTop (stdPairing n S₀)))
          (isLisse_artinSchreierOf ψ _) ⋙
        tensorLisse (artinSchreierOf ψ' ((r₂₃).appTop (stdPairing n S₀)))
          (isLisse_artinSchreierOf ψ' _) ⋙
        derivedLowerShriek k₀ l r₁₃ ⋙ derivedLowerShriek k₀ l pr₂ ⋙
        shiftFunctor _ (Fintype.card n : ℤ) ⋙ shiftFunctor _ (Fintype.card n : ℤ)) := by
  have : IsSeparated (r₂₃) := MorphismProperty.pullback_snd _ _ inferInstance
  have : LocallyOfFiniteType (r₂₃) := MorphismProperty.pullback_snd _ _ inferInstance
  have : QuasiCompact (r₂₃) := MorphismProperty.pullback_snd _ _ inferInstance
  rw [affineFourierTransform_eq, affineFourierTransform_eq]
  let b := stdPairing n S₀
  obtain ⟨bc⟩ := nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l) pr₂ pr₁ r₂₃ r₁₂
    (IsPullback.of_hasPullback _ _)
  obtain ⟨tA⟩ := nonempty_iso_tensorLisse_comp_upperStar r₁₂ (artinSchreierOf ψ b)
    (isLisse_artinSchreierOf ψ b)
  obtain ⟨aA⟩ := nonempty_iso_upperStar_artinSchreierOf (k₀ := k₀) (l := l) r₁₂ ψ b
  obtain ⟨eA⟩ := nonempty_iso_tensorLisse_of_iso aA
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreierOf ψ b))
    (isLisse_artinSchreierOf ψ _)
  obtain ⟨pf⟩ := nonempty_iso_derivedLowerShriek_tensorLisse (l := l) r₂₃
    (artinSchreierOf ψ' b) (isLisse_artinSchreierOf ψ' b)
  obtain ⟨aB⟩ := nonempty_iso_upperStar_artinSchreierOf (k₀ := k₀) (l := l) r₂₃ ψ' b
  obtain ⟨eB⟩ := nonempty_iso_tensorLisse_of_iso aB
    (ProEtale.IsAdicLisseSheaf.upperStar _ (isLisse_artinSchreierOf ψ' b))
    (isLisse_artinSchreierOf ψ' _)
  obtain ⟨d₁⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) r₂₃ pr₂
  obtain ⟨d₂⟩ := nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) r₁₃ pr₂
  exact nonempty_iso_comp_of_kernel ((upperStar pr₁).commShiftIso _)
    ((tensorLisse (artinSchreierOf ψ' b) (isLisse_artinSchreierOf ψ' b)).commShiftIso _)
    ((derivedLowerShriek k₀ l pr₂).commShiftIso _) bc (tA ≪≫ Functor.isoWhiskerLeft _ eA)
    (pf ≪≫ Functor.isoWhiskerRight eB _)
    ((upperStarCompIso r₁₂ pr₁).symm ≪≫
      upperStarCongrIso (pullback.tripleProj₁₃_fst πV πV πV).symm ≪≫ upperStarCompIso r₁₃ pr₁)
    (d₁.symm ≪≫ derivedLowerShriekIsoOfEq (pullback.tripleProj₁₃_snd πV πV πV).symm ≪≫ d₂)

end AlgebraicGeometry.WeilComplex
