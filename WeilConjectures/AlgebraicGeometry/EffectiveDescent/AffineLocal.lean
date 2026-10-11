/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Affine
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Invariant

/-!
# Effectivity on invariant affine opens over affine opens of the base

Let `p : X ⟶ Y` be affine, flat and surjective and let `D` be a descent datum on `V` over `X`
relative to `p`. If `U ⊆ V` is an invariant affine open subscheme lying over an affine open
`W ⊆ Y`, then the restriction of `D` to `U` is effective
(`CategoryTheory.Over.DescentDatum.isEffective_restrict_of_isAffineOpen`): it is a descent datum
relative to the morphism of affine schemes `p⁻¹ W ⟶ W`, which is effective by affine
faithfully flat descent.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}

section Localize

variable {W : Y.Opens} {U : V.left.Opens} (hUW : U ≤ (V.hom ≫ p) ⁻¹ᵁ W)

lemma range_ι_comp_hom_subset : Set.range (U.ι ≫ V.hom) ⊆ Set.range (p ⁻¹ᵁ W).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨u, rfl⟩
  exact hUW u.2

/-- The structure morphism of `U ⊆ V`, lifted to `p⁻¹ W`. -/
noncomputable def homToPreimage : U.toScheme ⟶ (p ⁻¹ᵁ W).toScheme :=
  IsOpenImmersion.lift (p ⁻¹ᵁ W).ι (U.ι ≫ V.hom) (range_ι_comp_hom_subset hUW)

@[reassoc (attr := simp)]
lemma homToPreimage_ι : homToPreimage hUW ≫ (p ⁻¹ᵁ W).ι = U.ι ≫ V.hom :=
  IsOpenImmersion.lift_fac _ _ _

lemma comp_ι_comp_eq {T : Scheme.{u}} {f₁ f₂ : T ⟶ (p ⁻¹ᵁ W).toScheme}
    (h : f₁ ≫ p ∣_ W = f₂ ≫ p ∣_ W) :
    (f₁ ≫ (p ⁻¹ᵁ W).ι) ≫ p = (f₂ ≫ (p ⁻¹ᵁ W).ι) ≫ p := by
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% h]

variable {D : DescentDatum p V} (hU : D.IsInvariant U)

/-- The restriction of `D` to `U ⊆ V`, as a descent datum relative to `p⁻¹ W ⟶ W`. -/
noncomputable def restrictBase : DescentDatum (p ∣_ W) (Over.mk (homToPreimage hUW)) where
  transport f₁ f₂ h a := Over.homMk ((D.restrict U hU).transport (f₁ ≫ (p ⁻¹ᵁ W).ι)
      (f₂ ≫ (p ⁻¹ᵁ W).ι) (comp_ι_comp_eq h)
      (Over.homMk a.left (by simp [← homToPreimage_ι, ← Over.w a]))).left (by
    rw [← cancel_mono (p ⁻¹ᵁ W).ι, Over.mk_hom, Category.assoc, homToPreimage_ι]
    exact Over.w ((D.restrict U hU).transport _ _ _ _))
  transport_homMk_comp g f₁ f₂ h a := by
    ext
    exact (D.restrict U hU).transport_left_eq_comp g _ _ _ _ _ (by simp) (by simp) _ (by simp)
  transport_self f a := by
    ext
    exact ((D.restrict U hU).transport_left_congr rfl _ rfl rfl _ _ rfl).trans
      (by rw [transport_self]; rfl)
  transport_transport f₁ f₂ f₃ h₁₂ h₂₃ a := by
    ext
    refine ((D.restrict U hU).transport_left_congr (comp_ι_comp_eq h₂₃) _ rfl rfl
      ((D.restrict U hU).transport _ _ (comp_ι_comp_eq h₁₂) _) _ rfl).trans ?_
    rw [transport_transport]
    rfl

end Localize

/-- **Effectivity on invariant affine opens.** Let `p : X ⟶ Y` be affine, flat and surjective,
`W ⊆ Y` an affine open and `U ⊆ V` an invariant affine open lying over `W`. Then the restriction
of a descent datum `D` on `V` to `U` is effective. -/
theorem isEffective_restrict_of_isAffineOpen [IsAffineHom p] [Flat p] [Surjective p]
    (D : DescentDatum p V) {U : V.left.Opens} (hU : D.IsInvariant U) (hUa : IsAffineOpen U)
    {W : Y.Opens} (hW : IsAffineOpen W) (hUW : U ≤ (V.hom ≫ p) ⁻¹ᵁ W) :
    (D.restrict U hU).IsEffective := by
  have : IsAffine W := hW
  have : IsAffine (p ⁻¹ᵁ W) := hW.preimage p
  have : IsAffine U := hUa
  have : IsAffine (Over.mk (homToPreimage hUW)).left := hUa
  have : Flat (p ∣_ W) := MorphismProperty.of_isPullback (isPullback_morphismRestrict p W).flip
    inferInstance
  have : Surjective (p ∣_ W) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p W).flip inferInstance
  obtain ⟨V₀, q, hq, hinv⟩ := (restrictBase hUW hU).isEffective_of_isAffine
  refine ⟨Over.mk (V₀.hom ≫ W.ι), q, ?_, fun {T} f₁ f₂ h a ↦ ?_⟩
  · simpa using hq.paste_vert (isPullback_morphismRestrict p W)
  · have hr : Set.range f₂ ⊆ Set.range (p ⁻¹ᵁ W).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      have ha : (a.left ≫ U.ι ≫ V.hom ≫ p) t ∈ W := hUW (a.left t).2
      rwa [← Category.assoc, ← Category.assoc, Over.w a, h] at ha
    let f₂' := IsOpenImmersion.lift (p ⁻¹ᵁ W).ι f₂ hr
    have hf₂' : f₂' ≫ (p ⁻¹ᵁ W).ι = f₂ := IsOpenImmersion.lift_fac _ _ _
    have h' : (a.left ≫ homToPreimage hUW) ≫ p ∣_ W = f₂' ≫ p ∣_ W := by
      rw [← cancel_mono W.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
        morphismRestrict_ι, homToPreimage_ι_assoc, reassoc_of% hf₂', ← h, ← Over.w a]
      simp
    have := hinv (a.left ≫ homToPreimage hUW) f₂' h' (Over.homMk a.left rfl)
    refine Eq.trans ?_ this
    congr 1
    exact (D.restrict U hU).transport_left_congr _ _ (by simp [← Over.w a]) hf₂' _ _ rfl

end CategoryTheory.Over.DescentDatum
