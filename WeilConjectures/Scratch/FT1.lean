import WeilConjectures.FourierTransform.AffineSpace
import WeilConjectures.SixFunctors.Etale.Derived.Exchange
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AffineSpace

variable (Λ : Type (u + 1)) [CommRing Λ]

noncomputable def leftDerivedUpperStarId' (X : Scheme.{u}) : L((𝟙 X)^*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
  Functor.leftDerivedFunctorNatIso _ (Etale.upperStarId _ X) ≪≫
    (𝟭 _).leftDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryIdIso _

noncomputable def rightDerivedLowerStarId' (X : Scheme.{u}) : R((𝟙 X)_*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
  ((derivedUpperStarLowerStarAdjunction _ (𝟙 X)).ofNatIsoLeft
    (leftDerivedUpperStarId' Λ X)).rightAdjointUniq Adjunction.id

theorem nonempty_iso_rightDerivedLowerShriek_of_eq_id {X : Scheme.{u}} (f : X ⟶ X)
    [HasCompactification f] (hf : f = 𝟙 X) :
    Nonempty (R(f)_![ModuleCat.{u + 1} Λ] ≅ 𝟭 _) := by
  subst hf
  exact ⟨rightDerivedLowerShriekIsoRightDerivedLowerStar _ (𝟙 X) ≪≫ rightDerivedLowerStarId' Λ X⟩

variable {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable (n : Type u) [Fintype n] (S : Scheme.{u})

/-- the section -/
noncomputable def zeroSectionFst :
    𝔸(n; S) ⟶ pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) :=
  pullback.lift (𝔸(n; S) ↘ S ≫ zeroSection n S) (𝟙 _) (by simp)

lemma isPullback_zeroSectionFst :
    IsPullback (zeroSectionFst n S) (𝔸(n; S) ↘ S) (pullback.fst _ _) (zeroSection n S) := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _).flip
  simp only [zeroSectionFst, pullback.lift_snd, zeroSection_over]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩


omit [Fact p.Prime] [Invertible (p : Λ)] in
lemma appTop_stdPairing_eq_zero_of_fst {X : Scheme.{u}}
    (g : X ⟶ pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) (h : X ⟶ S)
    (hg : g ≫ pullback.fst _ _ = h ≫ zeroSection n S) : g.appTop (stdPairing n S) = 0 := by
  simp only [stdPairing, map_sum, map_mul, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hg]
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, zeroSection_appTop_coord, map_zero,
    zero_mul, Finset.sum_const_zero]

theorem nonempty_iso_upperStar_artinSchreierSheafZMod_of_appTop_eq_zero {X X' : Scheme.{u}}
    [CharP Γ(X, ⊤) p] (g : X' ⟶ X) (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤))
    (hf : g.appTop f = 0) :
    Nonempty ((g)^*[ModuleCat.{u + 1} Λ].obj (artinSchreierSheafZMod X Ψ f) ≅ 𝟙_ _) := by
  let := X.overSpecZModOfCharP p
  let : X'.Over (Spec (.of (ULift.{u} (ZMod p)))) := ⟨g ≫ X ↘ Spec _⟩
  have : g.IsOver (Spec (.of (ULift.{u} (ZMod p)))) := ⟨rfl⟩
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheafOf_zero (Λ := Λ) X'
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom)
  exact ⟨artinSchreierSheafOfPullbackIso g _ f ≪≫ eqToIso (by rw [hf]) ≪≫ e⟩

variable [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
variable [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]


theorem step1 [Finite Λ] :
    Nonempty (D((pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))^*[ModuleCat.{u + 1} Λ]).obj
      (skyscraperZero Λ n S) ≅ R((zeroSectionFst n S)_*[ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) := by
  have sq := isPullback_zeroSectionFst n S
  have h₁ := isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring Λ isAddTorsion_of_finite
    sq.flip
  obtain ⟨u₁⟩ := nonempty_iso_leftDerivedUpperStar_unit (ModuleCat.{u + 1} Λ) (𝔸(n; S) ↘ S)
  exact ⟨((leftDerivedUpperStarIsoMapDerivedCategory _ _).app _).symm ≪≫
      (asIso (derivedBaseChangeMap _ sq.flip.toCommSq)).app (𝟙_ _) ≪≫ R((_)_*[_]).mapIso u₁⟩

noncomputable def singleUnitIso (X : Scheme.{u}) :
    (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
      (𝟙_ _) ≅ 𝟙_ _ := Iso.refl _

theorem step2 (Ψ : AddChar (ZMod p) Λ) :
    Nonempty (((-⊗ᴸ-(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))[ModuleCat.{u + 1} Λ]).obj
      (R((zeroSectionFst n S)_*[ModuleCat.{u + 1} Λ]).obj (𝟙_ _))).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S))) ≅
        R((zeroSectionFst n S)_*[ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) := by
  have sq := isPullback_zeroSectionFst n S
  have hs : IsClosedImmersion (zeroSectionFst n S) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq.flip inferInstance
  obtain ⟨u₂⟩ := nonempty_iso_upperStar_artinSchreierSheafZMod_of_appTop_eq_zero Λ
    (zeroSectionFst n S) Ψ (stdPairing n S)
    (appTop_stdPairing_eq_zero_of_fst n S _ (𝔸(n; S) ↘ S) (pullback.lift_fst _ _ _))
  have h₂ := isIso_rightDerivedLowerStarProjectionMap_of_isClosedImmersion Λ (zeroSectionFst n S)
  exact ⟨((asIso (rightDerivedLowerStarProjectionMap _ _)).app _).app _ ≪≫
      R((_)_*[_]).mapIso (((-⊗ᴸ-(_)[_]).obj _).mapIso
        ((singleFunctorCompLeftDerivedUpperStarIso _ _).app _ ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso u₂ ≪≫ singleUnitIso Λ _) ≪≫
        derivedTensorLeftUnitor _ _ _)⟩

theorem skyscraper [Finite Λ] (Ψ : AddChar (ZMod p) Λ) :
    Nonempty ((affineFourierTransform Λ n S Ψ).obj (skyscraperZero Λ n S) ≅
        (shiftFunctor _ (Fintype.card n : ℤ)).obj (𝟙_ _)) := by
  obtain ⟨e₁⟩ := step1 Λ n S
  obtain ⟨e₂⟩ := step2 Λ n S Ψ
  let π := 𝔸(n; S) ↘ S
  let s := zeroSectionFst n S
  have hs : IsClosedImmersion s := MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_zeroSectionFst n S).flip inferInstance
  have : HasCompactification (s ≫ pullback.snd π π) := by
    rw [show s ≫ pullback.snd π π = 𝟙 _ from pullback.lift_snd _ _ _]; infer_instance
  obtain ⟨c⟩ := nonempty_iso_rightDerivedLowerShriek_comp (ModuleCat.{u + 1} Λ) s
    (pullback.snd π π)
  obtain ⟨i⟩ := nonempty_iso_rightDerivedLowerShriek_of_eq_id Λ (s ≫ pullback.snd π π)
    (pullback.lift_snd _ _ _)
  exact ⟨(shiftFunctor _ _).mapIso ((R(pullback.snd π π)_![_]).mapIso
    (((-⊗ᴸ-(_)[_]).mapIso e₁).app _ ≪≫ e₂ ≪≫
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ s).app _).symm) ≪≫
    (c.app _).symm ≪≫ i.app _)⟩

end AlgebraicGeometry.Etale
