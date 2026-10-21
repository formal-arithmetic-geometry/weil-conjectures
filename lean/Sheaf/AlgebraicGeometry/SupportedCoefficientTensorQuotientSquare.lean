/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct

/-! # Quotient normalization determines the ordinary coefficient tensor square -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v uA
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale

private noncomputable instance (priority := 2000) canonicalConstantPresheaf
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (Functor.const X.Etaleᵒᵖ (C := ModuleCat.{u + 1} A)).Monoidal :=
  Functor.Monoidal.const _ _

private noncomputable instance (priority := 2000) canonicalConstantSheaf
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).Monoidal :=
  monoidalConstantSheaf _ _

section ConstantMonoidal
variable (A : Type uA) [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]

private instance evaluationMonoidal {C A : Type*} [Category C] [Category A]
    [MonoidalCategory A] (U : C) : ((evaluation C A).obj U).Monoidal :=
  Functor.CoreMonoidal.toMonoidal { εIso := Iso.refl _, μIso _ _ := Iso.refl _ }

section
variable {C A : Type*} [Category C] [Category A] [MonoidalCategory A]
  (J : GrothendieckTopology C) [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  {T : C} (hT : IsTerminal T)
attribute [local instance] Sheaf.monoidalCategory

private noncomputable instance sectionsMonoidal : ((sheafSections J A).obj (op T)).LaxMonoidal :=
  inferInstanceAs (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op T)).LaxMonoidal

private instance constantPresheafAdj_monoidal : (constantPresheafAdj A hT).IsMonoidal := by
  constructor
  · simp [constantPresheafAdj, Functor.LaxMonoidal.ε, Functor.OplaxMonoidal.η]
  · intro X Y
    simp [constantPresheafAdj, Functor.LaxMonoidal.μ, Functor.OplaxMonoidal.δ]

private instance constantSheafAdj_monoidal : (constantSheafAdj J A hT).IsMonoidal := by
  unfold constantSheafAdj
  infer_instance
end

section Pullback
variable {C D A : Type*} [Category C] [Category D] [Category A]
  [MonoidalCategory A] [BraidedCategory A]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A]
  [F.IsContinuous J K]
attribute [local instance] Sheaf.monoidalCategory

private noncomputable def precomposeEvaluationIso (T : C) :
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ (evaluation Cᵒᵖ A).obj (op T) ≅
      (evaluation Dᵒᵖ A).obj (op (F.obj T)) := Iso.refl _

private instance precomposeEvaluation_monoidal (T : C) : NatTrans.IsMonoidal
    (precomposeEvaluationIso (A := A) F T).hom where
  unit := by simp [precomposeEvaluationIso,
    Functor.LaxMonoidal.ε]
  tensor P Q := by simp [precomposeEvaluationIso,
    Functor.LaxMonoidal.μ]

private instance sheafSectionsNatIsoEvaluation_monoidal {T : C} : NatTrans.IsMonoidal
    (sheafSectionsNatIsoEvaluation J A (X := T)).hom := by
  change NatTrans.IsMonoidal (𝟙 (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj (op T)))
  infer_instance

private noncomputable def pushforwardSectionsIso (T : C) :
    F.sheafPushforwardContinuous A J K ⋙ (sheafSections J A).obj (op T) ≅
      (sheafSections K A).obj (op (F.obj T)) :=
  Functor.isoWhiskerLeft _ (sheafSectionsNatIsoEvaluation J A) ≪≫
    (Functor.associator (F.sheafPushforwardContinuous A J K)
      (sheafToPresheaf J A) ((evaluation Cᵒᵖ A).obj (op T))).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
        F A J K).symm ((evaluation Cᵒᵖ A).obj (op T)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (precomposeEvaluationIso F T) ≪≫
    (sheafSectionsNatIsoEvaluation K A).symm

private instance pushforwardSections_monoidal (T : C) : NatTrans.IsMonoidal
    (pushforwardSectionsIso (A := A) F J K T).hom := by
  dsimp only [pushforwardSectionsIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

omit [MonoidalCategory A] [BraidedCategory A] [(J.W (A := A)).IsMonoidal]
  [(K.W (A := A)).IsMonoidal] [HasWeakSheafify K A] in
private theorem pushforwardUnderlying_inv_app (P : Sheaf K A) :
    (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F A J K).inv.app P = 𝟙 _ := by
  have h :=
    (Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      F A J K).hom_inv_id_app P
  rw [Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app,
    Category.id_comp] at h
  exact h

end Pullback

section SectionMaps
variable {C B : Type*} [Category C] [Category B] [MonoidalCategory B]
    (J : GrothendieckTopology C) [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
attribute [local instance] Sheaf.monoidalCategory

private theorem sectionsMap_monoidal {T U : C} (a : T ⟶ U) :
    NatTrans.IsMonoidal ((sheafSections J B).map a.op) := by
  constructor
  · with_unfolding_all change (𝟙 _ ≫ _) ≫ _ = 𝟙 _ ≫ _
    simpa using ((Functor.LaxMonoidal.ε (sheafToPresheaf J B)).naturality a.op).symm
  · intro P Q
    with_unfolding_all change (𝟙 _ ≫ _) ≫ _ = _ ≫ (𝟙 _ ≫ _)
    simpa using ((Functor.LaxMonoidal.μ (sheafToPresheaf J B) P Q).naturality a.op).symm
end SectionMaps

omit [HasSmallSiteSheafify A] [MonoidalPreadditive A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A] in
private theorem terminalSectionsIso_monoidal {X S : Scheme.{u}} (f : X ⟶ S) :
    NatTrans.IsMonoidal (lowerStarCompSheafSectionsTerminalIso A f).hom := by
  let e := (PreservesTerminal.iso f.Etale).op.symm
  have h := sectionsMap_monoidal X.smallEtaleTopology (B := A) e.hom.unop
  have h' : NatTrans.IsMonoidal ((sheafSections X.smallEtaleTopology A).map e.hom) := h
  let : NatTrans.IsMonoidal ((sheafSections X.smallEtaleTopology A).map e.hom) := h'
  have hmono : NatTrans.IsMonoidal
      ((pushforwardSectionsIso (A := A) f.Etale S.smallEtaleTopology X.smallEtaleTopology
        (⊤_ S.Etale)).hom ≫ (sheafSections X.smallEtaleTopology A).map e.hom) := by
    infer_instance
  have he : (pushforwardSectionsIso (A := A) f.Etale S.smallEtaleTopology
        X.smallEtaleTopology (⊤_ S.Etale)).hom ≫
      (sheafSections X.smallEtaleTopology A).map e.hom =
      (lowerStarCompSheafSectionsTerminalIso A f).hom := by
    ext P
    simp [pushforwardSectionsIso, precomposeEvaluationIso,
      lowerStarCompSheafSectionsTerminalIso, e, pushforwardUnderlying_inv_app]
  rw [he] at hmono
  exact hmono

omit [HasSmallSiteSheafify A] [MonoidalPreadditive A]
  [Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A] in
private theorem constantPullback_monoidal {X S : Scheme.{u}} (f : X ⟶ S) :
    NatTrans.IsMonoidal (Scheme.upperStarConstantSheafIso A f).inv := by
  let adj₁ := (constantSheafAdj S.smallEtaleTopology A terminalIsTerminal).comp
    (upperStarLowerStarAdjunction A f)
  let adj₂ := constantSheafAdj X.smallEtaleTopology A terminalIsTerminal
  let e := lowerStarCompSheafSectionsTerminalIso A f
  let : NatTrans.IsMonoidal e.hom := terminalSectionsIso_monoidal A f
  have h := isMonoidal_conjugateEquiv_symm adj₁ adj₂ e.hom
  have he : (conjugateEquiv adj₁ adj₂).symm e.hom =
      (Scheme.upperStarConstantSheafIso A f).inv := by
    ext P
    simp [Scheme.upperStarConstantSheafIso, Adjunction.leftAdjointUniq,
      conjugateEquiv_symm_apply_app, adj₁, adj₂, e]
  rw [he] at h
  exact h

end ConstantMonoidal

private theorem constantTensor_eq (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) (M N : ModuleCat.{u + 1} A) :
    supportedConstantTensor A X M N =
      Functor.OplaxMonoidal.δ
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) M N := by
  rfl

private theorem constantTensor_pullback (A : Type (u + 1)) [CommRing A]
    {P Q : Scheme.{u}} (h : Q ⟶ P) (M N : ModuleCat.{u + 1} A) :
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app (M ⊗ N) ≫
        (upperStar (ModuleCat.{u + 1} A) h).map (supportedConstantTensor A P M N) ≫
        Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) h)
          ((constantSheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)
          ((constantSheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N) =
      supportedConstantTensor A Q M N ≫
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app M ⊗ₘ
          (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app N) := by
  let C := ModuleCat.{u + 1} A
  let e := Scheme.upperStarConstantSheafIso C h
  let : NatTrans.IsMonoidal e.inv := constantPullback_monoidal C h
  apply (cancel_epi (Functor.LaxMonoidal.μ
    (constantSheaf Q.smallEtaleTopology C) M N)).1
  have hm := NatTrans.IsMonoidal.tensor (τ := e.inv) M N
  dsimp only [Functor.LaxMonoidal.comp_μ] at hm
  rw [constantTensor_eq, constantTensor_eq]
  rw [← Category.assoc, ← Category.assoc, hm]
  simp only [Category.assoc]
  erw [← Functor.map_comp_assoc, Functor.Monoidal.μ_δ]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Functor.Monoidal.μ_δ_assoc, Functor.Monoidal.μ_δ, Category.comp_id]

private theorem tensorSquare_of_quotients
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (H : C ⥤ D) [H.OplaxMonoidal]
    {C₀ C₁ C₂ F₀ F₁ F₂ : C} {D₀ D₁ D₂ G₀ G₁ G₂ : D}
    (q₀ : C₀ ⟶ F₀) (q₁ : C₁ ⟶ F₁) (q₂ : C₂ ⟶ F₂)
    (q₀' : D₀ ⟶ G₀) [Epi q₀'] (q₁' : D₁ ⟶ G₁) (q₂' : D₂ ⟶ G₂)
    (σ₀ : D₀ ⟶ H.obj C₀) (σ₁ : D₁ ⟶ H.obj C₁) (σ₂ : D₂ ⟶ H.obj C₂)
    (a₀ : G₀ ⟶ H.obj F₀) (a₁ : G₁ ⟶ H.obj F₁) (a₂ : G₂ ⟶ H.obj F₂)
    (τ : F₀ ⟶ F₁ ⊗ F₂) (τ' : G₀ ⟶ G₁ ⊗ G₂)
    (κ : C₀ ⟶ C₁ ⊗ C₂) (κ' : D₀ ⟶ D₁ ⊗ D₂)
    (hτ : q₀ ≫ τ = κ ≫ (q₁ ⊗ₘ q₂))
    (hτ' : q₀' ≫ τ' = κ' ≫ (q₁' ⊗ₘ q₂'))
    (hσ : σ₀ ≫ H.map κ ≫ Functor.OplaxMonoidal.δ H C₁ C₂ = κ' ≫ (σ₁ ⊗ₘ σ₂))
    (h₀ : q₀' ≫ a₀ = σ₀ ≫ H.map q₀)
    (h₁ : q₁' ≫ a₁ = σ₁ ≫ H.map q₁)
    (h₂ : q₂' ≫ a₂ = σ₂ ≫ H.map q₂) :
    a₀ ≫ H.map τ ≫ Functor.OplaxMonoidal.δ H F₁ F₂ = τ' ≫ (a₁ ⊗ₘ a₂) := by
  apply (cancel_epi q₀').1
  rw [reassoc_of% h₀, ← H.map_comp_assoc, hτ, H.map_comp, Category.assoc,
    ← Functor.OplaxMonoidal.δ_natural, reassoc_of% hσ,
    tensorHom_comp_tensorHom, ← h₁, ← h₂, ← tensorHom_comp_tensorHom,
    ← Category.assoc, ← hτ', Category.assoc]

/-- The first projected supported constant quotient.
Source: Tag 0F1E (blueprint: lem-pur-supported-coefficient-tensor-quotient-square). -/
noncomputable def supportFirstOrdinaryCoefficientQuotient
    (A : Type (u + 1)) [CommRing A] {S X Y B : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) [IsClosedImmersion b]
    (M : ModuleCat.{u + 1} A) :
    (constantSheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)).obj M ⟶
      (supportedFirstCoefficients A f g b).obj M :=
  (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (pullback.fst f g)).inv.app M ≫
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).map
      (supportedCoefficientQuotient A b M)

/-- The second projected supported constant quotient.
Source: Tag 0F1E (blueprint: lem-pur-supported-coefficient-tensor-quotient-square). -/
noncomputable def supportSecondOrdinaryCoefficientQuotient
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d]
    (N : ModuleCat.{u + 1} A) :
    (constantSheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)).obj N ⟶
      (supportedSecondCoefficients A f g d).obj N :=
  (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) (pullback.snd f g)).inv.app N ≫
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).map
      (supportedCoefficientQuotient A d N)

private theorem coefficientTensor_quotient
    (A : Type (u + 1)) [CommRing A] {S X Y B D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (M N : ModuleCat.{u + 1} A) :
    supportedCoefficientQuotient A (supportedProductImmersion f g b d) (M ⊗ N) ≫
        supportedCoefficientTensor A f g b d M N =
      supportedConstantTensor A (pullback f g) M N ≫
        (supportFirstOrdinaryCoefficientQuotient A f g b M ⊗ₘ
          supportSecondOrdinaryCoefficientQuotient A f g d N) := by
  have h := (exists_unique_supportedCoefficientTensor A f g b d M N).choose_spec.1
  change supportedCoefficientQuotient A (supportedProductImmersion f g b d) (M ⊗ N) ≫
    supportedCoefficientTensor A f g b d M N = _ at h
  rw [h]
  change (_ ≫ (_ ⊗ₘ _)) ≫ (_ ⊗ₘ _) = _ ≫ ((_ ≫ _) ⊗ₘ (_ ≫ _))
  rw [Category.assoc, tensorHom_comp_tensorHom]

private theorem coefficientQuotient_epi
    (A : Type (u + 1)) [CommRing A] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (M : ModuleCat.{u + 1} A) :
    Epi (supportedCoefficientQuotient A i M) := by
  constructor
  intro F a b hab
  let adj := supportedCoefficientAdjunction A i
  apply (adj.homEquiv M F).injective
  have : Mono ((supportedEtaleSectionsι A X i.openComplement).app F) := by
    dsimp [supportedEtaleSectionsι]
    infer_instance
  apply (cancel_mono ((supportedEtaleSectionsι A X i.openComplement).app F)).1
  apply ((constantSheafΓAdj X.smallEtaleTopology (ModuleCat.{u + 1} A)).homEquiv M F).symm.injective
  have ha := (exists_unique_supportedCoefficientAdjunction A i).choose_spec.1 M F
    ((adj.homEquiv M F) a)
  have hb := (exists_unique_supportedCoefficientAdjunction A i).choose_spec.1 M F
    ((adj.homEquiv M F) b)
  erw [Equiv.symm_apply_apply] at ha hb
  exact ha.symm.trans (hab.trans hb)

/-- Maps preserving the three constant quotients commute with the ordinary supported
coefficient tensor comparison.
Source: Tag 0F1E, the coefficient calculation in step 11 of
lem-pur-supported-product-localization.
(blueprint: lem-pur-supported-coefficient-tensor-quotient-square).
Proof: cancel the epic product-support quotient. Its three normalization equations
reduce the square to inverse image of the constant tensor pairing. The constant
inverse-image comparison is monoidal: it is the conjugate of the monoidal global
sections comparison under the constant adjunctions. Its tensor equation gives the
constant square. Naturality of the inverse-image tensor comparison and composition
of tensor maps then give the desired equality. No flatness or nonempty-support
hypothesis is used. -/
theorem supportedCoefficientTensor_quotientSquare
    (A : Type (u + 1)) [CommRing A]
    {S X Y B D S' X' Y' B' D' : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    (f' : X' ⟶ S') (g' : Y' ⟶ S') (b' : B' ⟶ X') (d' : D' ⟶ Y')
    [IsClosedImmersion b] [IsClosedImmersion d]
    [IsClosedImmersion b'] [IsClosedImmersion d']
    (h : pullback f' g' ⟶ pullback f g) (M N : ModuleCat.{u + 1} A)
    (a₀ : (supportedCoefficients A (supportedProductImmersion f' g' b' d')).obj (M ⊗ N) ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj
        ((supportedCoefficients A (supportedProductImmersion f g b d)).obj (M ⊗ N)))
    (a₁ : (supportedFirstCoefficients A f' g' b').obj M ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj ((supportedFirstCoefficients A f g b).obj M))
    (a₂ : (supportedSecondCoefficients A f' g' d').obj N ⟶
      (upperStar (ModuleCat.{u + 1} A) h).obj ((supportedSecondCoefficients A f g d).obj N))
    (h₀ : supportedCoefficientQuotient A (supportedProductImmersion f' g' b' d') (M ⊗ N) ≫
        a₀ = (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app (M ⊗ N) ≫
          (upperStar (ModuleCat.{u + 1} A) h).map
            (supportedCoefficientQuotient A (supportedProductImmersion f g b d) (M ⊗ N)))
    (h₁ : supportFirstOrdinaryCoefficientQuotient A f' g' b' M ≫ a₁ =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app M ≫
        (upperStar (ModuleCat.{u + 1} A) h).map
          (supportFirstOrdinaryCoefficientQuotient A f g b M))
    (h₂ : supportSecondOrdinaryCoefficientQuotient A f' g' d' N ≫ a₂ =
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app N ≫
        (upperStar (ModuleCat.{u + 1} A) h).map
          (supportSecondOrdinaryCoefficientQuotient A f g d N)) :
    a₀ ≫ (upperStar (ModuleCat.{u + 1} A) h).map
        (supportedCoefficientTensor A f g b d M N) ≫
      Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) h)
        ((supportedFirstCoefficients A f g b).obj M)
        ((supportedSecondCoefficients A f g d).obj N) =
      supportedCoefficientTensor A f' g' b' d' M N ≫ (a₁ ⊗ₘ a₂) := by
  have := coefficientQuotient_epi A (supportedProductImmersion f' g' b' d') (M ⊗ N)
  exact tensorSquare_of_quotients (upperStar (ModuleCat.{u + 1} A) h)
    (supportedCoefficientQuotient A (supportedProductImmersion f g b d) (M ⊗ N))
    (supportFirstOrdinaryCoefficientQuotient A f g b M)
    (supportSecondOrdinaryCoefficientQuotient A f g d N)
    (supportedCoefficientQuotient A (supportedProductImmersion f' g' b' d') (M ⊗ N))
    (supportFirstOrdinaryCoefficientQuotient A f' g' b' M)
    (supportSecondOrdinaryCoefficientQuotient A f' g' d' N)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app (M ⊗ N))
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app M)
    ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) h).inv.app N)
    a₀ a₁ a₂ (supportedCoefficientTensor A f g b d M N)
    (supportedCoefficientTensor A f' g' b' d' M N)
    (supportedConstantTensor A (pullback f g) M N)
    (supportedConstantTensor A (pullback f' g') M N)
    (coefficientTensor_quotient A f g b d M N)
    (coefficientTensor_quotient A f' g' b' d' M N)
    (constantTensor_pullback A h M N) h₀ h₁ h₂

end AlgebraicGeometry.Etale
