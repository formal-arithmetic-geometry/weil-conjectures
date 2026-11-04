/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.ScalarDirectImage.PbcScalarCoefficientInverseImage
public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCompletedObjectComplete

/-! # The finite-free inverse scalar mate for the completed coefficient inclusion

The completed target coefficient sheaf is finite free over the completed source coefficient
sheaf, so the inverse scalar mate of the canonical restriction/direct-image comparison is
invertible.

Source: Stacks Project, Tags 0B56 and 07A6; Bhatt--Scholze, Lemma 6.8.2(1).
(blueprint: lem-pbc-scalar-ambient-operation-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

private local instance (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)

/-- Restricting the unit module along a ring-sheaf isomorphism gives the unit module. -/
private def restrictionUnitIso (X : Scheme.{u})
    {R S : Sheaf (ProEt.topology X) RingCat.{u + 1}} (e : S ≅ R) :
    (SheafOfModules.restrictScalars.{u + 1} e.hom).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · let eU := ((sheafToPresheaf (ProEt.topology X) RingCat).mapIso e).app U
    exact ModuleCat.restrictScalarsIsoOfEquiv eU.ringCatIsoToRingEquiv
  · intro U V f
    ext x
    exact ConcreteCategory.congr_hom (e.inv.hom.naturality f) x

/-- Restriction of scalars along two composites with equal values agree. -/
private def restrictScalarsSquareIso {X : Scheme.{u}}
    {R R' S S' : Sheaf (ProEt.topology X) RingCat.{u + 1}}
    (α : R ⟶ S) (β : S ⟶ S') (γ : R ⟶ R') (δ : R' ⟶ S') (h : α ≫ β = γ ≫ δ)
    (M : SheafOfModules.{u + 1} S') :
    (SheafOfModules.restrictScalars.{u + 1} α).obj
        ((SheafOfModules.restrictScalars.{u + 1} β).obj M) ≅
      (SheafOfModules.restrictScalars.{u + 1} γ).obj
        ((SheafOfModules.restrictScalars.{u + 1} δ).obj M) :=
  (Iso.refl ((SheafOfModules.restrictScalars.{u + 1} (α ≫ β)).obj M)) ≪≫
    eqToIso (congrArg (fun φ ↦ (SheafOfModules.restrictScalars.{u + 1} φ).obj M) h) ≪≫
      Iso.refl _

/-- The completed target coefficient sheaf is finite free over the completed source one.
Source: Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
theorem pbcScalarCoefficientMap_finiteFree (W : Scheme.{u}) :
    ∃ d : ℕ, Nonempty
      ((pbcRestrict (pbcScalarCoefficientMap l E F i W)).obj
          (SheafOfModules.unit ((adicLisseForget W).obj
            (pbcAdicCompletion W (pbcIntegralDatum l F)))) ≅
        ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget W).obj
          (pbcAdicCompletion W (pbcIntegralDatum l E)))) := by
  let V := adicLisseForget W
  let eE := WeilConjectures.purCoefficientIso l E W
  let eF := WeilConjectures.purCoefficientIso l F W
  have hmap : WeilConjectures.integralCompletedScalarMap l E F i W =
      WeilConjectures.completedCoefficientMap l E F i W := by
    apply (WeilConjectures.completedCoefficientMap_existsUnique l E F i W).unique
    · exact (WeilConjectures.integralCompletedScalarMap_existsUnique l E F i W).exists.choose_spec
    · exact (WeilConjectures.completedCoefficientMap_existsUnique l E F i W).exists.choose_spec
  have hsq := scalarComplete_coefficientScalar_square l E F i W
  rw [hmap] at hsq
  obtain ⟨b⟩ := (WeilConjectures.finiteFreeCompletedScalarComparison l E F i W).1
  refine ⟨WeilConjectures.completedScalarRelativeDegree l E F i, ⟨?_⟩⟩
  let Φ := pbcRestrict eE.hom
  refine (pbcRestrict (pbcScalarCoefficientMap l E F i W)).mapIso
      (restrictionUnitIso W (V.mapIso eF)).symm ≪≫
    restrictScalarsSquareIso (V.map (pbcScalarCoefficientMap l E F i W)) (V.map eF.hom)
      (V.map eE.hom) (V.map (WeilConjectures.completedCoefficientMap l E F i W))
      (by rw [← V.map_comp, ← V.map_comp, hsq]) _ ≪≫ Φ.mapIso b ≪≫
    PreservesProduct.iso Φ _ ≪≫ Pi.mapIso (fun _ ↦ restrictionUnitIso W (V.mapIso eE))

/-- Invertibility of an inverse mate is independent of the chosen left adjoints. -/
private theorem inverseMate_isIso_of_isIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ L₁' : A ⥤ B} {R₁ : B ⥤ A} {L₂ L₂' : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (b₁ : L₁' ⊣ R₁) (b₂ : L₂' ⊣ R₂)
    (β : TwoSquare R₁ H G R₂)
    [IsIso (((mateEquiv b₁ b₂).symm β).natTrans)] :
    IsIso (((mateEquiv a₁ a₂).symm β).natTrans) := by
  let e₁ : L₁' ≅ L₁ := (conjugateIsoEquiv a₁ b₁).symm (Iso.refl R₁)
  let e₂ : L₂' ≅ L₂ := (conjugateIsoEquiv a₂ b₂).symm (Iso.refl R₂)
  have h₁ : conjugateEquiv a₁ b₁ e₁.hom = 𝟙 R₁ :=
    (conjugateEquiv a₁ b₁).apply_symm_apply (𝟙 R₁)
  have h₂ : conjugateEquiv a₂ b₂ e₂.hom = 𝟙 R₂ :=
    (conjugateEquiv a₂ b₂).apply_symm_apply (𝟙 R₂)
  let w := (mateEquiv a₁ a₂).symm β
  let w' := (mateEquiv b₁ b₂).symm β
  have h : w'.whiskerLeft e₁.hom = w.whiskerRight e₂.hom := by
    apply (mateEquiv a₁ b₂).injective
    rw [conjugateEquiv_mateEquiv_vcomp a₁ b₁ b₂ e₁.hom w',
      mateEquiv_conjugateEquiv_vcomp a₁ a₂ b₂ w e₂.hom]
    simp only [w, w', Equiv.apply_symm_apply, h₁, h₂]
    ext X
    simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom]
  let : ∀ X, IsIso (w.natTrans.app X) := fun X ↦ by
    have hc := congrArg (fun t ↦ t.natTrans.app X) h
    change w'.app X ≫ H.map (e₁.hom.app X) = e₂.hom.app (G.obj X) ≫ w.app X at hc
    have : IsIso (e₂.hom.app (G.obj X) ≫ w.app X) := by
      rw [← hc]
      infer_instance
    exact IsIso.of_isIso_comp_left (e₂.hom.app (G.obj X)) (w.app X)
  exact NatIso.isIso_of_isIso_app _

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The inverse scalar mate of the canonical restriction/direct-image comparison is
invertible for the completed coefficient inclusion.
Source: Stacks Project, Tags 0B56 and 07A6
(blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
theorem pbcScalarRestrictionDirectImageMate_isIso :
    IsIso (((mateEquiv (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
      (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))).symm
        (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionDerivedDirectImage g
          (pbcAdicCompletion Y (pbcIntegralDatum l E)) (pbcAdicCompletion Y (pbcIntegralDatum l F))
          (pbcAdicCompletion X (pbcIntegralDatum l E)) (pbcAdicCompletion X (pbcIntegralDatum l F))
          (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
          (pbcActualCoefficientIso g _) (pbcActualCoefficientIso g _)
          (pbcScalarCoefficientMap_inverseImage l E F i g)).inv)).natTrans) := by
  classical
  let R' : FiniteFreeDirectImage.Coefficients g :=
    ⟨pbcAdicCompletion Y (pbcIntegralDatum l E), pbcAdicCompletion X (pbcIntegralDatum l E),
      pbcActualCoefficientIso g _⟩
  let S' : FiniteFreeDirectImage.Coefficients g :=
    ⟨pbcAdicCompletion Y (pbcIntegralDatum l F), pbcAdicCompletion X (pbcIntegralDatum l F),
      pbcActualCoefficientIso g _⟩
  let a' : FiniteFreeDirectImage.CoefficientMap R' S' :=
    ⟨pbcScalarCoefficientMap l E F i Y, pbcScalarCoefficientMap l E F i X,
      pbcScalarCoefficientMap_inverseImage l E F i g⟩
  obtain ⟨sV, sU, _, _, hi, _⟩ := FiniteFreeDirectImage.finiteFreeDirectImageCoherence g
  obtain ⟨d, ⟨b⟩⟩ := pbcScalarCoefficientMap_finiteFree l E F i Y
  let N := SheafOfModules.unit ((adicLisseForget Y).obj (pbcAdicCompletion Y
    (pbcIntegralDatum l E)))
  let : HasBiproduct (fun _ : Fin d ↦ N) := HasBiproduct.of_hasProduct _
  have : IsIso (FiniteFreeDirectImage.comparison sV sU a') := by
    refine (hi R' S' a' d ⟨b ≪≫ ?_⟩).1
    exact (biproduct.isoProduct (fun _ : Fin d ↦ N)).symm ≪≫
      biproduct.isoCoproduct (fun _ : Fin d ↦ N) ≪≫
        Sigma.whiskerEquiv Equiv.ulift.symm (fun _ ↦ Iso.refl N)
  let δ := proEtaleRingRestrictionDerivedDirectImage g
    (pbcAdicCompletion Y (pbcIntegralDatum l E)) (pbcAdicCompletion Y (pbcIntegralDatum l F))
    (pbcAdicCompletion X (pbcIntegralDatum l E)) (pbcAdicCompletion X (pbcIntegralDatum l F))
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcActualCoefficientIso g _) (pbcActualCoefficientIso g _)
    (pbcScalarCoefficientMap_inverseImage l E F i g)
  have hm : (mateEquiv (sU.adjunction a'.source) (sV.adjunction a'.target)
      (TwoSquare.mk _ _ _ _ (FiniteFreeDirectImage.comparison sV sU a'))).natTrans =
      δ.inv := by
    rw [FiniteFreeDirectImage.comparison, iterated_mateEquiv_conjugateEquiv]
    exact (conjugateEquiv _ _).apply_symm_apply δ.inv
  have he : ((mateEquiv (sU.adjunction a'.source) (sV.adjunction a'.target)).symm
      (TwoSquare.mk _ _ _ _ δ.inv)).natTrans =
        FiniteFreeDirectImage.comparison sV sU a' := by
    apply congrArg TwoSquare.natTrans
    apply (mateEquiv (sU.adjunction a'.source) (sV.adjunction a'.target)).injective
    rw [Equiv.apply_symm_apply]
    ext X
    exact (NatTrans.congr_app hm X).symm
  have : IsIso (((mateEquiv (sU.adjunction a'.source)
      (sV.adjunction a'.target)).symm (TwoSquare.mk _ _ _ _ δ.inv)).natTrans) := by
    rw [he]
    infer_instance
  exact inverseMate_isIso_of_isIso
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i X))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i Y))
    (sU.adjunction a'.source) (sV.adjunction a'.target) (TwoSquare.mk _ _ _ _ δ.inv)

end AlgebraicGeometry.Scheme
