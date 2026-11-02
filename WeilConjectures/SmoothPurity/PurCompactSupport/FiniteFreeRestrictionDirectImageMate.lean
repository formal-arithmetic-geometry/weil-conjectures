/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageCoherence
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # The finite-free scalar mate of restriction and direct image

Source: Stacks Project, Tags 0B56 and 07A6.
(blueprint: lem-pur-finite-free-restriction-direct-image-mate).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurCompactSupport

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

/-- The inverse scalar mate of the canonical restriction/direct-image square is invertible
for a globally finite-free coefficient extension.

Source: Stacks Project, Tags 0B56 (projection formula) and 07A6 (derived adjunction);
finite-free direct-image coherence and the mate-transport argument of
`FiniteFreeProperScalarComparison`.
(blueprint: lem-pur-finite-free-restriction-direct-image-mate).

Proof: replace the finite-product basis by a coproduct basis indexed by ULift (Fin d).
The finite-free direct-image coherence theorem proves that the comparison for its
normalized scalar models is invertible. The iterated-mates identity identifies its
mate with the inverse canonical restriction/direct-image square. Conjugating the
identity transformations of scalar restriction identifies the normalized left
adjoints with the specified scalar left adjoints. The vertical composition identities
for mates express the two inverse mates as conjugates by these isomorphisms, so their
invertibility agrees. This includes rank zero and arbitrary unbounded inputs.
The conclusion is the explicit mate expression; it does not import the higher
compact-support comparison module. -/
theorem finiteFreeRestrictionDirectImageMate_isIso {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) (d : ℕ)
    (hfree : Nonempty
      ((pbcRestrict (a.map V)).obj
          (SheafOfModules.unit ((adicLisseForget V).obj (S.ring V))) ≅
        ∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit ((adicLisseForget V).obj (R.ring V)))) :
    IsIso (((mateEquiv (pbcDerivedScalarAdjunction (a.map U))
      (pbcDerivedScalarAdjunction (a.map V))).symm
        (TwoSquare.mk _ _ _ _ (proEtaleRingRestrictionDerivedDirectImage g
          (R.ring V) (S.ring V) (R.ring U) (S.ring U)
          (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)).inv)).natTrans) := by
  classical
  let R' : FiniteFreeDirectImage.Coefficients g := ⟨R.ring V, R.ring U, R.pull g⟩
  let S' : FiniteFreeDirectImage.Coefficients g := ⟨S.ring V, S.ring U, S.pull g⟩
  let a' : FiniteFreeDirectImage.CoefficientMap R' S' :=
    ⟨a.map V, a.map U, a.square g⟩
  obtain ⟨sV, sU, _, _, hi, _⟩ := FiniteFreeDirectImage.finiteFreeDirectImageCoherence g
  obtain ⟨b⟩ := hfree
  let N := SheafOfModules.unit ((adicLisseForget V).obj (R.ring V))
  let : HasBiproduct (fun _ : Fin d ↦ N) := HasBiproduct.of_hasProduct _
  let e : (∏ᶜ fun _ : Fin d ↦ N) ≅
      SheafOfModules.free (R := (adicLisseForget V).obj (R.ring V))
        (ULift.{u + 1} (Fin d)) :=
    (biproduct.isoProduct (fun _ : Fin d ↦ N)).symm ≪≫
      biproduct.isoCoproduct (fun _ : Fin d ↦ N) ≪≫
        Sigma.whiskerEquiv Equiv.ulift.symm (fun _ ↦ Iso.refl N)
  have : IsIso (FiniteFreeDirectImage.comparison sV sU a') :=
    (hi R' S' a' d ⟨b ≪≫ e⟩).1
  let δ := proEtaleRingRestrictionDerivedDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  have hm : (mateEquiv (sU.adjunction a'.source) (sV.adjunction a'.target)
      (TwoSquare.mk _ _ _ _ (FiniteFreeDirectImage.comparison sV sU a'))).natTrans =
      δ.inv := by
    rw [FiniteFreeDirectImage.comparison,
      iterated_mateEquiv_conjugateEquiv]
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
    (pbcDerivedScalarAdjunction (a.map U)) (pbcDerivedScalarAdjunction (a.map V))
    (sU.adjunction a'.source) (sV.adjunction a'.target) (TwoSquare.mk _ _ _ _ δ.inv)

end WeilConjectures.PurCompactSupport
