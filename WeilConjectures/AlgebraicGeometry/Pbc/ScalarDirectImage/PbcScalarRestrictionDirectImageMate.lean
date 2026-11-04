/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.ScalarDirectImage.PbcScalarCoefficientInverseImage
public import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeDirectImageCoherence
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCompletedObjectComplete
import WeilConjectures.AlgebraicGeometry.FiniteFreeDirectImage.FiniteFreeRestrictionDirectImageMate

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
  obtain ⟨d, hfree⟩ := pbcScalarCoefficientMap_finiteFree l E F i Y
  exact FiniteFreeDirectImage.restrictionDirectImageMate_isIso g _ _ _ _ _ _ _ _ _ d hfree

end AlgebraicGeometry.Scheme
