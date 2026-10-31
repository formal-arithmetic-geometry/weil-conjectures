/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitShift
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.CategoryTheory.Shift.RestrictFullyFaithful
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionResMate2

/-!
# The base change map of `Rν_*` for the derived extension of scalars commutes with the shifts

Let `φ : Λ →+* Λ'` be a surjective morphism of rings with principal kernel and `Ψ` the derived
extensions of scalars along `φ`, with the shift structures inherited, as left adjoints, from the
restrictions of scalars. This file shows that the comparisons between `Ψ` and the comparison
functors `ν^*`, `Rν_*` commute with the shifts:

- `ProEtale.derivedComparisonAdjunction_unit`: the adjunction `ν^* ⊣ Rν_*` is the derived
  adjunction `Adjunction.mapDerivedCategoryRightDerivedAdjunction`, hence commutes with the
  shifts;
- the commutation `ν^* Ψ ≅ Ψ ν^*` and the base change map `Rν_* Ψ ⟶ Ψ Rν_*`
  (`ProEtale.derivedExtendScalarsComparisonLowerStarMap`) commute with the shifts.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.NatTrans.CommShift

variable {A : Type*} [AddMonoid A]
  {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  [HasShift C A] [HasShift D A] [HasShift E A] [HasShift F A]
  {G : C ⥤ D} {H : E ⥤ F} {L₁ : C ⥤ E} {R₁ : E ⥤ C} {L₂ : D ⥤ F} {R₂ : F ⥤ D}
  [G.CommShift A] [H.CommShift A] [L₁.CommShift A] [R₁.CommShift A] [L₂.CommShift A]
  [R₂.CommShift A]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) [adj₁.CommShift A] [adj₂.CommShift A]

/-- The inverse mate of a natural transformation commuting with shifts, with respect to
adjunctions commuting with shifts, commutes with shifts. -/
lemma mateEquiv_symm (β : TwoSquare R₁ H G R₂) [NatTrans.CommShift β.natTrans A] :
    NatTrans.CommShift ((CategoryTheory.mateEquiv adj₁ adj₂).symm β).natTrans A := by
  dsimp only [CategoryTheory.mateEquiv, Equiv.coe_fn_symm_mk, TwoSquare.mk, TwoSquare.natTrans]
  infer_instance

end CategoryTheory.NatTrans.CommShift

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The small étale site of a scheme is essentially small. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

section Comparison

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})

/-- The unit of the adjunction `ν^* ⊣ Rν_*` is the one of the derived adjunction
`Adjunction.mapDerivedCategoryRightDerivedAdjunction` of `ν^* ⊣ ν_*`. -/
lemma derivedComparisonAdjunction_unit :
    (derivedComparisonAdjunction A X).unit =
      (comparisonAdjunction A X).mapDerivedCategoryRightDerivedAdjunction.unit := by
  refine Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) (fun Y ↦ ?_)
  rw [← cancel_mono ((R(ν_*(X)[A])).map ((ν^*(X)[A]).mapDerivedCategoryFactorsh.hom.app Y))]
  have h₁ := (comparisonAdjunction A X).derivedAdjunction_unit_app_Qh_fac Y
  have h₂ := ((comparisonAdjunction A X).mapHomotopyCategory (ComplexShape.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) (ν^*(X)[A]).mapDerivedCategoryFactorsh.hom
    (ν_*(X)[A]).rightDerivedFunctorUnit Y
  have h₃ := NatTrans.congr_app (ν^*(X)[A]).leftDerivedFunctorIsoMapDerivedCategory_hom_fac Y
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  simp only [derivedComparisonAdjunction, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Category.assoc]
  erw [← Functor.map_comp, h₃, h₁]
  exact h₂.symm

/-- The adjunction `ν^* ⊣ Rν_*` commutes with the shifts. -/
instance commShift_derivedComparisonAdjunction : (derivedComparisonAdjunction A X).CommShift ℤ :=
  Adjunction.CommShift.mk' _ ℤ (by rw [derivedComparisonAdjunction_unit]; infer_instance)

end Comparison

section ExtendScalars

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'}
  (hφ : Function.Surjective φ) {a : Λ} (ha : RingHom.ker φ = Ideal.span {a}) (X : Scheme.{u})

/-- The derived extension of scalars of pro-étale sheaves commutes with the shifts: the structure
inherited, as a left adjoint, from the one of the derived restriction of scalars. -/
noncomputable instance : (ProEtale.derivedExtendScalars hφ ha X).CommShift ℤ :=
  (ProEtale.derivedExtendScalarsAdjunction hφ ha X).leftAdjointCommShift ℤ

/-- The adjunction `Ψ ⊣ Res` on pro-étale sheaves is compatible with the shifts. -/
instance : (ProEtale.derivedExtendScalarsAdjunction hφ ha X).CommShift ℤ :=
  (ProEtale.derivedExtendScalarsAdjunction hφ ha X).commShift_of_rightAdjoint ℤ

instance commShift_derivedRestrictScalarsCompComparisonUpperStarIso_hom :
    NatTrans.CommShift (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom ℤ := by
  dsimp only [derivedRestrictScalarsCompComparisonUpperStarIso,
    Functor.mapDerivedCategorySquareIso]
  infer_instance

variable [IsNoetherianRing Λ]

/-- The commutation `ν^* Ψ ≅ Ψ ν^*` commutes with the shifts: it is the mate of the commutation
of `Res` with `ν^*` (`comparisonUpperStarDerivedExtendScalarsIso_hom_eq`). -/
instance commShift_comparisonUpperStarDerivedExtendScalarsIso_hom :
    NatTrans.CommShift (comparisonUpperStarDerivedExtendScalarsIso hφ ha X).hom ℤ := by
  rw [comparisonUpperStarDerivedExtendScalarsIso_hom_eq]
  exact NatTrans.CommShift.mateEquiv_symm _ _ _

/-- The base change map `Rν_* L ⊗ᴸ_Λ Λ' ⟶ Rν_*(L ⊗ᴸ_Λ Λ')` commutes with the shifts. -/
instance commShift_derivedExtendScalarsComparisonLowerStarMap :
    NatTrans.CommShift (derivedExtendScalarsComparisonLowerStarMap hφ ha X) ℤ :=
  NatTrans.CommShift.mateEquiv _ _ (TwoSquare.mk _ _ _ _
    (comparisonUpperStarDerivedExtendScalarsIso hφ ha X).inv)

end ExtendScalars

end AlgebraicGeometry.ProEtale
