/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicOpenUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Monad.Adjunction

/-! # Auxiliary mate calculus for the support scalar mate

Abstract mate lemmas (vertical composition of mates and invertibility of a mate whose
transverse adjunctions have invertible units), together with the derived
extension-by-zero adjunction in intrinsic constant coefficients.
Source: Stacks Tags 03DI and 07A6
(blueprint: new-support-scalar-mate-canonical-open).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare

namespace CategoryTheory

section Abstract

variable {C₁ C₂ C₃ D₁ D₂ D₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  [Category D₁] [Category D₂] [Category D₃]

/-- The inverse mate of a vertical composite of squares between right adjoints is the
horizontal composite of the inverse mates. -/
theorem mateEquiv_symm_vComp
    {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    {L₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)
    {G₁ : C₁ ⥤ C₂} {H₁ : D₁ ⥤ D₂} {G₂ : C₂ ⥤ C₃} {H₂ : D₂ ⥤ D₃}
    (α : TwoSquare R₁ H₁ G₁ R₂) (β : TwoSquare R₂ H₂ G₂ R₃) :
    (mateEquiv adj₁ adj₃).symm (α ≫ᵥ β) =
      (mateEquiv adj₁ adj₂).symm α ≫ₕ (mateEquiv adj₂ adj₃).symm β := by
  rw [Equiv.symm_apply_eq, mateEquiv_vcomp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The inverse mate of an invertible square is invertible, provided that the two
transverse functors on the source side are left adjoints with invertible units, and the
right adjoints of the transverse functors commute with the two right adjoints up to some
natural isomorphism. -/
theorem mateEquiv_symm_isIso_of_unit_isIso
    {LX : C₁ ⥤ D₁} {RX : D₁ ⥤ C₁} {LZ : C₂ ⥤ D₂} {RZ : D₂ ⥤ C₂}
    (aX : LX ⊣ RX) (aZ : LZ ⊣ RZ)
    {EA : C₁ ⥤ C₂} {JA : C₂ ⥤ C₁} {EB : D₁ ⥤ D₂} {JB : D₂ ⥤ D₁}
    (dA : EA ⊣ JA) (dB : EB ⊣ JB) [IsIso dA.unit] [IsIso dB.unit]
    (α : RX ⋙ EA ≅ EB ⋙ RZ) (θ : RZ ⋙ JA ≅ JB ⋙ RX) :
    IsIso ((mateEquiv aX aZ).symm (TwoSquare.mk _ _ _ _ α.hom)).natTrans := by
  let m := (mateEquiv aX aZ).symm (TwoSquare.mk _ _ _ _ α.hom)
  have h := iterated_mateEquiv_conjugateEquiv aX aZ dA dB m
  rw [Equiv.apply_symm_apply] at h
  have hc : IsIso (mateEquiv dB dA (TwoSquare.mk _ _ _ _ α.hom)).natTrans := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro y
    have hJ : IsIso (JB.map (dB.counit.app y)) := by
      have : IsIso (dB.unit.app (JB.obj y) ≫ JB.map (dB.counit.app y)) := by
        rw [dB.right_triangle_components]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_left (dB.unit.app (JB.obj y)) _
    have hJ' : IsIso ((JB ⋙ RX).map (dB.counit.app y)) := by
      rw [Functor.comp_map]
      infer_instance
    have hR : IsIso ((RZ ⋙ JA).map (dB.counit.app y)) :=
      (NatIso.isIso_map_iff θ _).2 hJ'
    rw [Functor.comp_map] at hR
    simp only [mateEquiv_apply, Functor.comp_obj, NatTrans.comp_app, Functor.id_obj,
      Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
      Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id]
    infer_instance
  rw [h] at hc
  exact conjugateEquiv_of_iso (aX.comp dB) (dA.comp aZ) m.natTrans

end Abstract

end CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
  (A : Type u) [CommRing A] [Finite A]

instance sfIntrinsicOpenRestriction_additive :
    (sfIntrinsicOpenRestriction j A).Additive :=
  (sfIntrinsicExtensionByZeroAdjunction j A).right_adjoint_additive

instance sfIntrinsicOpenRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (sfIntrinsicOpenRestriction j A) := by
  have := (sfIntrinsicExtensionByZeroAdjunction j A).rightAdjoint_preservesLimits
  infer_instance

instance sfIntrinsicOpenRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (sfIntrinsicOpenRestriction j A) := by
  let adj : sfIntrinsicOpenRestriction j A ⊣ _ :=
    ((sfIntrinsicModuleEquivalence Z A).symm.toAdjunction.comp
      (ProEtale.openImmersionRestrictionLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).comp
          (sfIntrinsicModuleEquivalence U A).toAdjunction
  have := adj.leftAdjoint_preservesColimits
  infer_instance

instance sfIntrinsicExtensionByZeroAdjunction_unit_isIso :
    IsIso (sfIntrinsicExtensionByZeroAdjunction j A).unit :=
  (NatTrans.isIso_iff_isIso_app _).2 (fun M ↦ sfIntrinsicOpenUnit_isIso j A M)

/-- The derived extension-by-zero adjunction in intrinsic constant coefficients, obtained
by localizing the termwise adjunction on cochain complexes.
Source: Stacks Tag 03DI (blueprint: new-support-scalar-mate-canonical-open). -/
def sfIntrinsicDerivedOpenAdjunction :
    (sfIntrinsicExtensionByZero j A).mapDerivedCategory ⊣
      (sfIntrinsicOpenRestriction j A).mapDerivedCategory :=
  let G := sfIntrinsicExtensionByZero j A
  let F := sfIntrinsicOpenRestriction j A
  let : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  ((sfIntrinsicExtensionByZeroAdjunction j A).mapHomologicalComplex
    (ComplexShape.up ℤ)).localization
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
      G.mapDerivedCategory F.mapDerivedCategory

/-- The derived intrinsic extension by zero has invertible unit.
Source: Stacks Tags 03DI and 09AE (blueprint: new-support-scalar-mate-canonical-open). -/
instance sfIntrinsicDerivedOpenAdjunction_unit_isIso :
    IsIso (sfIntrinsicDerivedOpenAdjunction j A).unit := by
  let G := sfIntrinsicExtensionByZero j A
  let F := sfIntrinsicOpenRestriction j A
  let e : G ⋙ F ≅ 𝟭 _ := (asIso (sfIntrinsicExtensionByZeroAdjunction j A).unit).symm
  let eD : G.mapDerivedCategory ⋙ F.mapDerivedCategory ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso G F).symm ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _
  let ff := (sfIntrinsicDerivedOpenAdjunction j A).fullyFaithfulLOfCompIsoId eD
  have : G.mapDerivedCategory.Full := ff.full
  have : G.mapDerivedCategory.Faithful := ff.faithful
  infer_instance

end AlgebraicGeometry.Scheme
