/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarStages
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionNormalizationScalarMate
import all WeilConjectures.AlgebraicGeometry.Adic.ReductionDerivedChangeCoherence
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement

/-! # Derived scalar extension along the identity, on complexes

For the identity endomorphism `ψ = 𝟙 R` of a ring sheaf on the pro-étale site, the identity
comparison `pbcDerivedExtendIdIso`, conjugate to the identity restriction, is computed on every
cochain complex by the multiplication map `a ⊗ x ↦ a • x` read through the universal counit.

## References

* Stacks Project, Tags 06YY and 03DA
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}


private theorem conjugateIso_symm_eq_leftAdjointUniq {C : Type*} [Category C] {F G : C ⥤ C}
    (adj : F ⊣ G) (δ : G ≅ 𝟭 C) :
    ((conjugateIsoEquiv adj Adjunction.id).symm δ).symm =
      (adj.ofNatIsoRight δ).leftAdjointUniq Adjunction.id := by
  ext K
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app, Adjunction.ofNatIsoRight,
    conjugateIsoEquiv]

/-- Derived scalar extension along a ring endomorphism equal to the identity: the ordinary
multiplication unitor, the identity restriction, and the computation of the conjugate derived
unitor on every cochain complex through the universal counit. -/
theorem pbcDerivedExtendIdIso_hom_app_Q (ψ : R ⟶ R) (hψ : ψ = 𝟙 R) :
    ∃ (o : pbcExtend ψ ≅ 𝟭 _) (e : pbcRestrict ψ ≅ 𝟭 _),
      (∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
        (e.hom.app M).val.app U x = x) ∧
      (∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (a : R.obj.obj U) (m : M.val.obj U),
        (o.hom.app M).val.app U (pbcTensorSection ψ M U a m) = a • m) ∧
      ∀ P : CochainComplex (pbcModules X R) ℤ,
        (pbcDerivedExtendIdIso ψ e).hom.app (DerivedCategory.Q.obj P) =
          pbcComplexCounit ψ P ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app P) := by
  subst hψ
  let e : pbcRestrict (𝟙 R) ≅ 𝟭 _ :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ ModuleCat.restrictScalarsId'App _ rfl (M.val.obj U))
        (fun {U V} f ↦ by ext x; rfl))) (fun f ↦ by ext U x; rfl)
  have he (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
      (e.hom.app M).val.app U x = x := rfl
  let o : pbcExtend (𝟙 R) ≅ 𝟭 _ :=
    NatIso.ofComponents (fun M ↦ ⟨changeIdCounit M, changeIdUnit M, changeIdUnit_counit M,
      changeIdCounit_unit M⟩) (fun f ↦ changeIdCounit_naturality f)
  refine ⟨o, e, he, fun M U a m ↦ changeIdCounit_apply M U a m, fun P ↦ ?_⟩
  let a := (pbcScalarAdjunction (𝟙 R)).mapHomologicalComplex (.up ℤ)
  let η := NatIso.mapHomologicalComplex e (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (pbcModules X R) (.up ℤ)
  let δ := Functor.exactDerivedRestrictionUnit (pbcRestrict (𝟙 R)) e
  have hν (Q : CochainComplex (pbcModules X R) ℤ) :
      a.homEquiv _ _ ((NatIso.mapHomologicalComplex o (.up ℤ)).hom.app Q) ≫ η.hom.app Q =
        Adjunction.id.unit.app Q := by
    rw [Adjunction.homEquiv_unit]
    apply HomologicalComplex.hom_ext
    intro i
    ext U x
    change (changeIdCounit (Q.X i)).val.app U
      (((pbcScalarAdjunction (𝟙 R)).unit.app (Q.X i)).val.app U x) = x
    have hu : ((pbcScalarAdjunction (𝟙 R)).unit.app (Q.X i)).val.app U x =
        pbcTensorSection (𝟙 R) (Q.X i) U 1 x :=
      (pbcScalarAdjunction_exists (𝟙 R)).exists.choose_spec (Q.X i) U x
    erw [hu]
    exact (changeIdCounit_apply (Q.X i) U 1 x).trans (one_smul _ x)
  have h := normalizedAdjunction_uniqueness (QA := DerivedCategory.Q)
    (QB := DerivedCategory.Q) a Adjunction.id (pbcDerivedScalarAdjunction (𝟙 R))
    Adjunction.id (pbcComplexCounit (𝟙 R)) (fun _ ↦ 𝟙 _)
    (pbcRestrict (𝟙 R)).mapDerivedCategoryFactors.inv.app (fun _ ↦ 𝟙 _)
    (canonicalTranspose X (𝟙 R))
    (by
      intro P K f
      simp only [Category.id_comp, Category.comp_id]
      rfl)
    η δ (fun Q ↦ (NatIso.mapHomologicalComplex o (.up ℤ)).hom.app Q) hν
    (fun K ↦ by
      simpa only [Category.comp_id] using
        Functor.exactDerivedRestrictionUnit_inv_factors (pbcRestrict (𝟙 R)) e K) P
  rw [Category.comp_id] at h
  rw [← h, pbcDerivedExtendIdIso, conjugateIso_symm_eq_leftAdjointUniq]
  rfl

end AlgebraicGeometry.Scheme
