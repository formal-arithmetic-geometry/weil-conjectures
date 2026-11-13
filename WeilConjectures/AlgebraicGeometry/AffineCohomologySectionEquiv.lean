/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.AffineResolutionSectionBijective
import WeilConjectures.AlgebraicGeometry.ResolutionSectionScalarMap

/-! # Affine cohomology and higher-image sections

## References

* Stacks Project, Tags 01F4, 01XJ, 01E4 and 03FD
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 500000 in
-- The explicit derived section comparisons require substantial elaboration.
/-- The affine Leray comparison, normalized by any augmentation-preserving restricted
resolution. This comparison is formed before any base change or scalar extension
(Stacks, Tags 01F4, 01XJ, 01E4 and 03FD). -/
theorem exists_affine_cohomology_section_equiv
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (I : InjectiveResolution F)
    (p : ℕ) (V : S.Opens) (hV : IsAffineOpen V)
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ V))
    (E : ∀ M : (f ⁻¹ᵁ V).toScheme.Modules,
      ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj M) ≃+ H M p)
    (hE : ∀ (M M' : (f ⁻¹ᵁ V).toScheme.Modules) (φ : M ⟶ M')
      (x : (RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj M),
      E M' (((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).map φ).hom x) =
        H.map φ p (E M x)) :
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let N := (pullback (f ⁻¹ᵁ V).ι).obj F
    let P := ((pushforward f).rightDerived p).obj F
    let eH : ((RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p).obj
        ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) ≃+ HOver h N p :=
      (E ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).trans
        (H.mapLinearEquiv ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F) p).toAddEquiv
    ∃ e : HOver h N p ≃ₗ[Γ(S, V)] Γ(P, V),
      ∀ xi : HOver h N p,
        e xi = (resolutionSectionClass R.resolution
          (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
          V R.sections p ≫ Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V)
            (eH.symm xi) := by
  classical
  intro h N P eH
  let c := resolutionSectionClass R.resolution
    (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    V R.sections p ≫ Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V
  let l : HOver h N p →ₗ[Γ(S, V)] Γ(P, V) :=
    { toFun := fun xi ↦ c (eH.symm xi)
      map_add' := fun x y ↦ by
        rw [map_add, map_add]
      map_smul' := fun a xi ↦ by
        let M := (restrictFunctor (f ⁻¹ᵁ V).ι).obj F
        let C := RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p
        let b := ((Scheme.ΓSpecIso Γ(S, V)).inv ≫ h.appTop).hom a
        let e := H.mapLinearEquiv ((restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app F) p
        have he (x : C.obj M) : eH ((C.map (M.smulHom b)).hom x) = a • eH x := by
          exact (congrArg e (hE M M (M.smulHom b) x)).trans (e.map_smul b (E M x))
        have hi : eH.symm (a • xi) = (C.map (M.smulHom b)).hom (eH.symm xi) := by
          apply eH.injective
          rw [AddEquiv.apply_symm_apply, he, AddEquiv.apply_symm_apply]
        change c (eH.symm (a • xi)) = a • c (eH.symm xi)
        rw [hi]
        exact resolutionSectionClass_map_smulHom f F I p V R a (eH.symm xi) }
  have hc : Function.Bijective c :=
    affine_resolutionSectionClass_bijective f F I p V hV R
  have hl : Function.Bijective l := hc.comp eH.symm.bijective
  exact ⟨LinearEquiv.ofBijective l hl, fun _ ↦ rfl⟩

end AlgebraicGeometry.Scheme.Modules
