/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.AffineResolutionSectionBijective
import Sheaf.AlgebraicGeometry.ResolutionSectionScalarMap

/-! # Affine cohomology and higher-image sections

Source: Stacks Project, Tags 01F4, 01XJ, 01E4 and 03FD.
(blueprint: new-affine-cohomology-section-equiv)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
-- The explicit derived section comparisons require substantial elaboration.
/-- The affine Leray comparison, normalized by any augmentation-preserving restricted
resolution. This comparison is formed before any base change or scalar extension.
Source: Stacks Project, Tags 01F4 (2), 01XJ (1), 01E4 and 03FD.
(blueprint: new-affine-cohomology-section-equiv)

Proof: Put U = f inverse V. The canonical isomorphism restrictFunctorIsoPullback
identifies F restricted to U with N, preserving the restriction adjunction unit.
Transport the supplied natural module/Ext cohomology comparison E through this
isomorphism to form the displayed eH. The naturality hypothesis hE, applied to
multiplication by sections, makes eH linear for A = Gamma(S,V), acting through h.
Thus even a different natural choice of E gives a linear change of coordinates.
Restrict f to U -> V. Higher images commute with open restriction. They are
quasi-coherent by 01XJ, so their positive cohomology on affine V vanishes. The
cocycle-defined Leray edge of 01F4 is consequently an isomorphism. Its naturality
for multiplication makes it A-linear. Identify its values with sections on V of
R^p f_* F by open-restriction comparison. The common section complex computes
both sides: its homology projection followed by the sheafification unit is
sectionCohomologyTheta, by 01E4. The augmentation and components equations of R
identify this computation with resolutionSectionClass for the chosen R; an
augmentation-preserving change of resolution induces the same derived comparison.
Compose this edge with eH inverse to obtain e and the displayed equality.
For p = 0 this is the augmentation comparison. Empty V and zero coefficients
give zero groups throughout, so the same comparison and formula remain valid. -/
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
