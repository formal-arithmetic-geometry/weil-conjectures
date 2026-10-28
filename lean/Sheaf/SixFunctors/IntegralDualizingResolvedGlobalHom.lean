/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.SixFunctors.IntegralDualizingRoosModel
public import Sheaf.Algebra.Homology.RingedSiteGlobalRHomModel
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.KInjectiveHomComplexOfUniverses
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import Sheaf.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Integral scalar global Hom on a fixed K-injective target

Source: Stacks 0B6E, 0A95, 0A96 and 08JA. The representative here involves no tower
and no inverse limit. Its first variable is the entire category of complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Integral scalars as actual compatible sections of the completed structure ring.
Source: Stacks 0B6E (blueprint: lem-coef-integral-dualizing-resolved-global-hom). -/
def integralDualizingScalarSections : integralDualizingCoefficients l E →+*
    RingCat.sectionsSubring (completedIntegralCoefficientSheafUnrestricted l E X).obj :=
  (RingHom.pi (integralDualizingScalar l E X)).codRestrict _ (fun a ↦ by
    intro U V f
    let η := Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (integralDualizingCoefficients l E))))
      (forget₂ CommRingCat RingCat) ≫
        (integralConstantToCompletionOfUniverses.{u, u} l E X).hom
    exact (ConcreteCategory.congr_hom (η.naturality f) a).symm)

/-- The signed global Hom complex, retaining the specified integral scalar action.
Source: Stacks 0B6E, 08JA
(blueprint: lem-coef-integral-dualizing-resolved-global-hom). -/
def integralDualizingResolvedHom :
    (CochainComplex (scalarReductionSource l E X) ℤ)ᵒᵖ ⥤
      CochainComplex (scalarReductionSource l E X) ℤ ⥤
        CochainComplex (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) ℤ :=
  homComplexFunctor (R := completedIntegralCommRingSheafUnrestricted l E X) ⋙
    (Functor.whiskeringRight _ _ _).obj
      ((RingedSiteGlobalRHom.sections
        (completedIntegralCommRingSheafUnrestricted l E X)
        (integralDualizingCoefficients l E) (integralDualizingScalarSections l E X))
          |>.mapHomologicalComplex (.up ℤ))

/-- Global Hom before restriction to constructible inputs.
Source: Stacks 0B6E
(blueprint: lem-coef-integral-dualizing-resolved-global-hom). -/
def integralDualizingAmbientGlobalHom (M : DerivedCategory (scalarReductionSource l E X)) :
    (DerivedCategory (scalarReductionSource l E X))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  (Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u}
    (Scheme.ProEt.topology X) (completedIntegralCommRingSheafUnrestricted l E X))).flip.obj M ⋙
      integralDualizingDerivedSections l E X

private def scalarSectionsEquiv
    (N : scalarReductionSource l E X) :
    (RingedSiteGlobalRHom.sections (completedIntegralCommRingSheafUnrestricted l E X)
      (integralDualizingCoefficients l E) (integralDualizingScalarSections l E X)).obj N ≃ₗ[
        integralDualizingCoefficients l E] (integralDualizingSections l E X).obj N where
  toFun f := f.val.app (op (Scheme.ProEt.mk (𝟙 X)))
    (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
      (op (Scheme.ProEt.mk (𝟙 X))))
  invFun x := N.unitHomEquiv.symm (N.val.sectionsMk
    (fun U ↦ N.val.map ((Scheme.ProEt.isTerminalMkId X).op.to U) x)
    (by
      intro U V f
      rw [← PresheafOfModules.map_comp_apply]
      exact N.val.congr_map_apply
        ((Scheme.ProEt.isTerminalMkId X).op.hom_ext _ _) x))
  left_inv f := by
    apply N.unitHomEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro U
    change N.val.map _ (f.val.app _ (1 :
      (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        (op (Scheme.ProEt.mk (𝟙 X))))) = f.val.app U
        (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj U)
    have hf := PresheafOfModules.naturality_apply f.val
      ((Scheme.ProEt.isTerminalMkId X).op.to U)
      (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
        (op (Scheme.ProEt.mk (𝟙 X))))
    change f.val.app U
        ((completedIntegralCoefficientSheafUnrestricted l E X).obj.map
          ((Scheme.ProEt.isTerminalMkId X).op.to U) 1) =
      N.val.map _ (f.val.app _
        (1 : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
          (op (Scheme.ProEt.mk (𝟙 X))))) at hf
    rw [map_one] at hf
    exact hf.symm
  right_inv x := by
    change (N.unitHomEquiv (N.unitHomEquiv.symm _)).val _ = x
    rw [Equiv.apply_symm_apply]
    change N.val.map _ x = x
    have h : (Scheme.ProEt.isTerminalMkId X).op.to
        (op (Scheme.ProEt.mk (𝟙 X))) = 𝟙 _ :=
      (Scheme.ProEt.isTerminalMkId X).op.hom_ext _ _
    rw [h]
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def scalarSectionsIso :
    RingedSiteGlobalRHom.sections (completedIntegralCommRingSheafUnrestricted l E X)
      (integralDualizingCoefficients l E) (integralDualizingScalarSections l E X) ≅
        integralDualizingSections l E X :=
  NatIso.ofComponents (fun N ↦ (scalarSectionsEquiv l E X N).toModuleIso)
    (by intro M N f; ext x; rfl)

attribute [local irreducible] homComplexFunctor

/-- On a fixed K-injective target, global derived Hom is represented by the signed
ordinary global Hom complex, naturally in every source complex.

Source: Stacks 0B6E, 0A95, 0A96 and 08JA; the representative comparison in the first
step of lem-sfb-ringed-site-global-rhom-derived-limits.
(blueprint: lem-coef-integral-dualizing-resolved-global-hom).

Proof: identify compatible sections with sections at the final pro-etale object;
scalar restriction uses precisely integralDualizingScalarSections evaluated there.
The replacement-normalized internal-Hom comparison identifies RHom(QP,QI) with
Q Hom(P,I), naturally in P. For flat-term K-flat P, Hom(P,I) is K-injective, so
ordinary sections compute derived sections. For arbitrary P, take a flat-term
K-flat resolution P' to P. Precomposition is a quasi-isomorphism both on sheaf Hom
and on its ordinary global Hom complex because I is K-injective. Naturality of
the derived-sections unit transfers invertibility from P' to P. Thus the canonical
comparison is a natural isomorphism on all complexes, without a bound on P or I.
The same argument includes the zero complex and the empty scheme. -/
theorem integralDualizing_resolved_globalHom
    (I : CochainComplex (scalarReductionSource l E X) ℤ) [I.IsKInjective] :
    Nonempty (DerivedCategory.Q.op ⋙
      integralDualizingAmbientGlobalHom l E X (DerivedCategory.Q.obj I) ≅
        (integralDualizingResolvedHom l E X).flip.obj I ⋙ DerivedCategory.Q) := by
  classical
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let A := scalarReductionSource l E X
  let : IsGrothendieckAbelian.{u + 1} A :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u+1,u,u}
      (Scheme.ProEt.topology X) R).1
  let F := integralDualizingSections l E X
  let H := (homComplexFunctor (R := R)).flip.obj I
  let ii : (DerivedInternalHomSectionsModel.injectiveProperty.{u + 1, u, u} R).FullSubcategory :=
    ⟨I, (show I.IsKInjective from inferInstance)⟩
  obtain ⟨a₀⟩ :=
    (DerivedInternalHomSectionsModel.derived_internalHom_sections_model.{u + 1, u, u}
      R).1
  let a : DerivedCategory.Q.op ⋙
      (Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u}
        (Scheme.ProEt.topology X) R)).flip.obj (DerivedCategory.Q.obj I) ≅
      H ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ a₀.app (P, ii)) (by
      intro P P' f
      have hn := a₀.hom.naturality (show (P, ii) ⟶ (P', ii) from (f, 𝟙 ii))
      simpa [DerivedInternalHomSectionsModel.representedInternalHom,
        DerivedInternalHomSectionsModel.representativeHom, Functor.flip,
        Functor.curry, Functor.curryObj, H, ii] using hn)
  let δ : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun _ _ f ↦ F.rightDerivedFunctorUnitQ_naturality f }
  let γ := Functor.whiskerLeft H δ
  have hγ : ∀ P, IsIso (γ.app P) := by
    intro L
    obtain ⟨P, p, hP, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients L.unop
    have : QuasiIso p := hp
    have : (homComplex (R := R) P I).IsKInjective :=
      CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses.{u, u + 1, u} P I hP
    have hf : QuasiIso (H.map p.op) := by
      have hf₀ := quasiIso_homComplex_mapOfUniverses.{u + 1, u, u} (𝟙 I) p
      simpa [H, Functor.flip] using hf₀
    have : QuasiIso (H.map p.op) := hf
    have hFg : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (H.map p.op)) := by
      let V := forget₂ (ModuleCat.{u + 1} (integralDualizingCoefficients l E))
        AddCommGrpCat.{u + 1}
      let : PreservesColimitsOfSize.{0, 0} V :=
        ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0}
          (R := integralDualizingCoefficients l E)
      let : PreservesFiniteColimits V := PreservesColimitsOfSize.preservesFiniteColimits V
      apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ V).mp
      have h := homComplex_sections_quasiIsoOfUniverses.{u + 1, u, u}
        (𝟙 I) p (Scheme.ProEt.mk (𝟙 X))
      let R₀ := (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
      let Γ := SheafOfModules.forget R₀ ⋙
        PresheafOfModules.evaluation R₀.obj (op (Scheme.ProEt.mk (𝟙 X))) ⋙
          forget₂ (ModuleCat.{u + 1} (R₀.obj.obj (op (Scheme.ProEt.mk (𝟙 X)))))
            AddCommGrpCat.{u + 1}
      let ε : F ⋙ V ≅ Γ :=
        NatIso.ofComponents (fun N ↦ (AddEquiv.refl _).toAddCommGrpIso)
          (by intro M N f; ext x; rfl)
      let b := Functor.mapHomologicalComplexCompIso ε (.up ℤ)
      have : QuasiIso ((Γ.mapHomologicalComplex (.up ℤ)).map (H.map p.op)) := by
        simpa [Γ, R₀, H, Functor.flip] using h
      change QuasiIso ((F.mapHomologicalComplex (.up ℤ) ⋙
        V.mapHomologicalComplex (.up ℤ)).map (H.map p.op))
      apply (quasiIso_iff_comp_right _
        (b.app (H.obj (op P))).hom).mp
      change QuasiIso ((F.mapHomologicalComplex (.up ℤ) ⋙
        V.mapHomologicalComplex (.up ℤ)).map (H.map p.op) ≫ b.hom.app _)
      rw [b.hom.naturality (H.map p.op)]
      infer_instance
    have : IsIso ((H ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor).map p.op) := by
      change IsIso (F.rightDerivedFunctor.map (DerivedCategory.Q.map (H.map p.op)))
      infer_instance
    have : IsIso ((H ⋙ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).map p.op) := by
      change IsIso (DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map (H.map p.op)))
      infer_instance
    have : IsIso (γ.app (op P)) := by
      change IsIso (F.rightDerivedFunctorUnitQ (homComplex (R := R) P I))
      rw [Functor.rightDerivedFunctorUnitQ_eq]
      infer_instance
    have hn := γ.naturality p.op
    have : IsIso (γ.app L ≫
        (H ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor).map p.op) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((H ⋙ DerivedCategory.Q ⋙ F.rightDerivedFunctor).map p.op)
  have : IsIso γ := (NatTrans.isIso_iff_isIso_app γ).mpr hγ
  let b := NatIso.mapHomologicalComplex (scalarSectionsIso l E X) (.up ℤ)
  let e := Functor.isoWhiskerRight a F.rightDerivedFunctor ≪≫ (asIso γ).symm ≪≫
    Functor.isoWhiskerLeft H (Functor.isoWhiskerRight b.symm DerivedCategory.Q)
  exact ⟨e⟩

end WeilConjectures
