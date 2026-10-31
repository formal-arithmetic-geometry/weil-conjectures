/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingMappingTower
public import WeilConjectures.SixFunctors.IntegralDualizingResolvedGlobalHom
import WeilConjectures.Algebra.Homology.DerivedInternalHomSectionsModel
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
import Mathlib.Algebra.Category.Grp.Abelian
import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Category.Grp.EpiMono
import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Functor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Ordinary Hom into a K-injective on the constant sequence site

Source: Stacks Project, Tags 0A95, 0A96, 08JA and 0941.
(blueprint: lem-coef-integral-dualizing-sequence-hom-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

attribute [local irreducible] homComplexFunctor

/-- Sequence-site derived Hom into a fixed K-injective is computed by ordinary Hom
and ordinary sequence sections, naturally in every source complex.

Source: Stacks Project, Tags 0A95, 0A96, 08JA and 0941.
(blueprint: lem-coef-integral-dualizing-sequence-hom-comparison).

Proof: the natural internal-Hom representative comparison identifies derived Hom
with the localization of ordinary Hom into the K-injective target. For a K-flat
source this Hom complex is K-injective, so the section comparison unit is invertible.
For an arbitrary source choose a K-flat resolution on the sequence site. Its
precomposition map is a quasi-isomorphism on Hom sheaves and on sections at each
(n, final pro-etale object). Evaluation and the forgetful functor to abelian groups
detect quasi-isomorphisms of module towers. Naturality of the derived-section unit
and cancellation therefore imply its invertibility for the original source. Since
the unit itself is natural, these objectwise assertions give a natural isomorphism.
The argument applies without boundedness assumptions, including zero complexes. -/
theorem integralDualizing_sequence_hom_comparison
    (T : CochainComplex (coefHomConstantModules l E X) ℤ) [T.IsKInjective] :
    Nonempty (DerivedCategory.Q.op ⋙
      (Functor.curry.obj (coefHomConstantInternalHom l E X)).flip.obj
        (DerivedCategory.Q.obj T) ⋙ coefHomConstantDerivedSections l E X ≅
      (homComplexFunctor.{u + 1, u, u + 1, u + 1}
        (R := coefHomConstantRing l E X)).flip.obj T ⋙
        (coefHomConstantSections l E X).mapHomologicalComplex (.up ℤ) ⋙
          DerivedCategory.Q) := by
  classical
  let R := coefHomConstantRing l E X
  let A := coefHomConstantModules l E X
  let : IsGrothendieckAbelian.{u + 1} A := by
    open SheafOfModules in
      exact (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology X)) R).1
  let F := coefHomConstantSections l E X
  let H := (homComplexFunctor (R := R)).flip.obj T
  let ii : (DerivedInternalHomSectionsModel.injectiveProperty.{u + 1, u, u} R).FullSubcategory :=
    ⟨T, (show T.IsKInjective from inferInstance)⟩
  obtain ⟨a₀⟩ :=
    (DerivedInternalHomSectionsModel.derived_internalHom_sections_model.{u + 1, u, u} R).1
  have a : DerivedCategory.Q.op ⋙
      (Functor.curry.obj (coefHomConstantInternalHom l E X)).flip.obj
        (DerivedCategory.Q.obj T) ≅ H ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ a₀.app (P, ii)) (by
      intro P P' f
      have hn := a₀.hom.naturality (show (P, ii) ⟶ (P', ii) from (f, 𝟙 ii))
      simpa [DerivedInternalHomSectionsModel.representedInternalHom,
        DerivedInternalHomSectionsModel.representativeHom, Functor.flip,
        Functor.curry, Functor.curryObj, H, ii, coefHomConstantInternalHom, R] using hn)
  let δ : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    { app := F.rightDerivedFunctorUnitQ
      naturality := fun _ _ f ↦ F.rightDerivedFunctorUnitQ_naturality f }
  let γ := Functor.whiskerLeft H δ
  have hγ : ∀ L, IsIso (γ.app L) := by
    intro L
    obtain ⟨P, p, hP, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients L.unop
    have : QuasiIso p := hp
    have : (homComplex (R := R) P T).IsKInjective :=
      CochainComplex.isKInjective_homComplex_of_isKFlatOfUniverses.{u, u + 1, u} P T hP
    have hf : QuasiIso (H.map p.op) := by
      have hf₀ := quasiIso_homComplex_mapOfUniverses.{u + 1, u, u} (𝟙 T) p
      simpa [H, Functor.flip] using hf₀
    have : QuasiIso (H.map p.op) := hf
    have hFg : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map (H.map p.op)) := by
      apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
      intro n
      let V := forget₂ (ModuleCat.{u + 1} (integralDualizingCoefficients l E))
        AddCommGrpCat.{u + 1}
      let : PreservesColimitsOfSize.{0, 0} V :=
        ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, 0, 0}
          (R := integralDualizingCoefficients l E)
      let : PreservesFiniteColimits V := PreservesColimitsOfSize.preservesFiniteColimits V
      apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ V).mp
      have h := homComplex_sections_quasiIsoOfUniverses.{u + 1, u, u}
        (𝟙 T) p (n.unop, Scheme.ProEt.mk (𝟙 X))
      let R₀ := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
      let Γ := SheafOfModules.forget R₀ ⋙
        PresheafOfModules.evaluation R₀.obj (op (n.unop, Scheme.ProEt.mk (𝟙 X))) ⋙
          forget₂ (ModuleCat.{u + 1}
            (R₀.obj.obj (op (n.unop, Scheme.ProEt.mk (𝟙 X))))) AddCommGrpCat.{u + 1}
      let En := (evaluation ℕᵒᵖ
        (ModuleCat.{u + 1} (integralDualizingCoefficients l E))).obj n
      have ε : (F ⋙ En) ⋙ V ≅ Γ :=
        NatIso.ofComponents (fun N ↦ (AddEquiv.refl _).toAddCommGrpIso)
          (by intro M N f; ext x; rfl)
      have b : (F.mapHomologicalComplex (.up ℤ) ⋙ En.mapHomologicalComplex (.up ℤ)) ⋙
          V.mapHomologicalComplex (.up ℤ) ≅ Γ.mapHomologicalComplex (.up ℤ) :=
        Functor.isoWhiskerRight
          (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ En)) (.up ℤ))
          (V.mapHomologicalComplex (.up ℤ)) ≪≫
        Functor.mapHomologicalComplexCompIso ε (.up ℤ)
      have : QuasiIso ((Γ.mapHomologicalComplex (.up ℤ)).map (H.map p.op)) := by
        simpa [Γ, R₀, H, Functor.flip] using h
      change QuasiIso (((F.mapHomologicalComplex (.up ℤ) ⋙
        En.mapHomologicalComplex (.up ℤ)) ⋙
          V.mapHomologicalComplex (.up ℤ)).map (H.map p.op))
      apply (quasiIso_iff_comp_right _ (b.app (H.obj (op P))).hom).mp
      change QuasiIso (_ ≫ b.hom.app _)
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
      change IsIso (F.rightDerivedFunctorUnitQ (homComplex (R := R) P T))
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
  exact ⟨Functor.isoWhiskerRight a F.rightDerivedFunctor ≪≫ (asIso γ).symm⟩

end WeilConjectures
