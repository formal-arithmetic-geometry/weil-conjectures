/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.ConstantRingModuleSheaves
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.Ring.Adjunctions
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.AffineLocallyConstructibleProEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import WeilConjectures.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
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
import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsSupplement
import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
import WeilConjectures.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.ModuleInverseImageUnitComparison
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.FiniteComparisonModelRealization

/-! # Ordinary realization of coefficient-sized constant module sheaves

Source: Stacks Project, Tags 03CY and 09AL; coefficient transport in the opening
paragraph of the finite comparison proof
(blueprint: lem-ctf-finite-comparison-model-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

section ConstantScalars
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type u) [CommRing A]

private instance commRingForgetSheafification :
    J.PreservesSheafification (forget₂ CommRingCat.{u} RingCat.{u}) where
  le := by
    intro P Q f hf
    let : Presheaf.IsLocallyInjective J f := hf.isLocallyInjective
    let : Presheaf.IsLocallySurjective J f := hf.isLocallySurjective
    let : Presheaf.IsLocallyInjective J (Functor.whiskerRight f
        (forget₂ CommRingCat.{u} RingCat.{u})) :=
      ⟨fun x y h ↦ Presheaf.equalizerSieve_mem J f x y h⟩
    let : Presheaf.IsLocallySurjective J (Functor.whiskerRight f
        (forget₂ CommRingCat.{u} RingCat.{u})) :=
      ⟨fun x ↦ Presheaf.imageSieve_mem J f x⟩
    exact J.W_of_isLocallyBijective (Functor.whiskerRight f
      (forget₂ CommRingCat.{u} RingCat.{u}))

private def coefficientRingIso : SheafOfModules.constantCoefficientRing J A ≅
    (constantSheaf J RingCat.{u}).obj (RingCat.of A) :=
  (constantCommuteCompose J (forget₂ CommRingCat.{u} RingCat.{u})).app (CommRingCat.of A)

private def ringRestriction : ConstantCompletion.Mod (ConstantCompletion.constant J A) ⥤
    SheafOfModules.{u} ((constantSheaf J RingCat.{u}).obj (RingCat.of A)) :=
  SheafOfModules.restrictScalars (coefficientRingIso J A).inv

private theorem ringRestriction_equivalence : (ringRestriction J A).IsEquivalence := by
  let eC : C ≌ C := Equivalence.refl
  let : eC.functor.IsContinuous J J := inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let : eC.inverse.IsContinuous J J := inferInstanceAs (Functor.IsContinuous (𝟭 C) J J)
  let c := (coefficientRingIso J A).symm
  let e := SheafOfModules.pushforwardPushforwardEquivalence.{u}
    (J := J) (K := J) eC c.hom c.inv
    (by
      ext U x
      dsimp [eC, Equivalence.refl]
      simp only [Functor.map_id]
      exact congrArg (fun f ↦ f.hom.app U x) c.inv_hom_id.symm)
    (by
      ext U x
      dsimp [eC, Equivalence.refl]
      simp only [Functor.map_id]
      exact congrArg (fun f ↦ f.hom.app U x) c.hom_inv_id)
  exact e.isEquivalence_functor

private theorem coefficientRingIso_unit :
    SheafOfModules.constantCoefficientUnit J A ≫ (coefficientRingIso J A).hom.hom =
      toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A)) := by
  change SheafOfModules.constantCoefficientUnit J A ≫
    ((constantCommuteCompose J (forget₂ CommRingCat.{u} RingCat.{u})).hom.app
      (CommRingCat.of A)).hom = _
  rw [constantCommuteCompose_hom_app_hom]
  unfold SheafOfModules.constantCoefficientUnit
  rw [← Category.assoc, sheafComposeIso_inv_fac]
  exact (toSheafify_naturality J
    (Functor.constComp Cᵒᵖ (CommRingCat.of A)
      (forget₂ CommRingCat.{u} RingCat.{u})).hom).symm.trans
      (by rfl)

private theorem restriction_smul (M : ConstantCompletion.Mod (ConstantCompletion.constant J A))
    (V : Cᵒᵖ) (a : A) (x : M.val.obj V) :
    a • (show ((ringRestriction J A ⋙ constantRingModuleRestriction J A).obj M).obj.obj V
      from x) =
    a • (show ((coefficientModelFixedScalars J A).obj M).obj.obj V from x) := by
  have h := congrArg (fun f ↦ f.app V a) (coefficientRingIso_unit J A)
  have hi := congrArg (fun f ↦ f.hom.app V) (coefficientRingIso J A).hom_inv_id
  change (coefficientRingIso J A).inv.hom.app V
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of A))).app V a) • x =
      (SheafOfModules.constantCoefficientUnit J A).app V a • x
  erw [← h]
  exact congrArg (fun b ↦ b • x) (ConcreteCategory.congr_hom hi _)

private def restrictionIso :
    ringRestriction J A ⋙ constantRingModuleRestriction J A ≅ coefficientModelFixedScalars J A := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun V ↦ ?_) ?_)) ?_
  · exact ModuleCat.isoMk (Iso.refl _) (fun a ↦ by
      ext x
      exact (restriction_smul J A M V a x).symm)
  · intro V W f
    ext x
    rfl
  · intro M N f
    ext V x
    rfl

end ConstantScalars
end CategoryTheory

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]

private theorem modelComparisonRingMap_unit :
    SheafOfModules.constantCoefficientUnit
        (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A ≫
      (constructibleComparisonRingMap.{u, u + 1} X A).hom =
    Functor.whiskerLeft (Scheme.smallModelComparisonInclusion.{u, u + 1} X).op
      (SheafOfModules.constantCoefficientUnit
        (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A) := by
  let J := Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, u + 1} X
  let F := Scheme.smallModelComparisonInclusion.{u, u + 1} X
  let φ := Functor.whiskerLeft F.op
    (toSheafify K ((Functor.const _).obj (CommRingCat.of A)))
  have h := ((sheafificationAdjunction J CommRingCat.{u + 1}).homEquiv
    ((Functor.const _).obj (CommRingCat.of A))
    ((F.sheafPushforwardContinuous CommRingCat.{u + 1} J K).obj
      (ConstantCompletion.constant K A))).apply_symm_apply φ
  exact congrArg (fun f ↦ Functor.whiskerRight f
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) h

private def modelPushforwardSquare :
    SheafOfModules.pushforward (constructibleComparisonRingMap.{u, u + 1} X A) ⋙
        finiteComparisonEtaleModelRealization X A ≅
      finiteComparisonProEtaleModelRealization X A ⋙
        comparisonLowerStar (ModuleCat.{u + 1} A) X := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun V ↦ ?_) ?_)) ?_
  · refine ModuleCat.isoMk (Iso.refl _) (fun a ↦ ?_)
    ext x
    have h := congrArg (fun f ↦ f.app (Opposite.op (AsSmall.up.obj V.unop)) a)
      (modelComparisonRingMap_unit X A)
    change a • (show ((finiteComparisonProEtaleModelRealization X A).obj M).obj.obj
        ((Scheme.toProEt X).op.obj V) from x) =
      a • (show ((finiteComparisonEtaleModelRealization X A).obj
        ((SheafOfModules.pushforward (constructibleComparisonRingMap.{u, u + 1} X A)).obj
          M)).obj.obj V from x)
    exact congrArg (fun b ↦ b • (show M.val.obj
      ((Scheme.smallModelComparisonInclusion.{u, u + 1} X).op.obj
        (Opposite.op (AsSmall.up.obj V.unop))) from x)) h.symm
  · intro U V f
    ext x
    rfl
  · intro M N f
    ext V x
    rfl

/-- The comparison square persists for any localization of the specified termwise
model inverse image. Source: Stacks Tag 09AL
(blueprint: lem-ctf-finite-comparison-model-realization).

Proof: the model pullback is exact. Localize the preceding square of exact functors.
The supplied factorization identifies D with the exact-functor localization by the
fully faithful universal property of the localization Q. -/
theorem finiteComparisonModelDerivedSquare :
    letI : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
      HasDerivedCategory.standard _
    letI : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
      HasDerivedCategory.standard _
    ∀ D : ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A) ⥤
          ConstantCompletion.D (ConstantCompletion.constant
            (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A),
      Nonempty (ConstantCompletion.Q _ ⋙ D ≅
        constructibleComparisonComplexPullback.{u, u + 1} X A ⋙ ConstantCompletion.Q _) →
      Nonempty ((finiteComparisonEtaleModelRealization X A).mapDerivedCategory ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ≅
        D ⋙ (finiteComparisonProEtaleModelRealization X A).mapDerivedCategory) := by
  let : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 2} (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, u + 1} X) A)) :=
    HasDerivedCategory.standard _
  intro D ⟨eD⟩
  let L := constructibleComparisonPullback.{u, u + 1} X A
  have : PreservesFiniteLimits L := (constructibleComparisonPullback_exact_faithful X A).1
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  have : PreservesFiniteColimits L := inferInstance
  let Q := ConstantCompletion.Q (ConstantCompletion.constant
    (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)
  let W := HomologicalComplex.quasiIso
    (ConstantCompletion.Mod (ConstantCompletion.constant
      (Scheme.smallModelComparisonEtaleTopology.{u, u + 1} X) A)) (.up ℤ)
  let T := constructibleComparisonComplexPullback.{u, u + 1} X A ⋙ ConstantCompletion.Q _
  let : Localization.Lifting Q W T D := ⟨eD⟩
  let : Localization.Lifting Q W T L.mapDerivedCategory := ⟨L.mapDerivedCategoryFactors⟩
  let e : L.mapDerivedCategory ≅ D :=
    Localization.liftNatIso Q W T T L.mapDerivedCategory D (Iso.refl _)
  obtain ⟨h⟩ := finiteComparisonModelPullbackSquare X A
  exact ⟨Functor.mapDerivedCategorySquareIso h.symm ≪≫
    Functor.isoWhiskerRight e
      (finiteComparisonProEtaleModelRealization X A).mapDerivedCategory⟩

end AlgebraicGeometry.ProEtale
