/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.RingTheory.ProEtale.WContractible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.CategoryTheory.Sites.Over

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
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
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.FlatTruncationTower
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.Algebra.Homology.KFlatTelescopeClosure
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TelescopeColimit
import WeilConjectures.Algebra.Homology.TruncationTelescope
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.CategoryTheory.ZetaWeil.PartitionRefinementSheafification
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Mathlib.Topology.ExtremallyDisconnected
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CanonicalModuleEvaluationTensor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.PartitionEvaluationColimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.PartitionFlatSections
public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.WContractibleDisjointCover
public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.ExactBraidedDerivedEvaluation
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.StoneanFiniteDisjointRefinements
/-!
# Derived tensor evaluation on contractible objects

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 4.1(1);
Stacks Project, Tags 0F63, 06YS and 0FPT
(blueprint: lem-zl-contractible-derived-sections-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r t

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite WeilConjectures

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (U : Cᵒᵖ)

/-- The actual section functor with its coefficient action.
Source: HRS Lemma 4.1(1), Stacks 03DA
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
abbrev contractibleModuleEvaluation :
    RingedTensorModules.{c, v, r} J R ⥤ ModuleCat.{max c v r} (R.obj.obj U) :=
  SheafOfModules.evaluation.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U

/-- The type of ordinary total-complex section pairings.
Source: HRS Lemma 4.1(1), Stacks 06YN
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
abbrev ContractibleSectionsPairing :=
  ∀ P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
      ((contractibleModuleEvaluation.{c, v, r} J R U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P ⊗
        ((contractibleModuleEvaluation.{c, v, r} J R U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Q ⟶
        ((contractibleModuleEvaluation.{c, v, r} J R U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((coefficientTotalTensor.{r, c, v} J R).obj (P, Q))

/-- The strong monoidal structure on termwise derived evaluation.
Source: HRS Lemma 4.1(1), Stacks 06YU
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
abbrev ContractibleSectionsMonoidal
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, max c v r} J R)) :=
  @Functor.Monoidal
    (DerivedCategory (RingedTensorModules.{c, v, r} J R)) _ S.monoidal
    (DerivedCategory (ModuleCat.{max c v r} (R.obj.obj U))) _ _
    (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategory

/-- The ordinary comparison of the actual degree-zero coefficient complexes.
Source: HRS Lemma 4.1(1), Stacks 0FPT
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
abbrev ContractibleSectionsUnitComplex :=
  (𝟙_ (CochainComplex (ModuleCat.{max c v r} (R.obj.obj U)) ℤ)) ≅
    ((contractibleModuleEvaluation.{c, v, r} J R U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (ringedTensorUnitComplex.{c, v, r} J R)

/-- The canonical termwise localization, with its fixed unit, is total right derived sections.
Source: HRS Lemma 4.1(1), Stacks 079P
(blueprint: lem-zl-contractible-derived-sections-tensor). -/
def ContractibleSectionsRightDerived : Prop :=
  Functor.IsRightDerivedFunctor
    (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategory
      (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (RingedTensorModules.{c, v, r} J R) (ComplexShape.up ℤ))

private theorem contractibleSectionsRightDerived_of_exact :
    ContractibleSectionsRightDerived.{c, v, r} J R U := by
  exact Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso (RingedTensorModules.{c, v, r} J R) (.up ℤ))
    (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategory
    (contractibleModuleEvaluation.{c, v, r} J R U).mapDerivedCategoryFactorsh

private theorem contractibleSectionsNativeCoherence :
    ∃ S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, max c v r} J R),
      S.monoidal = RingedDerivedNative.monoidal.{c, v, r, max c v r} J R ∧
      ∃ T : CoefficientTensorModels.{r, c, v, max c v r} J R S,
        ∃ β : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
          _ S.monoidal,
        ∃ hc : RingedDerivedTensorCoherence.{c, v, r, max c v r} J R S T β,
          HEq β (RingedDerivedNative.symmetric.{c, v, r, max c v r} J R) ∧
          HEq hc.unitIso (RingedDerivedNative.unitIso.{c, v, r, max c v r} J R) ∧
          (∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
            (hP : P.IsKFlatIndependentCoefficients) (hQ : Q.IsKFlatIndependentCoefficients),
            HEq (T.iso J R S P Q hP hQ)
              (RingedDerivedNative.tensorIso.{c, v, r, max c v r} J R P Q (Or.inl hP))) := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    obtain ⟨⟨m, adj, ev⟩, hm, T, hT⟩ :=
      RingedDerivedNative.closedAdjunction.{c, v, r, max c v r} J R
    dsimp only [CoefficientClosedStructure.monoidal] at hm
    subst m
    let S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, max c v r} J R) :=
      ⟨RingedDerivedNative.monoidal.{c, v, r, max c v r} J R, adj, ev⟩
    let : MonoidalCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R)) :=
      RingedDerivedNative.monoidal.{c, v, r, max c v r} J R
    let : SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R)) :=
      RingedDerivedNative.symmetric.{c, v, r, max c v r} J R
    let : (DerivedCategory.Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ ⥤
        DerivedCategory (RingedTensorModules.{c, v, r} J R)).LaxMonoidal :=
      RingedDerivedNative.lax.{c, v, r, max c v r} J R
    have ht : T.comparison = RingedDerivedNative.comparison.{c, v, r, max c v r} J R :=
      eq_of_heq hT
    have htensor : ∀ P Q hP hQ,
        T.iso J R S P Q hP hQ =
          RingedDerivedNative.tensorIso.{c, v, r, max c v r} J R P Q (Or.inl hP) := by
      intro P Q hP hQ
      unfold CoefficientTensorModels.iso
      rw [ht]
      exact RingedDerivedNative.comparison_app.{c, v, r, max c v r} J R ⟨P, hP⟩ ⟨Q, hQ⟩
    have hc := RingedDerivedNative.complexConstraints.{c, v, r} J R
    refine ⟨S, rfl, T, RingedDerivedNative.symmetric.{c, v, r, max c v r} J R, {
      tensorIso := RingedDerivedNative.tensorIso.{c, v, r, max c v r} J R
      tensorIso_both := ?_
      tensorIso_naturality := RingedDerivedNative.tensorIso_naturality.{c, v, r, max c v r} J R
      unitIso := RingedDerivedNative.unitIso.{c, v, r, max c v r} J R
      symmetry_model := ?_
      associator_model := ?_
      leftUnitor_model := ?_
      rightUnitor_model := ?_ }, HEq.rfl, HEq.rfl, (fun P Q hP hQ ↦ heq_of_eq (htensor P Q hP hQ))⟩
    · intro P Q hP hQ
      exact (htensor P Q hP hQ).symm
    · intro P Q hP hQ
      refine ⟨β_ P Q, hc.symmetry P Q, ?_⟩
      rw [htensor P Q hP hQ, htensor Q P hQ hP]
      exact RingedDerivedNative.symmetry_square.{c, v, r, max c v r} J R P Q hP hQ
    · intro P Q N hP hQ hN
      refine ⟨MonoidalCategory.associator P Q N, hc.associator P Q N, ?_⟩
      rw [htensor P Q hP hQ, htensor Q N hQ hN]
      exact RingedDerivedNative.associator_square.{c, v, r, max c v r} J R P Q N hP hQ hN
    · intro P hP
      refine ⟨MonoidalCategory.leftUnitor P, ?_, ?_⟩
      · exact hc.leftUnitor P
      · exact RingedDerivedNative.leftUnitor_square.{c, v, r, max c v r} J R P hP
    · intro P hP
      refine ⟨MonoidalCategory.rightUnitor P, ?_, ?_⟩
      · exact hc.rightUnitor P
      · exact RingedDerivedNative.rightUnitor_square.{c, v, r, max c v r} J R P hP

variable [HasDerivedCategory.{max c v r} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{max c v r} (ModuleCat.{max c v r} (R.obj.obj U))]

variable
  [hlim : PreservesFiniteLimits (contractibleModuleEvaluation.{c, v, r} J R U)]
  [hfin : PreservesFiniteColimits (contractibleModuleEvaluation.{c, v, r} J R U)]

end CategoryTheory

namespace AlgebraicGeometry

end AlgebraicGeometry
