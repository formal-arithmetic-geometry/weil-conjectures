/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCoefficientSystemAdjoint
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CoefficientSystemDerivedComparison
public import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetract
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetractData
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.CategoryTheory.GrothendieckDerivedCompactLocalizationModel
public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.GrothendieckDerivedGabrielPopescuPresentation
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Equivalence
public import WeilConjectures.CategoryTheory.GabrielPopescuAbelianCore
public import WeilConjectures.CategoryTheory.GabrielPopescuLargeHomRightAdjoint
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import WeilConjectures.CategoryTheory.DerivedLargeCoproductsTransfer
public import WeilConjectures.CategoryTheory.DerivedHomologyInjective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveSurjective
public import Mathlib.Algebra.Homology.SingleHomology
public import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.LargeHomSolutionSet
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.CategoryTheory.CompactDerivedSourceCore
public import WeilConjectures.CategoryTheory.DerivedModuleCompactGeneration
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneProperties
public import Mathlib.Algebra.Module.ULift
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompact
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactInjective
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactSurjective
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneGenerator
public import WeilConjectures.CategoryTheory.DerivedModuleRankOneNonzeroMap
public import WeilConjectures.CategoryTheory.DerivedModuleNonzeroClassMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
public import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.GrothendieckDerivedExactLocalization
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
public import WeilConjectures.CategoryTheory.CountableCoproductsIdempotentComplete
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportConstruction
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportScalarAction
import WeilConjectures.AlgebraicGeometry.EtaleCoefficientProperCoproducts
import all WeilConjectures.CategoryTheory.ExactDerivedAdjunctionBounds
import all WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.CoefficientEvaluationModels
import all WeilConjectures.AlgebraicGeometry.CoefficientSystemDerivedComparison
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
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
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.SystemGrothendieck
import WeilConjectures.CategoryTheory.SystemCoproducts
import WeilConjectures.CategoryTheory.DerivedCategory.ExactFunctorCoproducts
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Brown adjunction for ordinary étale compact-support towers

Source: Stacks Project, Tag 0F5Y, proposition-brown; Zheng, Construction 4.1.
(blueprint: lem-pur-etale-tower-brown-adjunction).

The existing strict-system and compact-support definitions are reused. The base is
an arbitrary field of positive characteristic. A natural-number index `n` means
positive coefficient exponent `n + 1`. All coproducts use the sheaf universe.

## Main definitions and statement

* `EtaleTowerBrownSiteProperties`: Grothendieck systems and derived sums/evaluations.
* `etaleTowerBrownRestriction`: the composite canonical restriction comparison.
* `EtaleTowerBrownAdjunction`: the exact ordinary adjunction and its linearity.
* `etaleTowerBrownAdjunction`: existence over the stated characteristic-p field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleLevelDerived strictEtaleSystemDerived

/-- The Grothendieck, termwise-sum and conservative-evaluation assertions at one site.
`Q` preserving coproducts says that termwise sums of complexes represent derived sums.
Source: Zheng, Construction 4.1; Stacks 07D9 and 0F5Y
(blueprint: lem-pur-etale-tower-brown-adjunction). -/
def EtaleTowerBrownSiteProperties (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t : O) (P : StrictEtaleEvaluation T O t) : Prop :=
  IsGrothendieckAbelian.{u + 1} (strictEtaleCoefficientSystem T O t) ∧
  HasCoproducts.{u + 1} (strictEtaleCoefficientSystem T O t) ∧
  HasCoproducts.{u + 1} (DerivedCategory (strictEtaleCoefficientSystem T O t)) ∧
  (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
    (DerivedCategory.Q (C := strictEtaleCoefficientSystem T O t))) ∧
  (∀ (n : ℕ) (I : Type (u + 1)),
    PreservesColimitsOfShape (Discrete I) (P.evaluation n)) ∧
  (∀ {K L : DerivedCategory (strictEtaleCoefficientSystem T O t)} (a : K ⟶ L),
    IsIso a ↔ ∀ n : ℕ, IsIso ((P.evaluation n).map a))

/-- The canonical restriction comparison of compact support, composed from open
extension and proper direct image. The latter comparison is the recorded derived mate.
Source: Zheng, Construction 4.1; Stacks 03S2
(blueprint: lem-pur-etale-tower-brown-adjunction). -/
def etaleTowerBrownRestriction {O : Type (u + 1)} [CommRing O] {t : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O t c)
    (a : ∀ {m n : ℕ} (h : n ≤ m),
      (S.PX.scalar h).restriction ⋙ S.levelDerivedOpen m ≅
        S.levelDerivedOpen n ⋙ (S.PZ.scalar h).restriction)
    {m n : ℕ} (h : n ≤ m) :
    (S.PX.scalar h).restriction ⋙ S.levelFunctor m ≅
      S.levelFunctor n ⋙ (S.PY.scalar h).restriction :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (a h) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (S.properDerived.restrictedDirect h) ≪≫
    (Functor.associator _ _ _).symm

/-- Ordinary Brown adjunction data with canonical evaluation and scalar normalization.
The open restriction comparison is fixed by its inverse-image mate. Scalar actions
are the recorded multiplication on quotient sheaves and its localization on complexes.
Source: Stacks 0F5Y and 0A8D; Zheng, Construction 4.1
(blueprint: lem-pur-etale-tower-brown-adjunction). -/
structure EtaleTowerBrownAdjunction {O : Type (u + 1)} [CommRing O] {t : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O t c) where
  siteX : EtaleTowerBrownSiteProperties X O t S.PX
  siteZ : EtaleTowerBrownSiteProperties c.Z O t S.PZ
  siteY : EtaleTowerBrownSiteProperties Y O t S.PY
  openRestriction : ∀ {m n : ℕ} (h : n ≤ m),
    (S.PX.scalar h).restriction ⋙ S.levelDerivedOpen m ≅
      S.levelDerivedOpen n ⋙ (S.PZ.scalar h).restriction
  openRestrictionMate : ∀ {m n : ℕ} (h : n ≤ m),
    (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
      (.mk _ _ _ _ (openRestriction h).hom)).natTrans =
      (S.openDerived.restrictedInverse h).inv
  transition : ∀ {m n : ℕ} (h : n ≤ m)
      (K : DerivedCategory (strictEtaleCoefficientSystem X O t)),
    (S.PY.transition h).app (S.functor.obj K) ≫
      (S.PY.scalar h).restriction.map ((S.evaluation n).hom.app K) =
    (S.evaluation m).hom.app K ≫
      (S.levelFunctor m).map ((S.PX.transition h).app K) ≫
      (etaleTowerBrownRestriction S openRestriction h).hom.app ((S.PX.evaluation n).obj K)
  [leftAdditive : S.functor.Additive]
  [leftShift : S.functor.CommShift ℤ]
  leftExact : S.functor.IsTriangulated
  coproducts : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) S.functor
  scalarX : StrictEtaleScalarAction X O t
  scalarY : StrictEtaleScalarAction Y O t
  leftLinear : ∀ r K,
    S.functor.map ((scalarX.derived r).app K) =
      (scalarY.derived r).app (S.functor.obj K)
  right : DerivedCategory (strictEtaleCoefficientSystem Y O t) ⥤
    DerivedCategory (strictEtaleCoefficientSystem X O t)
  adjunction : S.functor ⊣ right
  [rightAdditive : right.Additive]
  [rightShift : right.CommShift ℤ]
  rightExact : right.IsTriangulated
  rightLinear : ∀ r L,
    right.map ((scalarY.derived r).app L) = (scalarX.derived r).app (right.obj L)
  scalarTranspose : ∀ r L,
    adjunction.homEquiv (right.obj L) L
      ((scalarY.derived r).app (S.functor.obj (right.obj L)) ≫
        adjunction.counit.app L) = (scalarX.derived r).app (right.obj L)
  homLinear : ∀ r K L (a : S.functor.obj K ⟶ L),
    adjunction.homEquiv K L ((scalarY.derived r).app (S.functor.obj K) ≫ a) =
      (scalarX.derived r).app K ≫ adjunction.homEquiv K L a
  homAdditive : ∀ K L (a b : S.functor.obj K ⟶ L),
    adjunction.homEquiv K L (a + b) =
      adjunction.homEquiv K L a + adjunction.homEquiv K L b

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem towerSite (T : Scheme.{u}) (O : Type (u + 1))
    [CommRing O] (t : O) (P : StrictEtaleEvaluation T O t) :
    EtaleTowerBrownSiteProperties T O t P := by
  let B := coefficientRings (J := T.smallEtaleTopology) (O := O) (ell := t)
  let e := coefficientSystemEquivalence (J := T.smallEtaleTopology) (O := O) (ell := t)
  let : HasDerivedCategory.{u + 2} (strictEtaleCoefficientSystem T O t) :=
    strictEtaleSystemDerived T O t
  let : ∀ n, HasDerivedCategory.{u + 2} (strictEtaleLevel T O t n) :=
    strictEtaleLevelDerived T O t
  have := strictRingSystem_isGrothendieckAbelian B
  have : IsGrothendieckAbelian.{u + 1} (strictEtaleCoefficientSystem T O t) :=
    IsGrothendieckAbelian.of_equivalence e.symm
  have : HasColimitsOfSize.{u + 1, u + 1} (strictEtaleCoefficientSystem T O t) :=
    IsGrothendieckAbelian.hasColimits _
  refine ⟨inferInstance, inferInstance, derived_hasCoproducts, ?_, ?_, ?_⟩
  · intro I
    exact derived_Q_preservesCoproducts I
  · intro n I
    have : IsGrothendieckAbelian.{u + 1} (strictEtaleLevel T O t n) :=
      isGrothendieckAbelian_coefficientUniverse _
    have := systemEvaluation_colimitsOfShape B (Discrete I) n
    have : PreservesColimitsOfShape (Discrete I)
        (coefficientEvaluation (J := T.smallEtaleTopology) (O := O) (ell := t) n) := by
      change PreservesColimitsOfShape (Discrete I) (e.functor ⋙ systemEvaluation B n)
      infer_instance
    have := (coefficientEvaluation_exact
      (J := T.smallEtaleTopology) (O := O) (ell := t) n).1
    have := (coefficientEvaluation_exact
      (J := T.smallEtaleTopology) (O := O) (ell := t) n).2
    have := (coefficientEvaluation (J := T.smallEtaleTopology)
      (O := O) (ell := t) n).mapDerivedCategory_preservesCoproducts I
    exact preservesColimitsOfShape_of_natIso (coefficientEvaluation_derivedIso O t P n).symm
  · intro K L a
    exact coefficientEvaluation_detectsIso O t P a

universe a b w dA dB v u' v'
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem brownSized
    {A : Type a} [Category.{w} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [hDA : HasDerivedCategory.{dA} A]
    {B : Type b} [Category.{w} B] [Abelian B]
    [IsGrothendieckAbelian.{w} B] [hDB : HasDerivedCategory.{dB} B]
    [HasCoproducts.{w} (DerivedCategory A)] [HasCoproducts.{w} (DerivedCategory B)]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
    (hF : ∀ I : Type w, PreservesColimitsOfShape (Discrete I) F) :
    F.IsLeftAdjoint := by
  let hA : HasDerivedCategory.{w} A := HasDerivedCategory.ofIsGrothendieckAbelian A
  let hB : HasDerivedCategory.{w} B := HasDerivedCategory.ofIsGrothendieckAbelian B
  let := hA
  let := hB
  let U := @Functor.mapDerivedCategory A _ _ hA A _ _ hDA (𝟭 A) _ _ _
  let V := @Functor.mapDerivedCategory B _ _ hDB B _ _ hB (𝟭 B) _ _ _
  have : U.IsEquivalence :=
    @Functor.isEquivalence_mapDerivedCategory A A _ _ _ _ hA hDA (𝟭 A) _ _
  have : V.IsEquivalence :=
    @Functor.isEquivalence_mapDerivedCategory B B _ _ _ _ hDB hB (𝟭 B) _ _
  let : U.CommShift ℤ := inferInstance
  have : ∀ n : ℤ, (shiftFunctor (@DerivedCategory A _ _ hA) n).Additive := by
    let := hA
    infer_instance
  have : ∀ n : ℤ, (shiftFunctor (@DerivedCategory A _ _ hDA) n).Additive := by
    let := hDA
    infer_instance
  have : U.IsTriangulated := inferInstance
  let : V.CommShift ℤ := inferInstance
  have : ∀ n : ℤ, (shiftFunctor (@DerivedCategory B _ _ hB) n).Additive := by
    let := hB
    infer_instance
  have : ∀ n : ℤ, (shiftFunctor (@DerivedCategory B _ _ hDB) n).Additive := by
    let := hDB
    infer_instance
  have : V.IsTriangulated := inferInstance
  let H := (U ⋙ F) ⋙ V
  let : H.CommShift ℤ := inferInstance
  have : H.IsTriangulated := inferInstance
  have hH (I : Type w) : PreservesColimitsOfShape (Discrete I) H := by
    have := hF I
    infer_instance
  have : H.IsLeftAdjoint := by
    let := hA
    let := hB
    have : HasCoproducts.{w} A := inferInstance
    have : HasCoproducts.{w} B := inferInstance
    have : HasCoproducts.{w} (@DerivedCategory A _ _ hA) := derived_hasCoproducts
    have : HasCoproducts.{w} (@DerivedCategory B _ _ hB) := derived_hasCoproducts
    exact grothendieckDerived_hasRightAdjoint H hH
  exact (Functor.isLeftAdjoint_comp_iff_right U F).mp
    ((Functor.isLeftAdjoint_comp_iff_left (U ⋙ F) V).mp inferInstance)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem towerExact {O : Type (u + 1)} [CommRing O] {t : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O t c) :
    ∃ (_ : S.functor.Additive) (s : S.functor.CommShift ℤ), letI := s;
      S.functor.IsTriangulated := by
  let : S.openImage.inverse.Additive := S.openImage.systemInverseAdditive
  let : S.properImage.inverse.Additive := S.properImage.systemInverseAdditive
  let : S.openImage.rightSystem.Additive := S.openImage.systemRightAdditive
  let : S.properImage.rightSystem.Additive := S.properImage.systemRightAdditive
  have := S.openImage.systemExact.1
  have := S.openImage.systemExact.2
  have := S.properImage.systemExact.1
  have := S.properImage.systemExact.2
  let eo := exactDerivedIso S.openImage.inverse S.openDerived.system.inverse
    S.openDerived.system.inverseFactors
  let ep := exactDerivedIso S.properImage.inverse S.properDerived.system.inverse
    S.properDerived.system.inverseFactors
  let : S.openDerived.system.inverse.CommShift ℤ := CommShift.ofIso eo.symm ℤ
  let : S.properDerived.system.inverse.CommShift ℤ := CommShift.ofIso ep.symm ℤ
  have : NatTrans.CommShift eo.symm.hom ℤ := CommShift.ofIso_compatibility eo.symm ℤ
  have : NatTrans.CommShift ep.symm.hom ℤ := CommShift.ofIso_compatibility ep.symm ℤ
  have : S.openDerived.system.inverse.IsTriangulated :=
    isTriangulated_of_iso eo.symm
  have : S.properDerived.system.inverse.IsTriangulated :=
    isTriangulated_of_iso ep.symm
  have : S.openDerived.system.inverse.Additive := additive_of_iso eo.symm
  have : S.properDerived.system.inverse.Additive := additive_of_iso ep.symm
  let : S.derivedOpen.CommShift ℤ := S.derivedOpenAdjunction.leftAdjointCommShift ℤ
  have : S.derivedOpenAdjunction.CommShift ℤ :=
    S.derivedOpenAdjunction.commShift_of_rightAdjoint ℤ
  have : S.derivedOpen.IsTriangulated := S.derivedOpenAdjunction.isTriangulated_leftAdjoint
  have : S.derivedOpen.Additive := S.derivedOpenAdjunction.left_adjoint_additive
  let : S.properDerived.system.direct.CommShift ℤ :=
    S.properDerived.system.adjunction.rightAdjointCommShift ℤ
  have : S.properDerived.system.adjunction.CommShift ℤ :=
    S.properDerived.system.adjunction.commShift_of_leftAdjoint ℤ
  have : S.properDerived.system.direct.IsTriangulated :=
    S.properDerived.system.adjunction.isTriangulated_rightAdjoint
  have : S.properDerived.system.direct.Additive :=
    S.properDerived.system.adjunction.right_adjoint_additive
  change ∃ (_ : (S.derivedOpen ⋙ S.properDerived.system.direct).Additive)
    (s : (S.derivedOpen ⋙ S.properDerived.system.direct).CommShift ℤ), letI := s;
    (S.derivedOpen ⋙ S.properDerived.system.direct).IsTriangulated
  exact ⟨inferInstance, inferInstance, inferInstance⟩

attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_adjunction {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) (s : 𝟭 C ⟶ 𝟭 C) (t : 𝟭 D ⟶ 𝟭 D)
    (h : ∀ K, F.map (s.app K) = t.app (F.obj K)) :
    (∀ K L (a : F.obj K ⟶ L),
      adj.homEquiv K L (t.app (F.obj K) ≫ a) = s.app K ≫ adj.homEquiv K L a) ∧
    (∀ L, adj.homEquiv (G.obj L) L (t.app (F.obj (G.obj L)) ≫
      adj.counit.app L) = s.app (G.obj L)) ∧
    (∀ L, G.map (t.app L) = s.app (G.obj L)) := by
  have hh (K : C) (L : D) (a : F.obj K ⟶ L) :
      adj.homEquiv K L (t.app (F.obj K) ≫ a) = s.app K ≫ adj.homEquiv K L a := by
    rw [← h, adj.homEquiv_naturality_left]
    rfl
  refine ⟨hh, ?_, ?_⟩
  · intro L
    rw [hh]
    have hc : adj.homEquiv (G.obj L) L (adj.counit.app L) = 𝟙 _ := by
      rw [← adj.homEquiv_symm_id L]
      exact Equiv.apply_symm_apply _ _
    rw [hc]
    exact Category.comp_id _
  · intro L
    apply (adj.homEquiv (G.obj L) L).symm.injective
    simp only [Adjunction.homEquiv_counit, h]
    calc
      _ = adj.counit.app L ≫ t.app L := by
        simpa only [Functor.comp_map, Functor.id_map, Functor.id_obj, Functor.comp_obj]
          using adj.counit.naturality (t.app L)
      _ = _ := by
        simpa only [Functor.id_map, Functor.id_obj, Functor.comp_obj]
          using t.naturality (adj.counit.app L)

private theorem towerTransition {O : Type (u + 1)} [CommRing O] {t : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O t c)
    (a : ∀ {m n : ℕ} (h : n ≤ m),
      (S.PX.scalar h).restriction ⋙ S.levelDerivedOpen m ≅
        S.levelDerivedOpen n ⋙ (S.PZ.scalar h).restriction)
    (ha : ∀ {m n : ℕ} (h : n ≤ m)
      (K : DerivedCategory (strictEtaleCoefficientSystem X O t)),
      (S.PZ.transition h).app (S.derivedOpen.obj K) ≫
        (S.PZ.scalar h).restriction.map ((S.openDerivedEvaluation n).hom.app K) =
      (S.openDerivedEvaluation m).hom.app K ≫
        (S.levelDerivedOpen m).map ((S.PX.transition h).app K) ≫
        (a h).hom.app ((S.PX.evaluation n).obj K))
    {m n : ℕ} (h : n ≤ m)
    (K : DerivedCategory (strictEtaleCoefficientSystem X O t)) :
    (S.PY.transition h).app (S.functor.obj K) ≫
      (S.PY.scalar h).restriction.map ((S.evaluation n).hom.app K) =
    (S.evaluation m).hom.app K ≫
      (S.levelFunctor m).map ((S.PX.transition h).app K) ≫
      (etaleTowerBrownRestriction S a h).hom.app ((S.PX.evaluation n).obj K) := by
  simp only [StrictEtaleCompactSupport.evaluation, etaleTowerBrownRestriction,
    StrictEtaleCompactSupport.functor, StrictEtaleCompactSupport.levelFunctor,
    Functor.comp_obj, Functor.id_obj,
    Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  change (S.PY.transition h).app (S.functor.obj K) ≫
      (S.PY.scalar h).restriction.map
        ((S.properDerived.directEvaluation n).hom.app (S.derivedOpen.obj K) ≫
          (S.properDerived.level n).direct.map ((S.openDerivedEvaluation n).hom.app K)) = _
  erw [Functor.map_comp, ← Category.assoc, S.properDerived.directTransition]
  have hn := (S.properDerived.restrictedDirect h).hom.naturality
    ((S.openDerivedEvaluation n).hom.app K)
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  erw [← hn]
  have hm := congrArg ((S.properDerived.level m).direct.map) (ha h K)
  convert! (congrArg (fun q ↦ (S.properDerived.directEvaluation m).hom.app
      (S.derivedOpen.obj K) ≫ q ≫
      (S.properDerived.restrictedDirect h).hom.app
        ((S.levelDerivedOpen n).obj ((S.PX.evaluation n).obj K))) hm) using 1
  all_goals
    try simp only [Functor.map_comp, Functor.comp_map, Category.assoc]
    try rfl

private theorem towerCoproducts {O : Type (u + 1)} [CommRing O] {t : O}
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (S : StrictEtaleCompactSupport O t c)
    (hX : EtaleTowerBrownSiteProperties X O t S.PX)
    (hY : EtaleTowerBrownSiteProperties Y O t S.PY)
    (hp : ∀ (n : ℕ) (I : Type (u + 1)),
      PreservesColimitsOfShape (Discrete I) (S.properDerived.level n).direct)
    (I : Type (u + 1)) : PreservesColimitsOfShape (Discrete I) S.functor := by
  have : HasCoproducts.{u + 1} (DerivedCategory (strictEtaleCoefficientSystem X O t)) :=
    hX.2.2.1
  have : HasCoproducts.{u + 1} (DerivedCategory (strictEtaleCoefficientSystem Y O t)) :=
    hY.2.2.1
  have hE (n : ℕ) : PreservesColimitsOfShape (Discrete I) (S.PY.evaluation n) :=
    hY.2.2.2.2.1 n I
  have hFE (n : ℕ) :
      PreservesColimitsOfShape (Discrete I) (S.functor ⋙ S.PY.evaluation n) := by
    have := hX.2.2.2.2.1 n I
    have := hp n I
    have : (S.levelDerivedOpen n).IsLeftAdjoint :=
      ⟨_, ⟨S.levelDerivedOpenAdjunction n⟩⟩
    have : PreservesColimitsOfShape (Discrete I) (S.levelFunctor n) := by
      change PreservesColimitsOfShape (Discrete I)
        (S.levelDerivedOpen n ⋙ (S.properDerived.level n).direct)
      infer_instance
    exact preservesColimitsOfShape_of_natIso (S.evaluation n).symm
  let hj : JointlyReflectIsomorphisms S.PY.evaluation :=
    ⟨fun a ha ↦ (hY.2.2.2.2.2 a).2 ha⟩
  constructor
  intro K
  apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
  apply hj.jointlyReflectsColimit
  intro n
  exact isColimitOfPreserves (S.functor ⋙ S.PY.evaluation n) (colimit.isColimit K)

private theorem towerCoefficientFacts
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (t : Padic.coefficientExtensionIntegers l E)
    (ht : Ideal.span ({t} : Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E) :
    (∀ x, t * x = 0 → x = 0) ∧
    IsAdicComplete (Ideal.span ({t} : Set (Padic.coefficientExtensionIntegers l E)))
      (Padic.coefficientExtensionIntegers l E) ∧
    (∀ n : ℕ, Finite ((Padic.coefficientExtensionIntegers l E) ⧸
      (Ideal.span ({t} : Set (Padic.coefficientExtensionIntegers l E))) ^ (n + 1))) := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have ht0 : t ≠ 0 := by
    intro hz
    have hm0 : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
      h.2.2.2.2.2.2.2.2.2.1
    apply hm0
    rw [← ht, hz, Ideal.span_singleton_zero]
  refine ⟨fun x hx ↦ (mul_eq_zero.mp hx).resolve_left ht0, ?_, ?_⟩
  · rw [ht]
    exact Padic.coefficientIntegers_complete l E
  · intro n
    have : Finite ((Padic.coefficientExtensionIntegers l E) ⧸
        Ideal.span ({t} : Set (Padic.coefficientExtensionIntegers l E))) := by
      rw [ht]
      exact h.2.2.2.2.2.2.2.2.2.2.2.1
    exact Ideal.finite_quotient_pow (Submodule.fg_span_singleton _) (n + 1)
private theorem towerNoetherian (k : Type u) [Field k]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) (c : Compactification f) :
    IsLocallyNoetherian Y ∧ CompactSpace Y ∧
      IsLocallyNoetherian c.Z ∧ CompactSpace c.Z := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  exact ⟨inferInstance, inferInstance, LocallyOfFiniteType.isLocallyNoetherian c.g,
    QuasiCompact.compactSpace_of_compactSpace c.g⟩

/-- Compact support on ordinary unbounded étale coefficient towers has an exact,
scalar-linear Brown right adjoint, with canonical evaluation comparisons.
Source: Stacks 0F5Y, proposition-brown; Zheng, Construction 4.1
(blueprint: lem-pur-etale-tower-brown-adjunction).

Proof plan (the node's nine steps):
1. The coefficient valuation-ring and completeness theorems give a domain R and
0 < |t| < 1. Compatible quotient lifts are Cauchy, since their differences lie in
(t^n). Completeness gives a limit in R with those residues. The intersection of
(t^n) is zero, so R is t-adically complete and t is a non-zero-divisor.
2. Apply lem-pur-system-grothendieck and lem-pur-system-coproducts to the constant
quotient sheaves. By lem-sfb-grothendieck-k-injective the system categories have
K-injective resolutions. The localization coproduct theorem
lem-pur-exact-derived-coproducts gives termwise derived sums. Evaluations are exact,
so cohomology is levelwise; applying joint detection of zero objects to cones
shows that the evaluations jointly detect isomorphisms.
3. The recorded etale extension by zero is sheafification of its presheaf formula.
It is exact and left adjoint to inverse image. Restriction of coefficients leaves
that formula unchanged. The level transpose formulas commute with semilinear
transitions and give the system adjunction. Open extension preserves sums and
scalar multiplication. Exact-functor factorization and
lem-pur-linear-localization-lift give its exact linear derived functor, its
termwise representatives and its coproduct preservation.
4. Apply lem-pur-coefficient-system-derived-comparison to the proper map. Compose
its unbounded canonical evaluation comparison with the open comparison. The
restriction mates give the displayed transition square on all objects and maps.
5. K-injective total right derivation is triangulated
(lem-pc-right-derived-functor-triangulated) and scalar-linear
(lem-weil-kinjective-total-derived-linear). Thus so is the composite F.
6. Finite type over a field makes Y and the proper compactification Noetherian.
Each finite ring R/(t^n) satisfies lem-amb-proper-coproducts. Evaluation turns the
system coproduct comparison into the finite-level comparison; joint detection
makes it invertible. Empty sums are included.
7. Apply lem-grothendieck-derived-brown-right-adjoint to F out of the ordinary
unbounded derived Grothendieck system category. It gives the ordinary adjunction
with its actual unit and counit and both triangle identities.
8. The unique right-adjoint shift structure compatible with that on F makes G
exact, by lem-weil-pbc-adjunction-shift-compatibility-unique and
lem-sf-triangulated-right-adjoint.
9. The inverse Hom bijection is v ↦ F(v) followed by the counit. It is R-linear,
so the Hom bijection is linear. Transposing r times the counit gives r times the
identity on G(L); naturality proves G linear. This is the stated scalar action
and the actual ordinary derived-system unit and counit. No unbounded pro-etale
exceptional adjoint is used.
-/
theorem etaleTowerBrownAdjunction
    (p l : ℕ) [Fact p.Prime] [Fact l.Prime] (_hpl : p ≠ l)
    (k : Type u) [Field k] [CharP k p]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (t : Padic.coefficientExtensionIntegers l E)
    (_ht : Ideal.span ({t} : Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (c : Compactification f) :
    ∃ S : StrictEtaleCompactSupport (Padic.coefficientExtensionIntegers l E) t c,
      Nonempty (EtaleTowerBrownAdjunction S) := by
  obtain ⟨hregular, hcomplete, hfinite⟩ := towerCoefficientFacts l E t _ht
  have := hcomplete
  obtain ⟨S, a, hamate, hatransition⟩ := etaleCompactSupport_construction _ t hregular c
  have hX := towerSite X _ t S.PX
  have hZ := towerSite c.Z _ t S.PZ
  have hY := towerSite Y _ t S.PY
  obtain ⟨hYnoeth, hYcompact, hZnoeth, hZcompact⟩ := towerNoetherian k f c
  have hp (n : ℕ) (I : Type (u + 1)) :
      PreservesColimitsOfShape (Discrete I) (S.properDerived.level n).direct := by
    have := hfinite n
    exact etaleCoefficientProper_coproducts _ t c.g S.properImage n
      (S.properDerived.level n) I
  have hcoproducts := towerCoproducts S hX hY hp
  obtain ⟨hadd, hs, hexact⟩ := towerExact S
  let : S.functor.CommShift ℤ := hs
  have : S.functor.IsTriangulated := hexact
  have : IsGrothendieckAbelian.{u + 1} (strictEtaleCoefficientSystem X _ t) := hX.1
  have : IsGrothendieckAbelian.{u + 1} (strictEtaleCoefficientSystem Y _ t) := hY.1
  have : HasCoproducts.{u + 1}
      (DerivedCategory (strictEtaleCoefficientSystem X _ t)) := hX.2.2.1
  have : HasCoproducts.{u + 1}
      (DerivedCategory (strictEtaleCoefficientSystem Y _ t)) := hY.2.2.1
  have : S.functor.IsLeftAdjoint := brownSized S.functor hcoproducts
  let G := S.functor.rightAdjoint
  let adj : S.functor ⊣ G := Adjunction.ofIsLeftAdjoint S.functor
  have : G.Additive := adj.right_adjoint_additive
  let : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  obtain ⟨sx, sy, hlinear⟩ := etaleCompactSupport_scalarAction S
  refine ⟨S, ⟨{
    siteX := hX
    siteZ := hZ
    siteY := hY
    openRestriction := a
    openRestrictionMate := hamate
    transition := towerTransition S a hatransition
    leftAdditive := hadd
    leftShift := hs
    leftExact := hexact
    coproducts := hcoproducts
    scalarX := sx
    scalarY := sy
    leftLinear := hlinear
    right := G
    adjunction := adj
    rightExact := inferInstance
    rightLinear := ?_
    scalarTranspose := ?_
    homLinear := ?_
    homAdditive := adj.homAddEquiv_add }⟩⟩
  · intro r
    exact (scalar_adjunction adj (sx.derived r) (sy.derived r) (hlinear r)).2.2
  · intro r
    exact (scalar_adjunction adj (sx.derived r) (sy.derived r) (hlinear r)).2.1
  · intro r
    exact (scalar_adjunction adj (sx.derived r) (sy.derived r) (hlinear r)).1

end AlgebraicGeometry
