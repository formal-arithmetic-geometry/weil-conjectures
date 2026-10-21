/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import Sheaf.Paper.ConstantCoefficientObjectsConstructible
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.FiniteTorAmplitudeProEtaleModule
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RingedSiteDualityMaps
public import Sheaf.Paper.CoefficientRingedTensorHomModel
public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import all Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus
import Sheaf.Paper.FiniteClopenConstructibilityBounds
import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
import Mathlib.Order.Bounds.Basic
import all Sheaf.CategoryTheory.StrictRoosAdditiveComparison
import all Sheaf.AlgebraicGeometry.VaryingRingOperations
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Sheaf.Paper.DerivedPullbackTensorIso

/-! # Finite clopen decomposition of derived coefficient categories

Source: Stacks Project, Tag 04TS, and the finite-clopen argument in the blueprint
sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md
(blueprint: lem-pur-finite-clopen-derived-decomposition).

Restrictions below are actual precomposition on the small pro-etale sites. The
coefficient rings are the published finite quotients and completed integral sheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures
namespace PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Finite or completed coefficients, with n denoting exponent n+1.
Source: Stacks 04TS and the section-invariant finite-clopen argument
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRing (X : Scheme.{u}) (n : ℕ) (integral : Bool) :
    Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  if integral then completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension X
  else integralCoefficientCommRingSheaf P.coefficients.l P.extension X n

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The actual inclusion of the component site: compose its structure map with j.
Source: Stacks 00XZ, 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenSiteInclusion {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] :
    Y.ProEt ⥤ X.ProEt :=
  MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Continuity of this concrete site inclusion, with no added assumption.
Source: Stacks 00XZ (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenSiteInclusionContinuous {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] :
    (clopenSiteInclusion j).IsContinuous (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Restrict a coefficient ring by precomposition along the component site.
Source: Stacks 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRingRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ((clopenSiteInclusion j).sheafPushforwardContinuous CommRingCat.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj R

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Forget commutativity only; this is the published module-sheaf encoding.
Source: Stacks Modules on Sites (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
abbrev clopenModules (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  ringedSiteModules.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The canonical sectionwise module restriction, including its scalar action.
Source: Stacks 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    clopenModules X R ⥤ clopenModules Y (clopenRingRestriction j R) :=
  SheafOfModules.pushforward (F := clopenSiteInclusion j) (𝟙 _)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Exactness of restriction, required to descend the actual degreewise functor.
Source: Stacks 04TS and 015F (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: localize the small site at the open immersion (weakly-etale localization).
Restriction of module sheaves is exact; kernels and sheafified cokernels restrict
locally. Its formula is additive. This uses sheaf exactness, not sectionwise
surjectivity of epimorphisms. -/
theorem clopenRestriction_exact {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (clopenRestriction j R).Additive ∧ PreservesFiniteLimits (clopenRestriction j R) ∧
      PreservesFiniteColimits (clopenRestriction j R) := by
  refine ⟨?_, ?_⟩
  · exact Scheme.ProEt.clopenModuleRestriction_additive j _
  · exact Scheme.ProEt.FiniteClopenTensor.restriction_exact.{u, u} j R

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Additivity from exact sectionwise restriction. Source: Stacks 04TS
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenRestrictionAdditive {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    (clopenRestriction j R).Additive := (clopenRestriction_exact j R).1

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Left exactness from the preceding named theorem. Source: Stacks 04TS
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenRestrictionLimits {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteLimits (clopenRestriction j R) := (clopenRestriction_exact j R).2.1

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Right exactness from the preceding named theorem. Source: Stacks 04TS
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenRestrictionColimits {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    PreservesFiniteColimits (clopenRestriction j R) := (clopenRestriction_exact j R).2.2

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The standard unbounded localization of these abelian module categories.
Source: Stacks 05RU (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
instance clopenHasDerived (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory (clopenModules X R) := HasDerivedCategory.standard _

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Restrict complexes degreewise and descend through quasi-isomorphisms.
Source: Stacks 015F, 05RU (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenDerivedRestriction {Y X : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  (clopenRestriction j R).mapDerivedCategory

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Invertibility of ell in a residue field over the fixed algebraically closed base.
Source: purity conventions (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: ell differs from p, so is nonzero in k. The structure map to the residue
field carries its inverse in k to an inverse there. No new geometric hypothesis
is required. -/
theorem clopenResidue_isUnit (Y : Over (Spec (CommRingCat.of P.field.k))) (y : Y.left) :
    IsUnit (P.coefficients.l : Y.left.residueField y) := by
  simpa only [map_natCast] using
    (P.coefficientPrime_isUnit_stalk Y.left Y.hom y).map
      (IsLocalRing.residue (Y.left.presheaf.stalk y))

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The recorded constructible integral pullback, supplying only the source-implied
residue-field invertibility. Source: blueprint integral coefficient conventions
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralPullback {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  constructibleIntegralPullback P.coefficients.l P.extension j.left

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The recorded raw rationalized pullback, without Karoubi completion.
Source: blueprint rational coefficient conventions
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRationalPullback {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  rationalDerivedPullback P.coefficients.l P.extension j.left

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The recorded common-stage pullback, on the fixed algebraic coefficient closure.
Source: blueprint common-stage coefficient conventions
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenCommonStagePullback {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  commonStageDerivedPullback P.coefficients.l P.coefficients.Qbar j.left


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The completed tensor on the constructible integral category, with the recorded
normalization on strict K-flat towers. Source: blueprint coefficient operations
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  constructibleIntegralTensor P.coefficients.l P.extension Y.left

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The recorded rational tensor, extended linearly on morphisms.
Source: blueprint coefficient operations
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRationalTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  rationalDerivedTensor P.coefficients.l P.extension Y.left

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The common-stage tensor, formed at the coefficient compositum.
Source: blueprint coefficient operations
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenCommonStageTensor (Y : Over (Spec (CommRingCat.of P.field.k))) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  commonStageDerivedTensor P.coefficients.l P.coefficients.Qbar Y.left

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The actual regular completed module in the intrinsic constructible category.
Only its membership proof comes from the published constant-coefficient theorem.
Source: blueprint coefficient unit (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralUnit (Y : Scheme.{u}) :
    sfIntegralConstructibleCategory P.coefficients.l P.extension Y :=
  ⟨integralConstantCoefficientObject P.coefficients.l P.extension Y,
    (integralConstantCoefficient_constructible P.coefficients.l P.extension Y
      P.field P.coefficients.different).2.1⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The raw rational image of the same regular integral module.
Source: blueprint coefficient unit (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRationalUnit (Y : Scheme.{u}) :=
  (sfRationalConstructibleLocalization P.coefficients.l P.extension Y).obj (P.clopenIntegralUnit Y)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The coefficient unit at any finite stage of the fixed algebraic closure.
Its small field model is the published one, and its integral representative is
the regular completed module in degree zero.
Source: blueprint coefficient unit (blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenCommonStageUnit (Y : Scheme.{u})
    (B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar) :
    generalAlgebraicallyClosedConstructibleCategory P.coefficients.l P.coefficients.Qbar Y :=
  ⟨B, (sfRationalConstructibleLocalization P.coefficients.l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
    Y).obj
      ⟨integralConstantCoefficientObject P.coefficients.l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B) Y,
        (integralConstantCoefficient_constructible P.coefficients.l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} P.coefficients.l P.coefficients.Qbar B)
          Y P.field P.coefficients.different).2.1⟩⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The existing canonical integral scalar/restriction comparison, on every finite
coefficient extension including identities. Source: blueprint coefficient transports
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralScalarComparison (L : Type u) [Field L]
    [Algebra (Padic P.coefficients.l) L] [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L)
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X)
    (K : sfIntegralConstructibleCategory P.coefficients.l P.extension X.left) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  integralPullbackScalarComparison P.coefficients.l P.extension L ι j.left K

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The same normalized comparison after raw rationalization. Its action is the
linear extension of the preceding integral map, exactly as in the recorded operations.
Source: blueprint coefficient transports
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenRationalScalarComparison (L : Type u) [Field L]
    [Algebra (Padic P.coefficients.l) L] [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L)
    {Y X : Over (Spec (CommRingCat.of P.field.k))} (j : Y ⟶ X) :=
  letI := fun y : Y.left ↦ (P.clopenResidue_isUnit Y y).invertible
  letI := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  rationalPullbackScalarComparison P.coefficients.l P.extension L ι j.left

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
private def clopenTowerComplex {A : Type*} [Category A] [HasZeroMorphisms A]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) : CochainComplex (ℕᵒᵖ ⥤ A) ℤ where
  X i := C ⋙ HomologicalComplex.eval A (ComplexShape.up ℤ) i
  d i j :=
    { app := fun n ↦ (C.obj n).d i j
      naturality := fun n m g ↦ (C.map g).comm i j }
  shape i j h := by ext n; exact (C.obj n).shape i j h
  d_comp_d' i j k _ _ := by ext n; exact (C.obj n).d_comp_d i j k

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
private theorem clopenRoosIso {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F] :
    Nonempty (integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ⋙
        integralOperationsRoosFunctor) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let : PreservesLimitsOfShape (Discrete ℕ) G :=
    HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun i ↦ by
      change PreservesLimitsOfShape (Discrete ℕ)
        (HomologicalComplex.eval A (ComplexShape.up ℤ) i ⋙ F)
      infer_instance)
  refine ⟨NatIso.ofComponents (fun C ↦ roosTheta F (clopenTowerComplex C)) ?_⟩
  intro C D a
  let f : clopenTowerComplex C ⟶ clopenTowerComplex D :=
    { f := fun i ↦
        { app := fun n ↦ (a.app n).f i
          naturality := fun n m g ↦ congrArg (fun z ↦ z.f i) (a.naturality g) }
      comm' := fun i j _ ↦ by ext n; exact (a.app n).comm i j }
  exact roosTheta_map F _ _ (strictRoosProductMap_comm f)
    _ _ (strictRoosProductMap_comm
      ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex (.up ℤ)).map f))
    (roosComparison_map F f) (roosComparison_map F f)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
private theorem clopenSupport_iso {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory Y A} (e : K ≅ L) :
    Scheme.proEtaleCohomologicalSupport K = Scheme.proEtaleCohomologicalSupport L := by
  ext m
  exact not_congr ⟨fun h ↦ h.of_iso ((DerivedCategory.homologyFunctor _ m).mapIso e).symm,
    fun h ↦ h.of_iso ((DerivedCategory.homologyFunctor _ m).mapIso e)⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
private theorem clopenTor_iso {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {K L : Scheme.proEtaleDerivedCategory Y A} (e : K ≅ L) (a b : ℤ) :
    Scheme.HasProEtaleTorAmplitude Y A K a b ↔
      Scheme.HasProEtaleTorAmplitude Y A L a b := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro T Q ht f hf hQ M q hq
    exact h.2 T Q ⟨ht.some ≪≫ e.symm⟩ f hf hQ M q hq
  · intro h
    refine ⟨h.1, ?_⟩
    intro T Q ht f hf hQ M q hq
    exact h.2 T Q ⟨ht.some ≪≫ e⟩ f hf hQ M q hq

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
private theorem clopenSheafConstructible_iso {Y : Scheme.{u}} {A : Type u}
    [CommRing A] [Finite A]
    {F G : Scheme.proEtaleRingModules Y (Scheme.proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : Scheme.IsConstructibleProEtaleModuleSheaf Y A F) :
    Scheme.IsConstructibleProEtaleModuleSheaf Y A G := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S, hn, fun i ↦ ?_⟩
  let e' := (Scheme.proEtaleConstantRingPullback A (S.immersion i)).mapIso e
  obtain ⟨I, U, f, hc, ht⟩ := (hS i).1
  refine ⟨⟨I, U, f, hc, fun j ↦ ?_⟩, ?_⟩
  · obtain ⟨M, ⟨hM⟩⟩ := ht j
    exact ⟨M, ⟨(SheafOfModules.overFunctor _ (U j)).mapIso e'.symm ≪≫ hM⟩⟩
  · intro Ω _ _ y
    let E := Scheme.geometricRingModuleStalkFunctor y (Scheme.proEtaleConstantRing (S.domain i) A)
    have : Finite (E.obj ((Scheme.proEtaleConstantRingPullback A
        (S.immersion i)).obj F)) := (hS i).2 Ω y
    exact Finite.of_injective (E.mapIso e'.symm).toLinearEquiv
      (E.mapIso e'.symm).toLinearEquiv.injective

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
private theorem clopenTor_mono {Y : Scheme.{u}} {A : Type u} [CommRing A]
    {K : Scheme.proEtaleDerivedCategory Y A} {a b c d : ℤ}
    (h : Scheme.HasProEtaleTorAmplitude Y A K a b) (hca : c ≤ a) (hbd : b ≤ d) :
    Scheme.HasProEtaleTorAmplitude Y A K c d := by
  refine ⟨hca.trans (h.1.trans hbd), ?_⟩
  intro L Q e f hf hQ M q hq
  exact h.2 L Q e f hf hQ M q (hq.imp (fun h ↦ h.trans_le hca)
    (fun h ↦ hbd.trans_lt h))

section Decomposition
variable (X : Over (Spec (CommRingCat.of P.field.k)))
  [hft : LocallyOfFiniteType X.hom] [hqc : QuasiCompact X.hom]
  {I : Type w} [hfinite : Finite I]
  (Xi : I → Over (Spec (CommRingCat.of P.field.k))) (j : ∀ i, Xi i ⟶ X)
  [∀ i, IsOpenImmersion (j i).left] [hclosed : ∀ i, IsClosedImmersion (j i).left]
  (hdisjoint : ∀ i i', i ≠ i' → Disjoint (Set.range (j i).left) (Set.range (j i').left))
  (hcover : (⋃ i, Set.range (j i).left) = Set.univ)

include hft hqc hfinite hclosed hdisjoint hcover

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Exact module equivalence and its explicit sectionwise inverse.
Source: Stacks 04TS (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: steps 1--3 of the node. The components cover the pro-etale site; distinct
intersections are empty. Glue modules and morphisms (module-sheaf gluing and set
sheaf morphism descent). On a test object V the inverse has sections the product
of the sections on V times_X Xi. Restriction maps and scalar actions are componentwise.
The sheaf axiom gives the unit and counit. Additivity is sectionwise and an additive
equivalence preserves kernels and cokernels. Empty components give zero factors;
the empty cover forces every section group to be zero. -/
theorem finiteClopen_module_equivalence (n : ℕ) (integral : Bool) :
    ∃ e : clopenModules X.left (P.clopenRing X.left n integral) ≌
        (∀ i, clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))),
      e.functor = Functor.pi' (fun i ↦
        clopenRestriction (j i).left (P.clopenRing X.left n integral)) ∧
      PreservesFiniteLimits e.functor ∧ PreservesFiniteColimits e.functor ∧
      PreservesFiniteLimits e.inverse ∧ PreservesFiniteColimits e.inverse ∧
      ∃ φ : ∀ (F : ∀ i, clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))
          (V : X.left.ProEt),
        ((e.inverse.obj F).val.obj (op V)) ≃+
          (∀ i, (F i).val.obj (op ((Scheme.proEtaleBaseChange (j i).left).obj V))),
        (∀ F V (r : (P.clopenRing X.left n integral).obj.obj (op V))
          (x : (e.inverse.obj F).val.obj (op V)) (i : I),
          φ F V (r • x) i =
            ((P.clopenRing X.left n integral).obj.map
              (MorphismProperty.Over.homMk
                (A := (clopenSiteInclusion (j i).left).obj
                  ((Scheme.proEtaleBaseChange (j i).left).obj V)) (B := V)
                (pullback.fst V.hom (j i).left) pullback.condition).op r) • φ F V x i) ∧
        (∀ (F : ∀ i, clopenModules (Xi i).left
            (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))
            (V W : X.left.ProEt) (f : V ⟶ W) (x : (e.inverse.obj F).val.obj (op W)),
          φ F V ((e.inverse.obj F).val.map f.op x) =
            fun i ↦ (F i).val.map ((Scheme.proEtaleBaseChange (j i).left).map f).op
              (φ F W x i)) ∧
        (∀ (F G : ∀ i, clopenModules (Xi i).left
            (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))
            (a : F ⟶ G) (V : X.left.ProEt) (x : (e.inverse.obj F).val.obj (op V)),
          φ G V ((e.inverse.map a).val.app (op V) x) =
            fun i ↦ (a i).val.app
              (op ((Scheme.proEtaleBaseChange (j i).left).obj V)) (φ F V x i)) := by
  classical
  obtain ⟨m, ⟨f⟩⟩ := Finite.exists_equiv_fin I
  let q := f.symm
  let Y (k : Fin m) := (Xi (q k)).left
  let k (r : Fin m) := (j (q r)).left
  let R := (sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    (P.clopenRing X.left n integral)
  have hc : ∀ x : X.left, ∃ a : Fin m, x ∈ Set.range (k a) := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (show x ∈ ⋃ i, Set.range (j i).left by
      rw [hcover]; trivial)
    refine ⟨f i, ?_⟩
    change x ∈ Set.range ((j (f.symm (f i))).left)
    rw [f.symm_apply_apply]
    exact hi
  let G := Scheme.ProEt.gluingFunctor.{u, u + 1, 0, 0} k R
  let E := Scheme.ProEt.gluingEquivalence.{u, u + 1, 0, 0} k
    (fun a b hab ↦ hdisjoint (q a) (q b) (fun he ↦ hab (q.injective he))) hc R
  let C (i : I) := clopenModules (Xi i).left
    (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))
  let T := Pi.equivalenceOfEquiv C q
  let E' : clopenModules X.left (P.clopenRing X.left n integral) ≌ (∀ i, C i) :=
    (E.trans T).changeFunctor (G := Functor.pi' (fun i ↦
      clopenRestriction (j i).left (P.clopenRing X.left n integral)))
    (by
      let U := Functor.pi' (fun i ↦
        clopenRestriction (j i).left (P.clopenRing X.left n integral))
      change (U ⋙ T.inverse) ⋙ T.functor ≅ U
      exact associator U T.inverse T.functor ≪≫
        isoWhiskerLeft U T.counitIso ≪≫ rightUnitor U)
  have heinv : E'.inverse = T.inverse ⋙ G := rfl
  refine ⟨E', rfl, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  rw [heinv]
  let τ (F : ∀ i, C i) (V : X.left.ProEt) :
      (∀ r : Fin m, (F (q r)).val.obj
        (op ((Scheme.proEtaleBaseChange (j (q r)).left).obj V))) ≃+
      (∀ i, (F i).val.obj (op ((Scheme.proEtaleBaseChange (j i).left).obj V))) :=
    { Equiv.piCongrLeft _ q with
      map_add' := fun x y ↦ by
        funext i
        obtain ⟨r, rfl⟩ := q.surjective i
        simp }
  have hτ (F : ∀ i, C i) (V : X.left.ProEt) (x) (a : Fin m) :
      τ F V x (q a) = x a := by
    simp [τ]
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro F V r x i
    obtain ⟨a, rfl⟩ := q.surjective i
    change τ F V _ (q a) = _ • τ F V _ (q a)
    rw [hτ, hτ]
    rfl
  · intro F V W g x
    funext i
    obtain ⟨a, rfl⟩ := q.surjective i
    change τ F V _ (q a) =
      (F (q a)).val.map ((Scheme.proEtaleBaseChange (j (q a)).left).map g).op
        (τ F W _ (q a))
    rw [hτ, hτ]
    rfl
  · intro F H g V x
    funext i
    obtain ⟨a, rfl⟩ := q.surjective i
    change τ H V _ (q a) =
      (g (q a)).val.app (op ((Scheme.proEtaleBaseChange (j (q a)).left).obj V))
        (τ F V _ (q a))
    rw [hτ, hτ]
    rfl

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The degreewise restrictions induce the product of the unbounded derived categories,
with componentwise cohomology, tensor and the regular coefficient unit.
Source: Stacks 04TS, 015F, 06YS, 0G7D
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node steps 4--6. Restriction and insertion into one coordinate are exact.
Their identities descend through quasi-isomorphisms, so the product here is the
product of derived categories. Exact restriction commutes with cohomology. The
bilinear universal property identifies ordinary tensors and the coefficient unit.
K-flatness is detected componentwise by testing against insertions of acyclic
complexes. Descending the pure-tensor comparison on K-flat resolutions gives
the natural tensor isomorphism, with the normalized existing tensor models. -/
theorem finiteClopen_unbounded_decomposition (n : ℕ) (integral : Bool) :
    (Functor.pi' (fun i ↦
      clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral))).IsEquivalence ∧
    (∀ (i : I) (m : ℤ), Nonempty
      (clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral) ⋙
          DerivedCategory.homologyFunctor _ m ≅
        DerivedCategory.homologyFunctor _ m ⋙
          clopenRestriction (j i).left (P.clopenRing X.left n integral))) ∧
    (∀ i : I, Nonempty
      ((clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral)).obj
          ((DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
            ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (P.clopenRing X.left n integral)))) ≅
        (DerivedCategory.singleFunctor _ 0).obj (SheafOfModules.unit
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (clopenRingRestriction (j i).left (P.clopenRing X.left n integral)))))) ∧
    ∀ (M : RingedSiteDualityModel.{u + 1, u, u, u + 2} (Scheme.ProEt.topology X.left)
        (P.clopenRing X.left n integral)) (i : I)
      (Mi : RingedSiteDualityModel.{u + 1, u, u, u + 2} (Scheme.ProEt.topology (Xi i).left)
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))),
      Nonempty (M.closed.tensor ⋙
          clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral) ≅
        ((clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral)).prod
          (clopenDerivedRestriction (j i).left (P.clopenRing X.left n integral))) ⋙
            Mi.closed.tensor) := by
  sorry

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Strict towers and their functorial Roos complexes restrict termwise.
Source: Stacks 08TC (blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node step 7. Restriction keeps sectionwise countable products and their
projections, including the transition endomorphism 1-s. It therefore commutes
with its functorial shifted mapping cone on objects and strict maps. Exactness
of countable pro-etale products identifies these products with derived products.
Applying the exact restriction to any Roos triangle gives the component Roos
triangle, with its original maps; no canonical uniqueness of bare cones is used. -/
theorem finiteClopen_strict_roos (n : ℕ) (integral : Bool) (i : I) :
    Nonempty (integralOperationsRoosFunctor ⋙
        (clopenRestriction (j i).left (P.clopenRing X.left n integral)).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj
          ((clopenRestriction (j i).left (P.clopenRing X.left n integral)).mapHomologicalComplex
            (ComplexShape.up ℤ)) ⋙ integralOperationsRoosFunctor) := by
  let F := clopenRestriction (j i).left (P.clopenRing X.left n integral)
  have : F.IsRightAdjoint :=
    AlgebraicGeometry.ProEtale.VaryingRing.largePush_isRightAdjoint
      (Scheme.ProEt.topology (Xi i).left) (Scheme.ProEt.topology X.left)
      (clopenSiteInclusion (j i).left) _ _ (𝟙 _)
  exact clopenRoosIso F

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Finite constructibility, fixed cohomological intervals and fixed Tor intervals
are detected on the components; hence both finite-coefficient subcategories split.
Source: blueprint section-invariant well-definedness, finite stage
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node step 8. Intersect a finite stratification with the clopen pieces;
conversely unite their finitely many stratifications. Cohomology is componentwise,
so every common interval works. Test Tor against inserted degree-zero modules and
use componentwise derived tensor. Lifting the restriction functors to these full
subcategories and restricting the gluing inverse gives the two equivalences.
No nonempty-index hypothesis is needed; ordered intervals also work for zero objects. -/
theorem finiteClopen_finite_bounds (n : ℕ)
    (K : Scheme.proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))) :
    (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) X.left K ↔
      ∀ i, Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
        (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K)) ∧
    (∀ a b : ℤ, a ≤ b →
      (Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc a b ↔
        ∀ i, Scheme.proEtaleCohomologicalSupport
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) ⊆
            Set.Icc a b)) ∧
    (∀ a b : ℤ, a ≤ b →
      (Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) K a b ↔
        ∀ i, Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) a b)) := by
  classical
  let Pn : PurityFiniteSetting.{u} := { P with
    level := n + 1
    level_pos := Nat.succ_pos n }
  let : X.left.Over (Spec (CommRingCat.of Pn.field.k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of Pn.field.k)) := hft
  have : QuasiCompact (X.left ↘ Spec (CommRingCat.of Pn.field.k)) := hqc
  have H := finite_clopen_constructibility_bounds Pn X.left (fun i ↦ (Xi i).left)
    (fun i ↦ (j i).left) hdisjoint hcover
  let e (i : I) := Scheme.openSquareDerivedPullbackModel Pn.Ring (j i).left
  have hsupport : ∀ (i : I),
      Scheme.proEtaleCohomologicalSupport
          ((Scheme.proEtaleConstantRingDerivedPullback Pn.Ring (j i).left).obj K) =
        Scheme.proEtaleCohomologicalSupport
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) :=
    fun i ↦ clopenSupport_iso ((e i).app K)
  have hbound : ∀ a b : ℤ, a ≤ b →
      (Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc a b ↔
        ∀ i, Scheme.proEtaleCohomologicalSupport
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) ⊆
            Set.Icc a b) := by
    intro a b hab
    simpa only [hsupport] using H.2.2.2.2.1 K a b hab
  refine ⟨?_, hbound, ?_⟩
  · have hconstructible := H.2.2.2.1 K
    have hcoh :
        (∀ m : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf X.left Pn.Ring
          ((DerivedCategory.homologyFunctor _ m).obj K)) ↔
        ∀ (i : I) (m : ℤ), Scheme.IsConstructibleProEtaleModuleSheaf (Xi i).left Pn.Ring
          ((DerivedCategory.homologyFunctor _ m).obj
            ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K)) := by
      refine hconstructible.trans ⟨?_, ?_⟩
      · intro h i m
        exact clopenSheafConstructible_iso
          ((DerivedCategory.homologyFunctor _ m).mapIso ((e i).app K)) (h i m)
      · intro h i m
        exact clopenSheafConstructible_iso
          ((DerivedCategory.homologyFunctor _ m).mapIso ((e i).app K)).symm (h i m)
    change (_ ∧ _) ↔ ∀ i, _ ∧ _
    constructor
    · rintro ⟨hb, hc⟩
      obtain ⟨a, ha⟩ := hb.bddBelow
      obtain ⟨b, hb⟩ := hb.bddAbove
      have hs : Scheme.proEtaleCohomologicalSupport K ⊆ Set.Icc (min a b) (max a b) :=
        fun q hq ↦ ⟨(min_le_left a b).trans (ha hq), (hb hq).trans (le_max_right a b)⟩
      intro i
      exact ⟨(Set.finite_Icc _ _).subset ((hbound _ _
        ((min_le_left a b).trans (le_max_left a b))).mp hs i), hcoh.mp hc i⟩
    · intro h
      have hs := Set.finite_iUnion (fun i ↦ (h i).1)
      obtain ⟨a, ha⟩ := hs.bddBelow
      obtain ⟨b, hb⟩ := hs.bddAbove
      refine ⟨(Set.finite_Icc (min a b) (max a b)).subset
        ((hbound _ _ ((min_le_left a b).trans (le_max_left a b))).mpr ?_),
        hcoh.mpr (fun i ↦ (h i).2)⟩
      intro i q hq
      have hmem : q ∈ ⋃ i, Scheme.proEtaleCohomologicalSupport
          ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) :=
        Set.mem_iUnion.mpr ⟨i, hq⟩
      exact ⟨(min_le_left a b).trans (ha hmem), (hb hmem).trans (le_max_right a b)⟩
  · intro a b hab
    refine (H.2.2.2.2.2.1 K a b hab).trans ?_
    exact forall_congr' (fun i ↦ clopenTor_iso ((e i).app K) a b)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Restriction on the finite constructible full subcategory, with its actual
ambient pullback on both objects and arrows. Source: blueprint finite-clopen argument
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenFiniteConstructiblePullback (n : ℕ) (i : I) :=
  (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left).lift
    ((Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X.left).ι ⋙
        finiteDerivedPullback P.coefficients.l P.extension n (j i).left)
    (fun K ↦ ((P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n K.obj).1.mp
      K.property) i)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The finite-Tor condition is detected on the finite list of components.
Source: blueprint finite-clopen argument, step 8
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: use finiteClopen_finite_bounds for constructibility and Tor in a fixed interval.
For the converse take the minimum and maximum of the finitely many component bounds.
For no components take [0,0]; vanishing is detected by the empty covering sheaf axiom. -/
theorem finiteClopen_finiteTor_iff (n : ℕ)
    (K : Scheme.proEtaleDerivedCategory X.left
      (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))) :
    finiteTorConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) X.left K ↔
      ∀ i, finiteTorConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj K) := by
  classical
  have H := P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n K
  constructor
  · rintro ⟨hc, a, b, ht⟩ i
    exact ⟨H.1.mp hc i, a, b, (H.2.2 a b ht.1).mp ht i⟩
  · intro h
    have hc := H.1.mpr (fun i ↦ (h i).1)
    choose a b ht using fun i ↦ (h i).2
    obtain ⟨c, hc'⟩ := (Set.finite_range a).bddBelow
    obtain ⟨d, hd'⟩ := (Set.finite_range b).bddAbove
    refine ⟨hc, min c d, max c d, (H.2.2 _ _ ?_).mpr ?_⟩
    · exact (min_le_left c d).trans (le_max_left c d)
    · intro i
      exact clopenTor_mono (ht i) ((min_le_left c d).trans (hc' ⟨i, rfl⟩))
        ((hd' ⟨i, rfl⟩).trans (le_max_right c d))

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The finite-Tor restriction is the full-subcategory lift of the recorded pullback.
Source: blueprint finite-clopen argument, step 8
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenFiniteTorPullback (n : ℕ) (i : I) :=
  (finiteTorConstructible P.coefficients.l P.extension (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n)) (Xi i).left).lift
    ((finiteTorConstructible P.coefficients.l P.extension (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) X.left).ι ⋙
        finiteDerivedPullback P.coefficients.l P.extension n (j i).left)
    (fun K ↦ (P.finiteClopen_finiteTor_iff X Xi j hdisjoint hcover n K.obj).mp K.property i)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Both finite coefficient full-subcategory equivalences use these exact restrictions.
Source: blueprint finite-clopen argument, step 8
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: restrict the ambient derived equivalence using the componentwise predicates.
The inverse gluing preserves them by the converse parts of the two bound statements. -/
theorem finiteClopen_finite_equivalences (n : ℕ) :
    (Functor.pi' (fun i ↦ P.clopenFiniteConstructiblePullback X Xi j
      hdisjoint hcover n i)).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenFiniteTorPullback X Xi j
      hdisjoint hcover n i)).IsEquivalence := by
  let Pn : PurityFiniteSetting.{u} := { P with
    level := n + 1
    level_pos := Nat.succ_pos n }
  let : X.left.Over (Spec (CommRingCat.of Pn.field.k)) := ⟨X.hom⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (CommRingCat.of Pn.field.k)) := hft
  have : QuasiCompact (X.left ↘ Spec (CommRingCat.of Pn.field.k)) := hqc
  have H := finite_clopen_constructibility_bounds Pn X.left (fun i ↦ (Xi i).left)
    (fun i ↦ (j i).left) hdisjoint hcover
  obtain ⟨e, ⟨he⟩⟩ := H.2.2.2.2.2.2.1
  obtain ⟨t, ⟨ht⟩⟩ := H.2.2.2.2.2.2.2.1
  constructor
  · apply Functor.isEquivalence_of_iso (F := e.functor)
    apply NatIso.pi'
    intro i
    apply Functor.fullyFaithfulCancelRight
      (Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_pos n) (Xi i).left).ι
    exact isoWhiskerRight he (Pi.eval _ i) ≪≫
      isoWhiskerLeft _ (Scheme.openSquareDerivedPullbackModel Pn.Ring (j i).left)
  · apply Functor.isEquivalence_of_iso (F := t.functor)
    apply NatIso.pi'
    intro i
    apply Functor.fullyFaithfulCancelRight
      (finiteTorConstructible P.coefficients.l P.extension (n + 1)
        (Nat.succ_pos n) (Xi i).left).ι
    exact isoWhiskerRight ht (Pi.eval _ i) ≪≫
      isoWhiskerLeft _ (Scheme.openSquareDerivedPullbackModel Pn.Ring (j i).left)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Tensor and integral reduction are componentwise for the actual coefficient functors.
Source: Stacks 06YS, 0G7D, 08TC; blueprint coefficient transport
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: steps 5--6 and 9--11. Restriction carries sheaf tensor generators to the
same pure tensors. Descend on K-flat representatives to obtain the finite natural
comparison. For integral tensor and reduction, restrict the strict towers and
use the natural Roos comparison. Extend the resulting maps linearly to rational
Homs and then represent them at the common finite coefficient compositum.
All maps commute with identity and composite coefficient changes because the
pure-tensor formulas and the strict tower maps do. -/
theorem finiteClopen_tensor_and_reduction (i : I) :
    (∀ n : ℕ, Nonempty
      (finiteIntrinsicDerivedTensor P.coefficients.l P.extension X.left n ⋙
          finiteDerivedPullback P.coefficients.l P.extension n (j i).left ≅
        ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).prod
          (finiteDerivedPullback P.coefficients.l P.extension n (j i).left)) ⋙
            finiteIntrinsicDerivedTensor P.coefficients.l P.extension (Xi i).left n)) ∧
    Nonempty (P.clopenIntegralTensor X ⋙ P.clopenIntegralPullback (j i) ≅
      ((P.clopenIntegralPullback (j i)).prod (P.clopenIntegralPullback (j i))) ⋙
        P.clopenIntegralTensor (Xi i)) ∧
    Nonempty (P.clopenRationalTensor X ⋙ P.clopenRationalPullback (j i) ≅
      ((P.clopenRationalPullback (j i)).prod (P.clopenRationalPullback (j i))) ⋙
        P.clopenRationalTensor (Xi i)) ∧
    Nonempty (P.clopenCommonStageTensor X ⋙ P.clopenCommonStagePullback (j i) ≅
      ((P.clopenCommonStagePullback (j i)).prod (P.clopenCommonStagePullback (j i))) ⋙
        P.clopenCommonStageTensor (Xi i)) ∧
    (∀ n : ℕ, Nonempty
      ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          scalarReductionDerivedExtension P.coefficients.l P.extension X.left n ⋙
          finiteDerivedPullback P.coefficients.l P.extension n (j i).left ≅
        P.clopenIntegralPullback (j i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι ⋙
          scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n)) ∧
    (∀ (m n : ℕ) (h : n ≤ m), Nonempty
      (coefficientFiniteQuotientDerived P.coefficients.l P.extension X.left h ⋙
          finiteDerivedPullback P.coefficients.l P.extension n (j i).left ≅
        finiteDerivedPullback P.coefficients.l P.extension m (j i).left ⋙
          coefficientFiniteQuotientDerived P.coefficients.l P.extension (Xi i).left h)) := by
  let := fun y : (Xi i).left ↦ (P.clopenResidue_isUnit (Xi i) y).invertible
  let := fun x : X.left ↦ (P.clopenResidue_isUnit X x).invertible
  let l := P.coefficients.l
  let E := P.extension
  have h := derivedPullbackTensorIso l E (j i).left 0 P.coefficients.Qbar
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨e, _⟩ := (derivedPullbackTensorIso l E (j i).left n P.coefficients.Qbar).1
    exact ⟨e⟩
  · exact ⟨h.2.2.2.2.2.1.choose⟩
  · exact ⟨h.2.2.2.2.2.2.1.choose⟩
  · exact ⟨h.2.2.2.2.2.2.2.1.choose⟩
  · intro n
    let C := (sfIntegralConstructible l E X.left).ι
    let F := P.clopenIntegralPullback (j i)
    let SX := pullbackTensorCalculus l E X.left
    let SY := pullbackTensorCalculus l E (Xi i).left
    let G := C ⋙ SX.reduction ⋙ pullbackTensorSequenceDerived l E (j i).left
    have hc : IsIso (whiskerLeft G SY.adjunction.counit) := by
      apply (NatTrans.isIso_iff_isIso_app _).mpr
      intro K
      exact (pullbackTensorComparisonCounits l E (j i).left K K).2.1
    let e : F ⋙ (sfIntegralConstructible l E (Xi i).left).ι ⋙ SY.reduction ≅
        C ⋙ SX.reduction ⋙ pullbackTensorSequenceDerived l E (j i).left :=
      isoWhiskerLeft C
        (isoWhiskerRight (pullbackTensorIntegralPullbackModel l E (j i).left)
          SY.reduction) ≪≫ asIso (whiskerLeft G SY.adjunction.counit)
    exact ⟨(isoWhiskerRight
        (isoWhiskerLeft C (SX.reductionEvaluation n))
          (finiteDerivedPullback l E n (j i).left)).symm ≪≫
      isoWhiskerLeft (C ⋙ SX.reduction)
        (pullbackTensorDerivedEvaluation l E (j i).left n).symm ≪≫
      isoWhiskerRight e.symm (coefficientSequenceDerivedEvaluation l E (Xi i).left n) ≪≫
      isoWhiskerLeft (F ⋙ (sfIntegralConstructible l E (Xi i).left).ι)
        (SY.reductionEvaluation n)⟩
  · intro m n h
    exact ⟨(pullbackTensorQuotient l E (j i).left h).symm⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Integral finite-Tor restriction, including detection of each common interval
uniformly over every finite reduction.
Source: blueprint finite-clopen argument, step 9
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: commute restriction with derived reduction and the strict Roos functor.
Completeness is the Roos triangle with its canonical reduction unit, hence is
componentwise. Apply finiteClopen_finite_bounds at every positive exponent; the
same a,b is retained, so these bounds are uniform in all reductions. A finite
union of the component intervals supplies common bounds for the inverse. -/
theorem finiteClopen_integral_bounds (K : sfIntegralConstructibleCategory
    P.coefficients.l P.extension X.left) :
    (finiteTorConstructibleIntegral P.coefficients.l P.extension X.left K.obj ↔
      ∀ i, finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left
        ((P.clopenIntegralPullback (j i)).obj K).obj) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
            K.obj) ⊆ Set.Icc a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((P.clopenIntegralPullback (j i)).obj K).obj) ⊆ Set.Icc a b)) ∧
    (∀ a b : ℤ, a ≤ b →
      ((∀ n : ℕ, Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension X.left n).obj
            K.obj) a b) ↔
        ∀ (i : I) (n : ℕ), Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))
          ((scalarReductionDerivedExtension P.coefficients.l P.extension (Xi i).left n).obj
            ((P.clopenIntegralPullback (j i)).obj K).obj) a b)) := by
  classical
  let l := P.coefficients.l
  let E := P.extension
  let ered (i : I) (n : ℕ) :
      (scalarReductionDerivedExtension l E (Xi i).left n).obj
          ((P.clopenIntegralPullback (j i)).obj K).obj ≅
        (finiteDerivedPullback l E n (j i).left).obj
          ((scalarReductionDerivedExtension l E X.left n).obj K.obj) :=
    (((P.finiteClopen_tensor_and_reduction X Xi j hdisjoint hcover i).2.2.2.2.1 n).some.app K).symm
  have hs (a b : ℤ) (hab : a ≤ b) :
      (∀ n, Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension l E X.left n).obj K.obj) ⊆ Set.Icc a b) ↔
        ∀ i n, Scheme.proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension l E (Xi i).left n).obj
            ((P.clopenIntegralPullback (j i)).obj K).obj) ⊆ Set.Icc a b := by
    constructor
    · intro h i n
      rw [clopenSupport_iso (ered i n)]
      exact (P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n _).2.1 a b hab |>.mp
        (h n) i
    · intro h n
      apply (P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n _).2.1 a b hab |>.mpr
      intro i
      simpa only [clopenSupport_iso (ered i n)] using h i n
  have ht (a b : ℤ) (hab : a ≤ b) :
      (∀ n, Scheme.HasProEtaleTorAmplitude X.left
          (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E X.left n).obj K.obj) a b) ↔
        ∀ i n, Scheme.HasProEtaleTorAmplitude (Xi i).left
          (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E (Xi i).left n).obj
            ((P.clopenIntegralPullback (j i)).obj K).obj) a b := by
    constructor
    · intro h i n
      apply (clopenTor_iso (ered i n) a b).mpr
      exact (P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n _).2.2 a b hab |>.mp
        (h n) i
    · intro h n
      apply (P.finiteClopen_finite_bounds X Xi j hdisjoint hcover n _).2.2 a b hab |>.mpr
      exact fun i ↦ (clopenTor_iso (ered i n) a b).mp (h i n)
  refine ⟨?_, hs, ht⟩
  constructor
  · rintro ⟨_, a, b, hab, h⟩ i
    exact ⟨((P.clopenIntegralPullback (j i)).obj K).property,
      a, b, hab, fun n ↦ (ht a b hab).mp h i n⟩
  · intro h
    choose a b hab hb using fun i ↦ (h i).2
    obtain ⟨c, hc⟩ := (Set.finite_range a).bddBelow
    obtain ⟨d, hd⟩ := (Set.finite_range b).bddAbove
    refine ⟨K.property, min c d, max c d,
      (min_le_left c d).trans (le_max_left c d), ?_⟩
    apply (ht _ _ ((min_le_left c d).trans (le_max_left c d))).mpr
    intro i n
    exact clopenTor_mono (hb i n)
      ((min_le_left c d).trans (hc (Set.mem_range_self i)))
      ((hd (Set.mem_range_self i)).trans (le_max_right c d))


attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Lift the canonical constructible pullback to the integral finite-Tor category.
Source: blueprint finite-clopen argument, step 9
(blueprint: lem-pur-finite-clopen-derived-decomposition). -/
def clopenIntegralTorPullback (i : I) :
    finiteTorConstructibleIntegralCategory P.coefficients.l P.extension X.left ⥤
      finiteTorConstructibleIntegralCategory P.coefficients.l P.extension (Xi i).left :=
  (finiteTorConstructibleIntegral P.coefficients.l P.extension (Xi i).left).lift
    ((finiteTorConstructibleIntegral P.coefficients.l P.extension X.left).ι ⋙
      integralDerivedPullback P.coefficients.l P.extension (j i).left)
    (fun K ↦ (P.finiteClopen_integral_bounds X Xi j hdisjoint hcover
      ⟨K.obj, K.property.1⟩).1.mp K.property i)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Integral, rationalized, and common-stage constructible restriction equivalences.
The finite-Tor field categories are the very same categories by definition.
Source: blueprint section-invariant well-definedness, coefficient transports
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: node steps 9--11. The exact module equivalence preserves every reduction
and the strict Roos construction. Completeness, constructible reductions, and
bounds uniform in the positive level are thus componentwise. Finiteness of I
provides one common interval, both for cohomology and Tor. Restrict the integral
equivalence. Rationalization has unchanged objects and tensors each Hom with E;
finite products commute with that tensor via coordinate insertion and summation.
At the algebraically closed stage choose the finite compositum of all component
fields, glue there, and represent arrows there. Equality is checked after a further
finite compositum, proving full faithfulness and essential surjectivity. The empty
family gives the zero category, equivalent to the empty product category. -/
theorem finiteClopen_constructible_equivalences :
    (Functor.pi' (fun i ↦ P.clopenIntegralPullback (j i))).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenIntegralTorPullback X Xi j
      hdisjoint hcover i)).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenRationalPullback (j i))).IsEquivalence ∧
    (Functor.pi' (fun i ↦ P.clopenCommonStagePullback (j i))).IsEquivalence := by
  sorry

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Scalar extension commutes with the same restrictions, for arbitrary finite
coefficient extensions, including the identity map. Rationalization is compatible
with the integral restriction equivalence.
Source: blueprint coefficient transport, steps 6 and 9--11
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: on strict K-flat representatives the two scalar/restriction composites
have identical pure-tensor maps at every quotient of the target coefficient
ring, with the same transition equations. Restricting Roos gives the natural
integral comparison. The rational comparison is its linear extension, and common
stages compute these same comparisons after a finite compositum. -/
theorem finiteClopen_scalar_extension (i : I)
    (L : Type u) [Field L] [Algebra (Padic P.coefficients.l) L]
    [FiniteDimensional (Padic P.coefficients.l) L]
    (ι : P.extension →ₐ[Padic P.coefficients.l] L) :
    Nonempty
      ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          integralScalarExtension P.coefficients.l P.extension L ι X.left ⋙
          integralDerivedPullback P.coefficients.l L (j i).left ≅
        P.clopenIntegralPullback (j i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι ⋙
          integralScalarExtension P.coefficients.l P.extension L ι (Xi i).left) ∧
    Nonempty (P.clopenIntegralPullback (j i) ⋙
        sfRationalConstructibleLocalization P.coefficients.l P.extension (Xi i).left ≅
      sfRationalConstructibleLocalization P.coefficients.l P.extension X.left ⋙
        P.clopenRationalPullback (j i)) := by
  sorry

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- Restriction preserves the specified coefficient units at every stage.
Source: blueprint coefficient transports, steps 5--6 and 9--11
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: the sheaf-level coefficient ring restricts to the component coefficient
ring, by localization of constant sheafification and sectionwise integral limits.
The regular modules therefore restrict to regular modules. The finite K-flat
and integral strict Roos formulas preserve this identification in degree zero.
Rationalization and the common-stage representative functors preserve these
isomorphisms, with no restriction on the chosen finite coefficient stage. -/
theorem finiteClopen_coefficient_units (i : I) :
    (∀ n : ℕ, Nonempty
      ((finiteDerivedPullback P.coefficients.l P.extension n (j i).left).obj
          (finiteConstantCoefficientObject P.coefficients.l P.extension X.left n) ≅
        finiteConstantCoefficientObject P.coefficients.l P.extension (Xi i).left n)) ∧
    Nonempty ((P.clopenIntegralPullback (j i)).obj (P.clopenIntegralUnit X.left) ≅
      P.clopenIntegralUnit (Xi i).left) ∧
    Nonempty ((P.clopenRationalPullback (j i)).obj (P.clopenRationalUnit X.left) ≅
      P.clopenRationalUnit (Xi i).left) ∧
    ∀ B : AlgebraicallyClosedCoefficients.Index P.coefficients.l P.coefficients.Qbar,
      Nonempty ((P.clopenCommonStagePullback (j i)).obj (P.clopenCommonStageUnit X.left B) ≅
        P.clopenCommonStageUnit (Xi i).left B) := by
  sorry

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The empty family forces the empty scheme and has the terminal product category.
Source: Stacks 04TS and the empty covering sheaf axiom
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: the union of the empty family of images is empty, so the covering condition
makes X empty. Functions on an empty index type and their coordinatewise morphisms
are unique. The preceding equivalences identify each source category with that
product; this includes zero sheaves and complexes, with no chosen nonzero component. -/
theorem finiteClopen_empty [IsEmpty I] (n : ℕ) (integral : Bool) :
    IsEmpty X.left ∧
      Subsingleton (∀ i, clopenModules (Xi i).left
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))) ∧
      ∀ F G : (∀ i, clopenModules (Xi i).left
        (clopenRingRestriction (j i).left (P.clopenRing X.left n integral))),
        Subsingleton (F ⟶ G) := by
  refine ⟨⟨fun x ↦ ?_⟩, inferInstance, fun F G ↦ ⟨fun f g ↦ funext (fun i ↦ isEmptyElim i)⟩⟩
  have hx : x ∈ ⋃ i, Set.range (j i).left := by rw [hcover]; trivial
  obtain ⟨i, _⟩ := Set.mem_iUnion.mp hx
  exact isEmptyElim i

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The finite derived restriction above is the recorded intrinsic inverse image,
after identifying its restricted constant coefficient sheaf with the component's.
The normalization on Q specifies termwise coefficient transport, including maps.
Source: Stacks 00XZ, 04TS, 015F
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: constant sheafification commutes with localization; its unit identifies
constant sections. Transport modules by the inverse ring isomorphism. The
underlying sectionwise restriction is the inverse image for an open immersion.
Its exact termwise descent is the recorded finiteDerivedPullback. -/
theorem finiteClopen_finite_restriction_identification (n : ℕ) (i : I) :
    ∃ (c : clopenRingRestriction (j i).left (P.clopenRing X.left n false) ≅
        integralCoefficientCommRingSheaf P.coefficients.l P.extension (Xi i).left n)
      (e : DerivedCategory (clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left n false))) ≌
        Scheme.proEtaleDerivedCategory (Xi i).left
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))),
      Nonempty (DerivedCategory.Q ⋙ e.functor ≅
        (SheafOfModules.restrictScalars
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            c.inv)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
      Nonempty (clopenDerivedRestriction (j i).left (P.clopenRing X.left n false) ⋙
        e.functor ≅ finiteDerivedPullback P.coefficients.l P.extension n (j i).left) := by
  sorry

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology in
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.hasDerived
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedMonoidal
  AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedSymmetric in
/-- The completed coefficient identification and its constructible comparison.
It relates the module-derived equivalence to the actual completed pullback;
completed pullback on arbitrary unbounded objects is not asserted to be an equivalence.
Source: Stacks 04TS; blueprint integral finite-clopen transport
(blueprint: lem-pur-finite-clopen-derived-decomposition).
Proof: restriction preserves sectionwise inverse limits, so the compatible finite
constant-ring identifications give the completed ring identification. Transport
scalars along its inverse. On complete objects the normalized Roos construction
computes the original restriction, with the original canonical reduction units.
This identifies the two restrictions naturally on the full integral subcategory. -/
theorem finiteClopen_integral_restriction_identification (i : I) :
    ∃ (c : clopenRingRestriction (j i).left (P.clopenRing X.left 0 true) ≅
        completedIntegralCommRingSheafUnrestricted P.coefficients.l P.extension (Xi i).left)
      (e : DerivedCategory (clopenModules (Xi i).left
          (clopenRingRestriction (j i).left (P.clopenRing X.left 0 true))) ≌
        DerivedCategory (scalarReductionSource P.coefficients.l P.extension (Xi i).left)),
      Nonempty (DerivedCategory.Q ⋙ e.functor ≅
        (SheafOfModules.restrictScalars
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            c.inv)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ∧
      Nonempty ((sfIntegralConstructible P.coefficients.l P.extension X.left).ι ⋙
          clopenDerivedRestriction (j i).left (P.clopenRing X.left 0 true) ⋙ e.functor ≅
        P.clopenIntegralPullback (j i) ⋙
          (sfIntegralConstructible P.coefficients.l P.extension (Xi i).left).ι) := by
  sorry

end Decomposition
end PurityFiniteSetting
end WeilConjectures
