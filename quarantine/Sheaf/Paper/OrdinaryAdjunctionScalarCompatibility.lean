/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
Authors: SHEAF group Q55
-/
module

public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.CompletedPullbackAdjunction
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.Paper.CompletedCoefficientPushforwardComparison
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.PbcScalarExtension
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Sheaf.Paper.SfScalarExtensionComposition
import Sheaf.Paper.ProEtaleProjectionFormulaArrows
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.SfIntegralDirectImageConstructible
import Sheaf.Paper.SfDerivedDirectImage
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedCoefficientRestrictionCounit
import Sheaf.Paper.PbcQbarCompletedPullback


/-! # Scalar compatibility of the ordinary completed adjunction

Source: fix-prop-adjunctions.proof.md, Step 1; Stacks 099N, 03D7, 070I
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
The canonical integral Hom equivalence, its scalar comparisons and its raw
rational/common-stage descent are all fixed by the recorded units.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
namespace WeilConjectures
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme TensorProduct
open scoped ChangeOfRings
universe u v
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The strict-tower comparison fixed by its actual completion unit.
Source: Stacks 099N (blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purStrictPullComparison :=
  (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) f).exists.choose

/-- The completed Hom bijection is completion-unit precomposition followed by the
ordinary derived module adjunction, on all complete objects.
Source: Stacks 099N (2),(5)
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: transport the constant-coefficient reflector of
lem-sp-completed-pullback-adjunction through the unit-preserving equivalence
lem-weil-pbc-constant-completion-equivalence. The right-functor comparison of
lem-pur-completed-coefficient-pushforward-comparison identifies its right adjoint
with actual ordinary ringed direct image. The strict-tower comparison preserves
the same completion unit. Precomposition with that unit is bijective for complete
K; compose with the ordinary derived-adjunction bijection. -/
theorem purOrdinaryHom_bijective
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :
    Function.Bijective (fun u :
      (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj ⟶ K.obj =>
        (pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).homEquiv M.obj K.obj
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app M.obj ≫ u)) := by
  sorry

/-- The canonical bijection, with real forward map; its inverse is the unique inverse
of the preceding bijection. Source: Stacks 099N
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purOrdinaryHom
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :
    ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj ⟶ K.obj) ≃
      (M.obj ⟶ (pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K.obj) :=
  Equiv.ofBijective _ (purOrdinaryHom_bijective l E f M K)

/-- Both directions preserve addition and the valuation-ring action.
Source: Stacks 03D7, 070I, 099N
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: the ordinary module adjunct is evaluation at 1 tensor x and its inverse
sends s tensor x to s times that evaluation. Both formulas commute with scalar
multiplication and addition, termwise on K-injective models and through homotopies.
K-injective Hom comparison transfers these identities to derived Hom. Completion
precomposition is linear and bijective, hence its inverse is linear. Restriction
through the constant/completed equivalence preserves the constant scalar action. -/
theorem purOrdinaryHom_linear
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :
    (∀ u w, purOrdinaryHom l E f M K (u + w) =
      purOrdinaryHom l E f M K u + purOrdinaryHom l E f M K w) ∧
    (∀ (r : PbcIntegralRing l E) u, purOrdinaryHom l E f M K (r • u) =
      r • purOrdinaryHom l E f M K u) ∧
    (∀ v w, (purOrdinaryHom l E f M K).symm (v + w) =
      (purOrdinaryHom l E f M K).symm v + (purOrdinaryHom l E f M K).symm w) ∧
    (∀ (r : PbcIntegralRing l E) v, (purOrdinaryHom l E f M K).symm (r • v) =
      r • (purOrdinaryHom l E f M K).symm v) := by
  sorry

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Scalar extension of a complete object, using the published preservation theorem.
Source: Bhatt--Scholze 6.8.2(1)
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purScalarComplete (W : Scheme.{u})
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))) :
    ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l L)) :=
  ⟨(pbcEmbeddingAmbientTensor l E L ι W).obj M.obj,
    pbcScalarPreservesComplete l E L ι W M⟩

/-- The specified a, on strict-tower pullbacks: tensor reassociation and the
unit-compatible completion comparison, conjugated by the strict-tower comparisons.
Source: prop-weil-pbc-scalar-extension, Stacks 099N
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purScalarPullComparison
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E))) :
    (pbcEmbeddingAmbientTensor l E L ι X).obj
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj) ≅
      (pbcActualStrictCompletedPull (pbcIntegralDatum l L) f).obj
        (purScalarComplete l E L ι Y M).obj :=
  (pbcEmbeddingAmbientTensor l E L ι X).mapIso ((purStrictPullComparison l E f).app M) ≪≫
    ((pbcScalarCompletedPullIso l E L ι f).symm.app M.obj) ≪≫
      ((purStrictPullComparison l L f).app (purScalarComplete l E L ι Y M)).symm

/-- The two factorizations of the ringed direct image have the canonical right
comparison. It is the conjugate of the normalized ordinary-derived tensor comparison.
Source: Stacks 0D6E, 03EL
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purScalarRightDerivedComparison :
    pbcActualDerivedPush f (pbcIntegralDatum l L) ⋙
        pbcDerivedRestrict (pbcScalarCoefficientMap l E L ι Y) ≅
      pbcDerivedRestrict (pbcScalarCoefficientMap l E L ι X) ⋙
        pbcActualDerivedPush f (pbcIntegralDatum l E) :=
  conjugateIsoEquiv
    ((pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E L ι Y)).comp
      (pbcActualDerivedAdjunction f (pbcIntegralDatum l L)))
    ((pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).comp
      (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E L ι X)))
    (pbcScalarOrdinaryPullIso l E L ι f).symm

/-- The homotopy comparison is induced by the identity-on-sections ringed comparison.
Source: Stacks 0D6E (blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purScalarRightHomotopyComparison :=
  Functor.mapHomotopyCategoryCompIso
    (pbcActualScalarRightIso f (pbcIntegralDatum l E) (pbcIntegralDatum l L)
      (pbcScalarCoefficientMap l E L ι Y) (pbcScalarCoefficientMap l E L ι X)
      (pbcScalarCoefficientStructureSquare l E L ι f)) (.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso
      (F := pbcRestrict (pbcScalarCoefficientMap l E L ι X))
      (G := pbcActualModulePush f (pbcIntegralDatum l E)) (Iso.refl _) (.up ℤ)).symm

/-- The chosen right comparison has the universal right-derived normalization of
ringed-topos composition, fixing it independently of any f-adjunction mate formula.
Source: Stacks 0D6E, 070I
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: ordinary right comparison is identity on sections for the commuting
structural coefficient square. Restriction is exact and finite-free extension is
exact, so restriction preserves K-injectives. Compute the derived composites on
K-injectives and descend their ordinary identity-on-sections comparison through
the universal derived units. On resolving models the normalized derived tensor
comparison is its adjunction conjugate. Universal uniqueness gives exactly the
displayed equation on all homotopy objects. -/
theorem purScalarRightDerivedComparison_normalization
    (I : HomotopyCategory (pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l L)))
      (.up ℤ)) :
    (pbcDerivedRestrict (pbcScalarCoefficientMap l E L ι Y)).map
        ((pbcActualPushUnit f (pbcIntegralDatum l L)).app I) ≫
      (purScalarRightDerivedComparison l E f L ι).hom.app (DerivedCategory.Qh.obj I) ≫
      (pbcActualDerivedPush f (pbcIntegralDatum l E)).map
        ((pbcRestrict (pbcScalarCoefficientMap l E L ι X)).mapDerivedCategoryFactorsh.hom.app I) =
    (pbcRestrict (pbcScalarCoefficientMap l E L ι Y)).mapDerivedCategoryFactorsh.hom.app
        (((pbcActualModulePush f (pbcIntegralDatum l L)).mapHomotopyCategory (.up ℤ)).obj I) ≫
      DerivedCategory.Qh.map ((purScalarRightHomotopyComparison l E f L ι).hom.app I) ≫
      (pbcActualPushUnit f (pbcIntegralDatum l E)).app
        (((pbcRestrict (pbcScalarCoefficientMap l E L ι X)).mapHomotopyCategory
          (.up ℤ)).obj I) := by
  sorry

/-- The specified b is the coefficient-adjunction transpose of F_E of the actual
coefficient unit, followed by inverse d. Thus b is not substituted by an arbitrary
isomorphism or fixed solely by the desired f-adjunction scalar equation.
Source: fix-prop-adjunctions Step 1; Stacks 03EK, 0D6E
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: at ordinary module level both transposes send m tensor s to s times the
counit image of m. On K-injective targets coefficient restriction remains
K-injective by exactness of finite-free scalar extension. Derived Hom comparison
therefore transfers this tensor calculation, with the normalization of d just
stated, to actual derived maps. Equivalently paste the two tensor-unit-normalized
adjunction squares; the two paths to the structural map are identical. This
identifies the published projection mate with the coefficient-unit definition. -/
theorem purScalarDirectImage_coefficientAdjunct
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E L ι Y)).homEquiv _ _
        ((pbcScalarDirectImageIso l E L ι f).hom.app K) =
      (pbcActualDerivedPush f (pbcIntegralDatum l E)).map
          ((pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E L ι X)).unit.app K) ≫
        (purScalarRightDerivedComparison l E f L ι).inv.app
          ((pbcEmbeddingAmbientTensor l E L ι X).obj K) := by
  sorry

/-- The linear equivalence underlying the fixed completed Hom bijection.
Source: Stacks 03D7, 099N
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purOrdinaryHomLinear
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :
    ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj ⟶ K.obj) ≃ₗ[
      PbcIntegralRing l E] (M.obj ⟶ (pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K.obj) :=
  { purOrdinaryHom l E f M K with
    map_add' := (purOrdinaryHom_linear l E f M K).1
    map_smul' := (purOrdinaryHom_linear l E f M K).2.1 }

/-- Raw localization of the fixed linear Hom equivalence, uniquely normalized on tensors.
Source: fix-prop-adjunctions Step 1
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: tensor purOrdinaryHomLinear and its inverse with the fraction ring.
Their composites fix every pure tensor and therefore every finite sum of tensors.
The displayed formula determines the map uniquely by the tensor universal property. -/
theorem purRationalHom_existsUnique
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :
    ∃! h : (Localization.Away (pbcUniformizer l E) ⊗[PbcIntegralRing l E]
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj ⟶ K.obj)) ≃ₗ[
          Localization.Away (pbcUniformizer l E)]
        (Localization.Away (pbcUniformizer l E) ⊗[PbcIntegralRing l E]
          (M.obj ⟶ (pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K.obj)),
      ∀ a u, h (a ⊗ₜ u) = a ⊗ₜ purOrdinaryHom l E f M K u := by
  sorry

/-- The raw localized canonical adjunction, uniquely fixed on every pure tensor.
Source: fix-prop-adjunctions Step 1
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purRationalHom
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :=
  (purRationalHom_existsUnique l E f M K).exists.choose

/-- The scalar map on the actual localized coefficient rings, including denominators.
Source: fix-prop-adjunctions Step 1
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purLocalizedCoefficientMap : Localization.Away (pbcUniformizer l E) →+*
    Localization.Away (pbcUniformizer l L) :=
  (pbcRationalCoefficientEquiv l L).symm.toRingHom.comp
    (ι.toRingHom.comp (pbcRationalCoefficientEquiv l E).toRingHom)

/-- The two maps induced by rational scalar extension, conjugating the source by a
and the target by b. They are fixed on all pure tensors, not only integral maps.
Source: fix-prop-adjunctions Step 1, rational passage
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: tensor the actual integral source and target maps with the coefficient
inclusion. Their semilinearity follows from the coefficient ring map. The image
of the source uniformizer is a unit times a positive power of the target one,
so every source denominator is invertible after target localization. Thus the
balanced maps descend to the displayed localized tensor groups. Pure tensors
generate, so their formulas determine both additive maps uniquely. -/
theorem purRationalScalarMaps_existsUnique
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :
    ∃! c :
      ((Localization.Away (pbcUniformizer l E) ⊗[PbcIntegralRing l E]
          ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj ⟶ K.obj)) →+
        (Localization.Away (pbcUniformizer l L) ⊗[PbcIntegralRing l L]
          ((pbcActualStrictCompletedPull (pbcIntegralDatum l L) f).obj
            (purScalarComplete l E L ι Y M).obj ⟶ (purScalarComplete l E L ι X K).obj))) ×
      ((Localization.Away (pbcUniformizer l E) ⊗[PbcIntegralRing l E]
          (M.obj ⟶ (pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K.obj)) →+
        (Localization.Away (pbcUniformizer l L) ⊗[PbcIntegralRing l L]
          ((purScalarComplete l E L ι Y M).obj ⟶
            (pbcActualDerivedPush f (pbcIntegralDatum l L)).obj
              (purScalarComplete l E L ι X K).obj))),
      (∀ a u, c.1 (a ⊗ₜ u) = purLocalizedCoefficientMap l E L ι a ⊗ₜ
        ((purScalarPullComparison l E f L ι M).inv ≫
          (pbcEmbeddingAmbientTensor l E L ι X).map u)) ∧
      (∀ a v, c.2 (a ⊗ₜ v) = purLocalizedCoefficientMap l E L ι a ⊗ₜ
        ((pbcEmbeddingAmbientTensor l E L ι Y).map v ≫
          (pbcScalarDirectImageIso l E L ι f).hom.app K.obj)) := by
  sorry

/-- The uniquely prescribed pair of rational scalar maps.
Source: fix-prop-adjunctions Step 1
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purRationalScalarMaps
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :=
  (purRationalScalarMaps_existsUnique l E f L ι M K).exists.choose


/-- Scalar compatibility of both canonical ordinary completed adjunct operations.
The two displayed equations use exactly a and b fixed by the source.
Source: fix-prop-adjunctions.proof.md Step 1; Stacks 099N, 03D7, 070I
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: finite freeness identifies completed coefficient change with ordinary tensor;
the two uniformizer filtrations are cofinal. On constant coefficients, test the
projection comparison through the coefficient adjunction x maps to x tensor 1.
The two orders of adjunct agree on tensor generators. K-injective targets and
exact finite-free restriction transfer this to derived Hom, without assuming
faithfulness of restriction. The two structural-ring factorizations identify the
specified b through the normalized direct-image comparison. The finite-free scalar
comparison preserves the actual completion units, so precomposition with that unit
identifies the transpose of b with C of the E-counit followed by a inverse. Its
injectivity gives this equality before completion. Naturality of inverse adjuncts
then gives the inverse equation for any v, and applying the L-bijection gives the
forward equation for any u. This is the DAG proof, steps 4--9. -/
theorem purOrdinaryAdjunctionScalarCompatibility
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :
    (∀ u : (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj ⟶ K.obj,
      purOrdinaryHom l L f (purScalarComplete l E L ι Y M) (purScalarComplete l E L ι X K)
          ((purScalarPullComparison l E f L ι M).inv ≫
            (pbcEmbeddingAmbientTensor l E L ι X).map u) =
        (pbcEmbeddingAmbientTensor l E L ι Y).map (purOrdinaryHom l E f M K u) ≫
          (pbcScalarDirectImageIso l E L ι f).hom.app K.obj) ∧
    (∀ v : M.obj ⟶ (pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K.obj,
      (purOrdinaryHom l L f (purScalarComplete l E L ι Y M)
          (purScalarComplete l E L ι X K)).symm
          ((pbcEmbeddingAmbientTensor l E L ι Y).map v ≫
            (pbcScalarDirectImageIso l E L ι f).hom.app K.obj) =
        (purScalarPullComparison l E f L ι M).inv ≫
          (pbcEmbeddingAmbientTensor l E L ι X).map ((purOrdinaryHom l E f M K).symm v)) := by
  sorry


/-- The forward and inverse scalar equations for every localized morphism.
Source: fix-prop-adjunctions Step 1
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: on a pure tensor both assertions are the integral scalar equations tensored
with its scalar, viewed in L. Additivity proves them for finite sums of tensors,
which exhaust each localized Hom group. The inverse formula also follows by
applying the inverse L-bijection to the forward equality. -/
theorem purRationalAdjunctionScalarCompatibility
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :
    (∀ u, purRationalHom l L f (purScalarComplete l E L ι Y M)
        (purScalarComplete l E L ι X K) ((purRationalScalarMaps l E f L ι M K).1 u) =
      (purRationalScalarMaps l E f L ι M K).2 (purRationalHom l E f M K u)) ∧
    (∀ v, (purRationalHom l L f (purScalarComplete l E L ι Y M)
        (purScalarComplete l E L ι X K)).symm ((purRationalScalarMaps l E f L ι M K).2 v) =
      (purRationalScalarMaps l E f L ι M K).1 ((purRationalHom l E f M K).symm v)) := by
  sorry

/-- Identity extension respects both of the specified comparisons.
Source: fix-prop-adjunctions Step 1; prop-weil-pbc-scalar-extension
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: ordinary scalar extension by the identity has the multiplication unit.
Its right-adjoint comparison is identity on sections, so its mate is that unit.
The completion comparisons preserve the quotient unit and are uniquely fixed by
it. Conjugating by the strict-tower comparisons gives the first equation. The
same mate unit equation gives the second. -/
theorem purOrdinaryAdjunctionScalar_identity
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :
    (purScalarPullComparison l E f E (AlgHom.id ℚ_[l] E) M).hom ≫
        (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).map
          ((pbcEmbeddingAmbientUnit l E Y).hom.app M.obj) =
      (pbcEmbeddingAmbientUnit l E X).hom.app
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj) ∧
    (pbcScalarDirectImageIso l E E (AlgHom.id ℚ_[l] E) f).hom.app K.obj ≫
        (pbcActualDerivedPush f (pbcIntegralDatum l E)).map
          ((pbcEmbeddingAmbientUnit l E X).hom.app K.obj) =
      (pbcEmbeddingAmbientUnit l E Y).hom.app
        ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K.obj) := by
  sorry

variable (N : Type u) [Field N] [Algebra ℚ_[l] N] [FiniteDimensional ℚ_[l] N]
  (j : L →ₐ[ℚ_[l]] N)

/-- The direct and iterated a and b agree through the actual balanced tensor
associators. These are precisely the conjugations in the scalar Hom equations.
Source: fix-prop-adjunctions Step 1; prop-weil-pbc-scalar-extension
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: tensor reassociation sends c tensor (b tensor x) to c*j(b) tensor x in
both orders. Conjugating with the specified chi maps cancels intermediate
inverse pairs by naturality. Completion-unit uniqueness gives the same equation
for completed pullbacks. Mate pasting gives the direct-image equation. The
ordinary balanced tensor pentagon makes these equations independent of the
parenthesization of every longer tower. -/
theorem purOrdinaryAdjunctionScalar_tower
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :
    (pbcEmbeddingAmbientTensor l L N j X).map
        ((purScalarPullComparison l E f L ι M).hom) ≫
      (purScalarPullComparison l L f N j (purScalarComplete l E L ι Y M)).hom ≫
      (pbcActualStrictCompletedPull (pbcIntegralDatum l N) f).map
        ((pbcAmbientScalarComp l E L N ι j Y).hom.app M.obj) =
    (pbcAmbientScalarComp l E L N ι j X).hom.app
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj) ≫
      (purScalarPullComparison l E f N (j.comp ι) M).hom ∧
    (pbcEmbeddingAmbientTensor l L N j Y).map
        ((pbcScalarDirectImageIso l E L ι f).hom.app K.obj) ≫
      (pbcScalarDirectImageIso l L N j f).hom.app
        ((pbcEmbeddingAmbientTensor l E L ι X).obj K.obj) ≫
      (pbcActualDerivedPush f (pbcIntegralDatum l N)).map
        ((pbcAmbientScalarComp l E L N ι j X).hom.app K.obj) =
    (pbcAmbientScalarComp l E L N ι j Y).hom.app
        ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K.obj) ≫
      (pbcScalarDirectImageIso l E N (j.comp ι) f).hom.app K.obj := by
  sorry

/-- The actual localized bounded constructible Hom groups in the recorded intrinsic
category identify with the tensor groups used above, through coefficient restriction.
The formula specifies this identification on every rational tensor.
Source: def-weil-rationalization-karoubi; Stacks 099N
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: coefficient restriction is an exact equivalence and is linear for the
constant scalar actions, with ULift.ringEquiv converting the coefficient rings.
It is fully faithful on the full bounded subcategories. Tensor this Hom
identification with the fraction fields; the displayed normalized fraction maps
convert the two localized scalar rings. The tensor universal property gives
inverse additive maps, and generation by pure tensors gives uniqueness. -/
theorem purRationalModelHom_existsUnique (W : Scheme.{u})
    (A B : PbcCompletedDerived W (pbcIntegralDatum l E))
    (hA : sfIntegralConstructible l E W ((purCoefficientModel l E W).functor.obj A))
    (hB : sfIntegralConstructible l E W ((purCoefficientModel l E W).functor.obj B)) :
    ∃! e : (Localization.Away (pbcUniformizer l E) ⊗[PbcIntegralRing l E] (A ⟶ B)) ≃+
      ((sfRationalConstructibleLocalization l E W).obj
          ⟨(purCoefficientModel l E W).functor.obj A, hA⟩ ⟶
        (sfRationalConstructibleLocalization l E W).obj
          ⟨(purCoefficientModel l E W).functor.obj B, hB⟩),
      ∀ a g, e (a ⊗ₜ g) =
        ((sfRationalCoefficientEquiv l E).symm (pbcRationalCoefficientEquiv l E a)) ⊗ₜ
          (ObjectProperty.homMk ((purCoefficientModel l E W).functor.map g)) := by
  sorry

/-- Canonical coordinates in the actual raw constructible rational category.
Source: def-weil-rationalization-karoubi
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
@[irreducible]
def purRationalModelHom (W : Scheme.{u})
    (A B : PbcCompletedDerived W (pbcIntegralDatum l E))
    (hA : sfIntegralConstructible l E W ((purCoefficientModel l E W).functor.obj A))
    (hB : sfIntegralConstructible l E W ((purCoefficientModel l E W).functor.obj B)) :=
  (purRationalModelHom_existsUnique l E W A B hA hB).exists.choose

/-- All endpoint objects in the two scalar Hom equations lie in the recorded bounded
constructible categories, under exactly the geometric hypotheses of the node.
The given k-structures on X and Y need not make f a k-morphism.
Source: fix-prop-adjunctions Step 1; Stacks 099N
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: the finite-field datum makes k algebraically closed of characteristic p.
Finite-type k-schemes are Noetherian and finite dimensional, and l is invertible.
For the constructible direct-image input give X the composite k-structure through
f and Y; finite-type composition verifies its hypothesis and leaves all sites and
coefficient sheaves unchanged. Integral operations preserve constructibility, and
the completed-coefficient pushforward comparison identifies tower direct image
with the actual ordinary direct image. Finite-free scalar extension preserves the
same bounded constructible category. The canonical coefficient-model equivalence
identifies these conditions with sfIntegralConstructible, including the common
interval for every reduction. Fullness therefore restricts the Hom bijections,
and the tensor Hom coordinates above identify their raw rationalizations. -/
theorem purOrdinaryAdjunctionScalar_bounded
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E)))
    (hM : sfIntegralConstructible l E Y ((purCoefficientModel l E Y).functor.obj M.obj))
    (hK : sfIntegralConstructible l E X ((purCoefficientModel l E X).functor.obj K.obj)) :
    sfIntegralConstructible l E X ((purCoefficientModel l E X).functor.obj
      ((pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj)) ∧
    sfIntegralConstructible l E Y ((purCoefficientModel l E Y).functor.obj
      ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K.obj)) ∧
    sfIntegralConstructible l L Y ((purCoefficientModel l L Y).functor.obj
      (purScalarComplete l E L ι Y M).obj) ∧
    sfIntegralConstructible l L X ((purCoefficientModel l L X).functor.obj
      (purScalarComplete l E L ι X K).obj) := by
  sorry

/-- The coefficient-model comparisons preserve the actual balanced tensor associator
and multiplication unit. After conjugating by sfIntegralOrdinaryComparison and
localizing, these are exactly sfRationalScalarComp and sfRationalScalarUnit used
by the recorded common-stage construction.
Source: fix-prop-adjunctions Step 1; lem-weil-scalar-extension-composition
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: evaluate the ordinary comparisons on pure tensor generators. Both triple
routes send c tensor (b tensor x) to c*j(b) tensor x, and the unit sends a tensor
x to a*x. Their universal derived counits descend these identities. Conjugating
by chi moves each intermediate chi by naturality and cancels it with its inverse.
The same balanced map remains. Tensoring components with one gives precisely the
normalized rational associator and unit of sfRationalScalarComp, including its
pentagon, rather than an arbitrary comparison between the same endpoints. -/
theorem purScalarModel_coherence (W : Scheme.{u})
    (K : PbcCompletedDerived W (pbcIntegralDatum l E)) :
    (purCoefficientModel l N W).functor.map
        ((pbcAmbientScalarComp l E L N ι j W).hom.app K) ≫
      (purScalarModel l E N (j.comp ι) W).hom.app K =
    (purScalarModel l L N j W).hom.app ((pbcEmbeddingAmbientTensor l E L ι W).obj K) ≫
      (integralOrdinaryDerivedScalar l L N j W).map
        ((purScalarModel l E L ι W).hom.app K) ≫
      (integralOrdinaryDerivedScalarComp l E L ι W N j).hom.app
        ((purCoefficientModel l E W).functor.obj K) ∧
    (purScalarModel l E E (AlgHom.id ℚ_[l] E) W).hom.app K ≫
      (integralOrdinaryDerivedScalarUnit l E W).hom.app
        ((purCoefficientModel l E W).functor.obj K) =
    (purCoefficientModel l E W).functor.map ((pbcEmbeddingAmbientUnit l E W).hom.app K) := by
  sorry

section CommonStage
open AlgebraicallyClosedCoefficients (Coefficient coefficientInclusion)
variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- Equality after a further finite coefficient extension for source representatives.
This is the defining common-stage relation, using the specified a comparison.
Source: def-weil-algebraically-closed-coefficients, fix-prop-adjunctions Step 1
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purCommonStageSourceRelated
    (A : Padic.FiniteCoefficientFields l Ω)
    (M : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l (Coefficient.{u} l Ω A))))
    (K : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l (Coefficient.{u} l Ω A))))
    (s t :
      Localization.Away (pbcUniformizer l (Coefficient.{u} l Ω A))
        ⊗[PbcIntegralRing l (Coefficient.{u} l Ω A)]
        ((pbcActualStrictCompletedPull (pbcIntegralDatum l (Coefficient.{u} l Ω A)) f).obj
          M.obj ⟶ K.obj)) : Prop :=
  ∃ (B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B),
    (purRationalScalarMaps l (Coefficient.{u} l Ω A) f (Coefficient.{u} l Ω B)
      (coefficientInclusion l Ω A B h) M K).1 s =
    (purRationalScalarMaps l (Coefficient.{u} l Ω A) f (Coefficient.{u} l Ω B)
      (coefficientInclusion l Ω A B h) M K).1 t

/-- Equality after a further finite coefficient extension for target representatives.
This is the defining common-stage relation, using the specified b comparison.
Source: def-weil-algebraically-closed-coefficients, fix-prop-adjunctions Step 1
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purCommonStageTargetRelated
    (A : Padic.FiniteCoefficientFields l Ω)
    (M : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l (Coefficient.{u} l Ω A))))
    (K : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l (Coefficient.{u} l Ω A))))
    (s t :
      Localization.Away (pbcUniformizer l (Coefficient.{u} l Ω A))
        ⊗[PbcIntegralRing l (Coefficient.{u} l Ω A)]
        (M.obj ⟶ (pbcActualDerivedPush f (pbcIntegralDatum l (Coefficient.{u} l Ω A))).obj
          K.obj)) : Prop :=
  ∃ (B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B),
    (purRationalScalarMaps l (Coefficient.{u} l Ω A) f (Coefficient.{u} l Ω B)
      (coefficientInclusion l Ω A B h) M K).2 s =
    (purRationalScalarMaps l (Coefficient.{u} l Ω A) f (Coefficient.{u} l Ω B)
      (coefficientInclusion l Ω A B h) M K).2 t

/-- The defining common-stage equivalence relation is preserved and reflected by
adjuncts and inverse adjuncts. Any two representatives may first be brought to
one common finite field A; the displayed existentials are exactly agreement
after a further common extension. Both implications retain that very extension.
Source: def-weil-algebraically-closed-coefficients, fix-prop-adjunctions Step 1
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility).
Proof: use the canonical coefficient models Coefficient and coefficientInclusion
from the recorded common-stage construction. Its tensor associators are identified
with the ordinary balanced tensor associators by purScalarModel_coherence and the
chi normalization. Over every further stage B, the rational compatibility equation
intertwines the two representative transports. Apply the injective B-adjunction
bijection to test equality: transported source representatives agree if and only
if their transported adjuncts agree. The inverse statement follows identically
using the inverse B-bijection. The same B works in either direction. Every Hom
has a representative over a common finite field, and equality is agreement after
a further common extension by GeneralAlgebraicallyClosedCoefficients.representatives.
Hence these criteria give representative-independent adjunct and inverse-adjunct
maps on exactly its Hom sets. Identity and tower coherence proved above make the
choice of the first common field immaterial; no faithful scalar restriction or
integral numerator for a rational morphism is assumed. -/
theorem purOrdinaryAdjunction_commonStage
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (A : Padic.FiniteCoefficientFields l Ω)
    (M : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l (Coefficient.{u} l Ω A))))
    (K : ObjectProperty.FullSubcategory
      (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l (Coefficient.{u} l Ω A)))) :
    (∀ s t, purCommonStageSourceRelated l f Ω A M K s t ↔
      purCommonStageTargetRelated l f Ω A M K
        (purRationalHom l (Coefficient.{u} l Ω A) f M K s)
        (purRationalHom l (Coefficient.{u} l Ω A) f M K t)) ∧
    (∀ s t, purCommonStageTargetRelated l f Ω A M K s t ↔
      purCommonStageSourceRelated l f Ω A M K
        ((purRationalHom l (Coefficient.{u} l Ω A) f M K).symm s)
        ((purRationalHom l (Coefficient.{u} l Ω A) f M K).symm t)) := by
  sorry

end CommonStage
end WeilConjectures
