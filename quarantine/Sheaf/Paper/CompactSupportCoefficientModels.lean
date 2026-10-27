/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Sheaf.Paper.CompletedConstantPresentationTransport
public import Sheaf.Paper.NativeConstantSupportModel
public import Sheaf.Paper.ConstantScalarTowerAdjunction
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis
import Sheaf.NumberTheory.Padics.AdicLimitFiniteModules
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Quotient
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.Paper.PurAdicScalarExtensionTorBound
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import all Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
import all Sheaf.Paper.SiteDerivedTensorRestriction
import Sheaf.Paper.CompactSupportCoefficientModelsOrdinaryExistence

/-! # Compatible coefficient models for integral compact support

Source: Bhatt--Scholze, Definition 6.7.6 and Lemmas 6.7.7, 6.8.2(1);
Weil blueprint, purity transport, coefficient extension step
(blueprint: lem-pur-compact-support-coefficient-models).

The arithmetic basis is fixed before passing to quotients. The scalar comparisons
are the published normalized comparisons, and the arbitrary ramified quotient is
handled by derived tensor balancing rather than a flatness assumption.
The native associator and unit clause is not restated: it is the proved
`RingedDerivedNative.associator_square`, `leftUnitor_square` and `rightUnitor_square`
of the cited node lem-sf-ringed-derived-native-tensor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] WeilConjectures.completedScalarComparison
  WeilConjectures.completedScalarChainComparison
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.completedAdicChangeData
attribute [local irreducible] CochainComplex.mapBifunctorSingle₂Iso
  CochainComplex.mapBifunctorSingle₁Iso
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped BigOperators
namespace WeilConjectures
open ConstantCompletion

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The existing Noetherian proof for the actual lifted valuation ring.
Source: Bhatt--Scholze 6.8.2(1), coefficient-model arithmetic
(blueprint: lem-pur-compact-support-coefficient-models). -/
instance compactSupportCoefficientModels_noetherian : IsNoetherianRing (PbcIntegralRing l E) :=
  (pbcIntegralDatum l E).noetherian

/-- Restriction identifies the complete categories, strict quotient towers (including
transitions), and total right-derived limits. The small-site equivalence retains the
original pro-etale site's distinct object and morphism universes.
Source: Stacks 099I, 099L, 093M; Bhatt--Scholze 6.7.6
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: the actual coefficient datum is Noetherian. The scalar-preserving small-site
transport identifies its projections and quotient transitions with the constant-completion
model. Apply the constant-completion equivalence, its normalized strict reduction-tower
comparison and its right-derived limit restriction. Their K-flat and K-injective
computation comparisons fix the isomorphisms, not just their objectwise classes. -/
theorem compactSupportCoefficientModels_constant (W : Scheme.{u}) :
    Nonempty (CompletedConstantPresentationData W (pbcIntegralDatum l E)) ∧
    (∃ q : ObjectProperty.FullSubcategory (ConstantCompletion.IsComplete
          (ConstantCompletion.projection (completedCechTopology W) (PbcIntegralRing l E)
            (pbcIntegralDatum l E).ideal 0)) ≌
        ObjectProperty.FullSubcategory (ConstantCompletion.IsComplete
          (ConstantCompletion.quotient (completedCechTopology W) (PbcIntegralRing l E)
            (pbcIntegralDatum l E).ideal 0)),
      Nonempty (q.functor ⋙ ObjectProperty.ι (ConstantCompletion.IsComplete
          (ConstantCompletion.quotient (completedCechTopology W) (PbcIntegralRing l E)
            (pbcIntegralDatum l E).ideal 0)) ≅
        ObjectProperty.ι (ConstantCompletion.IsComplete
          (ConstantCompletion.projection (completedCechTopology W) (PbcIntegralRing l E)
            (pbcIntegralDatum l E).ideal 0)) ⋙
          ConstantCompletion.dres (ConstantCompletion.coefficientMap
            (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal))) ∧
    Nonempty (ConstantCompletion.dres (ConstantCompletion.coefficientMap
        (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal) ⋙
      (ConstantCompletion.quotientPresentation (completedCechTopology W)
        (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal false).tower ≅
      (ConstantCompletion.quotientPresentation (completedCechTopology W)
        (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal true).tower ⋙
        ConstantCompletion.tdres (ConstantCompletion.coefficientMap
          (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal)) ∧
    Nonempty (ConstantCompletion.rlim (ConstantCompletion.completed
        (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal) ⋙
      ConstantCompletion.dres (ConstantCompletion.coefficientMap
        (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal) ≅
      ConstantCompletion.tdres (ConstantCompletion.coefficientMap
        (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal) ⋙
      ConstantCompletion.rlim (ConstantCompletion.constant
        (completedCechTopology W) (PbcIntegralRing l E))) := by
  refine ⟨completed_constant_presentation_transport W (pbcIntegralDatum l E),
    ConstantCompletion.equivalence (completedCechTopology W) (PbcIntegralRing l E)
      (pbcIntegralDatum l E).ideal, ?_, ?_⟩
  · obtain ⟨e, _⟩ := ConstantCompletion.derivedReductionTowerComparison
      (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal
    exact ⟨e⟩
  · obtain ⟨e, _⟩ := ConstantCompletion.derivedLimitRestriction
      (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal
    exact ⟨e⟩

/-- The normalized strict quotient-tower identification, including every transition.
Source: Stacks 099L, 06YY, 0940; Bhatt--Scholze 6.7.6
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: transport the actual quotient diagrams to the canonical small site. Apply the
constant-completion theorem to the Noetherian integral coefficient datum. On K-flat
complexes the scalar insertions give the tower square; on K-injective strict towers
restriction carries the limit computation to the ordinary coordinatewise limit.
The universal derived comparisons give precisely the displayed normalization. -/
theorem compactSupportCoefficientModels_constantTower (W : Scheme.{u}) :
    ∃ e : dres (coefficientMap (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum
      l E).ideal) ⋙ (quotientPresentation (completedCechTopology W) (PbcIntegralRing l E)
      (pbcIntegralDatum l E).ideal false).tower ≅
        (quotientPresentation (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum
      l E).ideal true).tower ⋙ tdres (coefficientMap (completedCechTopology W) (PbcIntegralRing
      l E) (pbcIntegralDatum l E).ideal),
      ∀ P : Cx (completed (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l
      E).ideal), P.IsAcyclicTensorKFlat →
        (∀ q : ℤ, SheafOfModules.IsFlat (P.X q)) →
        DerivedTowerComparisonFormula (resFactors (coefficientMap (completedCechTopology W)
      (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal))
          (quotientPresentation (completedCechTopology W) (PbcIntegralRing l E)
      (pbcIntegralDatum l E).ideal false).comparison (reductionTowerComparisonComplex
      (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal)
          (tresFactors (coefficientMap (completedCechTopology W) (PbcIntegralRing l E)
      (pbcIntegralDatum l E).ideal))
          (quotientPresentation (completedCechTopology W) (PbcIntegralRing l E)
      (pbcIntegralDatum l E).ideal true).comparison e P := by
  exact ConstantCompletion.derivedReductionTowerComparison
    (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal

/-- Restriction preserves the actual total right-derived inverse limit and its counit.
Source: Stacks 099L, 06YY, 0940; Bhatt--Scholze 6.7.6
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: transport the actual quotient diagrams to the canonical small site. Apply the
constant-completion theorem to the Noetherian integral coefficient datum. On K-flat
complexes the scalar insertions give the tower square; on K-injective strict towers
restriction carries the limit computation to the ordinary coordinatewise limit.
The universal derived comparisons give precisely the displayed normalization. -/
theorem compactSupportCoefficientModels_constantLimit (W : Scheme.{u}) :
    ∃ e : rlim (completed (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l
      E).ideal) ⋙ dres (coefficientMap (completedCechTopology W) (PbcIntegralRing l E)
      (pbcIntegralDatum l E).ideal) ≅
        tdres (coefficientMap (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum
      l E).ideal) ⋙ rlim (constant (completedCechTopology W) (PbcIntegralRing l E)),
      ∀ P : CochainComplex (ℕᵒᵖ ⥤ Mod (completed (completedCechTopology W) (PbcIntegralRing l E)
      (pbcIntegralDatum l E).ideal)) ℤ,
        (dres (coefficientMap (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum
      l E).ideal)).map ((limitComparison (completed (completedCechTopology W) (PbcIntegralRing l
      E) (pbcIntegralDatum l E).ideal)).app P) ≫
          e.hom.app ((TQ (completed (completedCechTopology W) (PbcIntegralRing l E)
      (pbcIntegralDatum l E).ideal)).obj P) =
        (resFactors (coefficientMap (completedCechTopology W) (PbcIntegralRing l E)
      (pbcIntegralDatum l E).ideal)).inv.app
            ((ordinaryLimit (completed (completedCechTopology W) (PbcIntegralRing l E)
      (pbcIntegralDatum l E).ideal)).obj P) ≫
          (Q (constant (completedCechTopology W) (PbcIntegralRing l E))).map ((limitRestriction
      (coefficientMap (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l
      E).ideal)).hom.app P) ≫
          (limitComparison (constant (completedCechTopology W) (PbcIntegralRing l E))).app
            (((tres (coefficientMap (completedCechTopology W) (PbcIntegralRing l E)
      (pbcIntegralDatum l E).ideal)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          (rlim (constant (completedCechTopology W) (PbcIntegralRing l E))).map ((tresFactors
      (coefficientMap (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l
      E).ideal)).hom.app P) := by
  exact ConstantCompletion.derivedLimitRestriction
    (completedCechTopology W) (PbcIntegralRing l E) (pbcIntegralDatum l E).ideal

private theorem coefficientExtensionTensor_naturality
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    [HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1}]
    [(ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (φ : R ⟶ S) {M N : pbcModules W R} (f : M ⟶ N)
    (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((pbcExtend φ).map f).val.app U (pbcTensorSection φ M U s x) =
      pbcTensorSection φ N U s (f.val.app U x) := by
  exact witnessTensor_naturality φ (pbcExtend φ)
    (pbcExtensionExistence φ).choose_spec.choose
    (pbcExtensionExistence φ).choose_spec.choose_spec.choose f U s x

/-- In the constant model completed scalar extension is ordinary tensor with B.
Its normalization uses every local scalar, and is independent of the chosen basis.
Source: Stacks 03EK, 099L; Bhatt--Scholze 6.8.2(1)
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: a single integral basis identifies B with A^r and its completion with the
r-fold completed module. The scalar-inclusion square makes the tensor map balanced.
Map `b tensor x` to `completion(b) tensor x`; the coordinate identification proves it
invertible. Local tensor generators prove uniqueness. Exactness and the K-flat
computation counits transport this ordinary identification to derived complete objects. -/
theorem compactSupportCoefficientModels_ordinary (W : Scheme.{u}) :
    ∃! β : PurStrictScalar.constantRestriction l E W ⋙
        pbcExtend (PurStrictScalar.constantMap l E F i W) ≅
      pbcExtend (completedCoefficientMap l E F i W) ⋙
        PurStrictScalar.constantRestriction l F W,
      ∀ (M : scalarReductionSource l E W) (U : W.ProEtᵒᵖ)
        (b : ((PurStrictScalar.constants l F).ring W).obj.obj U) (x : M.val.obj U),
        (β.hom.app M).val.app U
            (pbcTensorSection (PurStrictScalar.constantMap l E F i W)
              ((PurStrictScalar.constantRestriction l E W).obj M) U b x) =
          pbcTensorSection (completedCoefficientMap l E F i W) M U
            (((integralConstantToCompletionOfUniverses l F W).hom.app U) b) x := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} W
  classical
  choose β hβ using compactSupportCoefficientModels_ordinary_exists l E F i W
  let γ : PurStrictScalar.constantRestriction l E W ⋙
      pbcExtend (PurStrictScalar.constantMap l E F i W) ≅
      pbcExtend (completedCoefficientMap l E F i W) ⋙
        PurStrictScalar.constantRestriction l F W :=
    NatIso.ofComponents β (by
      intro M N f
      let h := (pbcExtensionExistence
        (PurStrictScalar.constantMap l E F i W)).choose_spec.choose
          ((PurStrictScalar.constantRestriction l E W).obj M)
      apply (cancel_epi (eqToHom h.symm)).mp
      apply SheafOfModules.tensor_generator_ext.{u + 1, u, u + 1}
        (PurStrictScalar.constantMap l E F i W)
      intro U x b
      change (β N).hom.val.app U
          (((pbcExtend (PurStrictScalar.constantMap l E F i W)).map
            ((PurStrictScalar.constantRestriction l E W).map f)).val.app U
              (pbcTensorSection (PurStrictScalar.constantMap l E F i W)
                ((PurStrictScalar.constantRestriction l E W).obj M) U b x)) =
        ((pbcExtend (completedCoefficientMap l E F i W)).map f).val.app U
          ((β M).hom.val.app U
            (pbcTensorSection (PurStrictScalar.constantMap l E F i W)
              ((PurStrictScalar.constantRestriction l E W).obj M) U b x))
      let c := ((integralConstantToCompletionOfUniverses l F W).hom.app U) b
      exact (congrArg ((β N).hom.val.app U)
        (coefficientExtensionTensor_naturality W
          (PurStrictScalar.constantMap l E F i W)
          ((PurStrictScalar.constantRestriction l E W).map f) U b x)).trans
        ((hβ N U b (f.val.app U x)).trans
          ((coefficientExtensionTensor_naturality W
            (completedCoefficientMap l E F i W) f U c x).symm.trans
            (congrArg
              (((pbcExtend (completedCoefficientMap l E F i W)).map f).val.app U)
              (hβ M U b x).symm))))
  refine ⟨γ, hβ, ?_⟩
  intro β' hβ'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let h : (pbcExtend (PurStrictScalar.constantMap l E F i W)).obj
      ((PurStrictScalar.constantRestriction l E W).obj M) =
      SheafOfModules.changeOfRings (PurStrictScalar.constantMap l E F i W)
        ((PurStrictScalar.constantRestriction l E W).obj M) :=
    (pbcExtensionExistence (PurStrictScalar.constantMap l E F i W)).choose_spec.choose _
  apply (cancel_epi (eqToHom h.symm)).mp
  apply SheafOfModules.tensor_generator_ext.{u + 1, u, u + 1}
    (PurStrictScalar.constantMap l E F i W)
  intro U x b
  change (β'.hom.app M).val.app U
      (pbcTensorSection (PurStrictScalar.constantMap l E F i W)
        ((PurStrictScalar.constantRestriction l E W).obj M) U b x) =
    (γ.hom.app M).val.app U
      (pbcTensorSection (PurStrictScalar.constantMap l E F i W)
        ((PurStrictScalar.constantRestriction l E W).obj M) U b x)
  exact (hβ' M U b x).trans (hβ M U b x).symm

/-- The ordinary-to-strict-tower comparison is the published normalized chi. Its descent
is specified on every good K-flat representative, not chosen using finite freeness.
Source: Bhatt--Scholze 6.8.2(1), Definition 3.4.10
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: choose the arithmetic basis to identify constant tensor with a finite sum.
It commutes with the products of a strict tower. The basis identifies the comparison
with the completion unit, hence proves invertibility on complete inputs. The actual
map is already determined by the quotient product map and the zero shifted-product
component. Its universal derived counit gives exactly the displayed descent equation. -/
theorem compactSupportCoefficientModels_chi (W : Scheme.{u}) :
    (∀ M : DerivedCategory (integralTowerModules l E W),
      IsDerivedCompleteUnrestricted l E W M →
        IsIso ((completedScalarComparison l E F i W).app M) ∧
        IsDerivedCompleteUnrestricted l F W
          ((completedDerivedScalarExtension l E F i W).obj M)) ∧
    (∀ P : (integralOperationsGoodComplex l E W).FullSubcategory,
      (completedScalarComparison l E F i W).app (DerivedCategory.Q.{u + 2}.obj P.obj) ≫
        (integralScalarExtensionComparisonOfUniverses l E F i W).hom.app P =
      completedScalarCounit l E F i W P.obj ≫
        DerivedCategory.Q.{u + 2}.map ((completedScalarChainComparison l E F i W).app P.obj)) ∧
    (∀ (P : CochainComplex (integralTowerModules l E W) ℤ) (q : ℤ)
        (n : ℕ) (U : W.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l F W).obj.obj U)
        (x : (P.X q).val.obj U),
        ((((completedScalarChainComparison l E F i W).app P).f q ≫
          (CochainComplex.mappingCocone.fst
            (completedScalarRoosEndomorphism l E F i W P)).f q ≫
          (Pi.π
            (fun n ↦ ((integralScalarTowerFunctor l E F i W).obj P).obj (op n)) n).f q).val.app U)
            (completedScalarTensorSection l E F i W (P.X q) U s x) =
          integralScalarTensorSection l E F i W n (P.X q) U
            ((completedIntegralCommRingProjectionUnrestricted l F W n).hom.app U s) x) ∧
    ∀ (P : CochainComplex (integralTowerModules l E W) ℤ) (q : ℤ),
      ((completedScalarChainComparison l E F i W).app P).f q ≫
        (CochainComplex.mappingCocone.snd
          (completedScalarRoosEndomorphism l E F i W P)).v q (q - 1) (by omega) = 0 := by
  refine ⟨(finiteFreeCompletedScalarComparison l E F i W).2.1, ?_, ?_⟩
  · exact completedScalarComparison_spec l E F i W
  · exact completedScalarChainComparison_spec l E F i W

private theorem coefficientIntegralBasis :
    let := i.toAlgebra
    let := (integralScalarIntegerInclusion l E F i).toAlgebra
    Nonempty (Module.Basis (Fin (Module.finrank E F))
      (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionIntegers l F)) := by
  classical
  let := i.toAlgebra
  let := (integralScalarIntegerInclusion l E F i).toAlgebra
  let A := Padic.coefficientExtensionIntegers l E
  let B := Padic.coefficientExtensionIntegers l F
  have : FiniteDimensional E F := Module.Finite.right ℚ_[l] E F
  obtain ⟨b, hb, hex⟩ := Padic.exists_integral_basis l E F
    (integralScalar_absoluteValue l E F i)
  let v : Fin (Module.finrank E F) → B := fun j ↦ ⟨b j, hb j⟩
  let f : (Fin (Module.finrank E F) → A) →ₗ[A] B :=
    ∑ j, (LinearMap.proj j).smulRight (v j)
  have hf (c : Fin (Module.finrank E F) → A) :
      (f c : F) = ∑ j, i (c j) * b j := by
    simp only [f, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    change B.subtype (∑ j, c j • v j) = _
    rw [map_sum]
    rfl
  have hbije : Function.Bijective f := by
    constructor
    · intro c c' h
      obtain ⟨a, ha, huniq⟩ := hex (f c) (f c).property
      have hc : (fun j ↦ (c j : E)) = a := huniq _
        ⟨fun j ↦ (c j).property, hf c⟩
      have hc' : (fun j ↦ (c' j : E)) = a := huniq _
        ⟨fun j ↦ (c' j).property, (congrArg (fun z : B ↦ (z : F)) h).trans (hf c')⟩
      funext j
      apply Subtype.ext
      exact congrFun (hc.trans hc'.symm) j
    · intro x
      obtain ⟨a, ha, _⟩ := hex x x.property
      let c : Fin (Module.finrank E F) → A := fun j ↦ ⟨a j, ha.1 j⟩
      refine ⟨c, Subtype.ext ?_⟩
      exact (hf c).trans ha.2.symm
  exact ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective f hbije).symm⟩

private theorem coefficientQuotientBasis
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (d : ℕ) (b : Module.Basis (Fin d) A B) (I : Ideal A) (K : Ideal B)
    (hK : K = I.map (algebraMap A B)) (h : I ≤ K.comap (algebraMap A B)) :
    letI := Ideal.Quotient.algebraQuotientOfLEComap h
    ∃ c : Module.Basis (Fin d) (A ⧸ I) (B ⧸ K),
      ∀ j : Fin d, c j = Ideal.Quotient.mk K (b j) := by
  subst K
  let c := (b.baseChange (A ⧸ I)).map
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv
  refine ⟨c, ?_⟩
  intro j
  apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).injective
  simp [c]

/-- Completeness, separatedness, and one basis at every quotient level.
The unique coordinate vector is over the actual quotient ring, with its action induced
by the integer inclusion; the same `b` is used for every exponent, so the coordinate
maps commute with all quotient transitions.
Source: Bhatt--Scholze 6.8.2(1), coefficient-model argument Steps 1--2
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: the valuation rings are closed in complete finite extensions and the valuation
balls are the uniformizer-adic balls. A nonzero element has a finite valuation, giving
the zero intersection. Choose an integral basis using lem-sfb-local-field-integral-basis.
Its coordinate map carries `(t^n A)^r` onto `t^n B`. Quotienting the same map gives the
unique residue coordinates, and its quotient diagrams commute on every coordinate. -/
theorem compactSupportCoefficientModels_arithmetic
    (e : ℕ) (hepos : 1 ≤ e) (he : PurCompactSupport.Ramification l E F i e) :
    IsAdicComplete (Ideal.span {Padic.coefficientExtensionUniformizer l E})
      (Padic.coefficientExtensionIntegers l E) ∧
    IsAdicComplete (Ideal.span {Padic.coefficientExtensionUniformizer l F})
      (Padic.coefficientExtensionIntegers l F) ∧
    (⨅ n : ℕ, Ideal.map (integralScalarIntegerInclusion l E F i)
      (Padic.coefficientExtensionIdeal l E n)) = ⊥ ∧
    ∃ (r : ℕ) (b : Fin r → Padic.coefficientExtensionIntegers l F),
      Function.Bijective (fun c : Fin r → Padic.coefficientExtensionIntegers l E ↦
        ∑ j, integralScalarIntegerInclusion l E F i (c j) * b j) ∧
      ∀ (n : ℕ) (y : Padic.coefficientExtensionIntegers l F),
        ∃! c : Fin r → Padic.coefficientExtensionRing l E n,
          ∀ d : Fin r → Padic.coefficientExtensionIntegers l E,
            (∀ j, Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n) (d j) = c j) →
            Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (e * n))
                (∑ j, integralScalarIntegerInclusion l E F i (d j) * b j) =
              Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l F (e * n)) y := by
  classical
  let := i.toAlgebra
  let := (integralScalarIntegerInclusion l E F i).toAlgebra
  let A := Padic.coefficientExtensionIntegers l E
  let B := Padic.coefficientExtensionIntegers l F
  have hcomplete (H : Type u) [Field H] [Algebra ℚ_[l] H]
      [FiniteDimensional ℚ_[l] H] :
      IsAdicComplete (Ideal.span {Padic.coefficientExtensionUniformizer l H})
        (Padic.coefficientExtensionIntegers l H) :=
    AdicCompletion.of_bijective_iff.mp
      (((Padic.finite_module_adic_complete_and_hom.{u, u, u} l H).1
        (Padic.coefficientExtensionIntegers l H)).2.1)
  have hF := (Padic.extension_integers_dvr l F
    (Padic.coefficientExtensionAbsoluteValue l F)
    (spectralNorm_extends (K := ℚ_[l]) (L := F))).choose_spec.choose_spec
  have : IsDiscreteValuationRing B := hF.2.2.2.2.2.2.2.1
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l F} =
      Padic.coefficientExtensionMaximalIdeal l F :=
    hF.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hmap (n : ℕ) : Ideal.map (integralScalarIntegerInclusion l E F i)
      (Padic.coefficientExtensionIdeal l E n) =
        Padic.coefficientExtensionIdeal l F (e * n) := by
    have he' := he
    change Ideal.map (integralScalarIntegerInclusion l E F i)
      (Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ 1) =
        Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ e at he'
    simp only [pow_one] at he'
    simp only [Padic.coefficientExtensionIdeal, Ideal.map_pow, he', pow_mul]
  have hsep : (⨅ n : ℕ, Ideal.map (integralScalarIntegerInclusion l E F i)
      (Padic.coefficientExtensionIdeal l E n)) = ⊥ := by
    simp_rw [hmap, Padic.coefficientExtensionIdeal, pow_mul]
    apply Ideal.iInf_pow_eq_bot_of_isLocalRing
    have hm : (Padic.coefficientExtensionMaximalIdeal l F).IsMaximal := hF.2.2.2.2.1
    apply ne_top_of_le_ne_top hm.ne_top
    rw [← hgen]
    exact Ideal.pow_le_self (by omega : e ≠ 0)
  obtain ⟨b⟩ := coefficientIntegralBasis l E F i
  refine ⟨hcomplete E, hcomplete F, hsep, Module.finrank E F, b, ?_, ?_⟩
  · have hb (z : Fin (Module.finrank E F) → A) :
        b.equivFun.symm z = ∑ j, integralScalarIntegerInclusion l E F i (z j) * b j := by
      rw [Module.Basis.equivFun_symm_apply]
      rfl
    have hbfun : (fun z ↦ ∑ j, integralScalarIntegerInclusion l E F i (z j) * b j) =
        ⇑b.equivFun.symm := funext (fun z ↦ (hb z).symm)
    rw [hbfun]
    exact b.equivFun.symm.bijective
  · intro n y
    let I := Padic.coefficientExtensionIdeal l E n
    let K := Padic.coefficientExtensionIdeal l F (e * n)
    have hK : K = I.map (algebraMap A B) := (hmap n).symm
    have hle : I ≤ K.comap (algebraMap A B) := by
      rw [hK]
      exact Ideal.le_comap_map
    let := Ideal.Quotient.algebraQuotientOfLEComap hle
    obtain ⟨c, hc⟩ := coefficientQuotientBasis (Module.finrank E F) b I K hK hle
    have hsum (d : Fin (Module.finrank E F) → A) :
        c.equivFun.symm (fun j ↦ Ideal.Quotient.mk I (d j)) =
          Ideal.Quotient.mk K (∑ j, integralScalarIntegerInclusion l E F i (d j) * b j) := by
      simp only [Module.Basis.equivFun_symm_apply, hc, map_sum, map_mul]
      rfl
    refine ⟨c.equivFun (Ideal.Quotient.mk K y), ?_, ?_⟩
    · intro d hd
      rw [← hsum, show (fun j ↦ Ideal.Quotient.mk I (d j)) =
        c.equivFun (Ideal.Quotient.mk K y) from funext hd]
      exact c.equivFun.symm_apply_apply _
    · intro z hz
      choose d hd using fun j ↦ Ideal.Quotient.mk_surjective (z j)
      apply c.equivFun.symm.injective
      rw [c.equivFun.symm_apply_apply, ← show (fun j ↦ Ideal.Quotient.mk I (d j)) = z
        from funext hd, hsum]
      exact hz d hd

/-- The actual map to any smaller ramified quotient; no flatness is asserted.
Source: Bhatt--Scholze 6.8.2(1), coefficient-model argument Step 7
(blueprint: lem-pur-compact-support-coefficient-models). -/
def compactSupportCoefficientQuotient
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e)
    (n a : ℕ) (ha : a ≤ e * n) :
    Padic.coefficientExtensionRing l E n →+* Padic.coefficientExtensionRing l F a :=
  (Ideal.Quotient.factor (Ideal.pow_le_pow_right ha)).comp
    (PurCompactSupport.ramifiedMap l E F i e he n)

/-- The preceding ring map on constant sheaves.
Source: Bhatt--Scholze 6.8.2(1), coefficient-model argument Step 7
(blueprint: lem-pur-compact-support-coefficient-models). -/
def compactSupportCoefficientQuotientSheaf
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e)
    (n a : ℕ) (ha : a ≤ e * n) (W : Scheme.{u}) :=
  (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (compactSupportCoefficientQuotient l E F i e he n a ha).ulift.{u + 1, u + 1})

private theorem coefficientProjection_quotient (W : Scheme.{u})
    (m a : ℕ) (hm : 1 ≤ m) (ha : 1 ≤ a) (h : a ≤ m) :
    PurCompactSupport.projection l F m hm W ≫
        PurCompactSupport.finiteQuotient l F m a hm ha h W =
      PurCompactSupport.projection l F a ha W := by
  cases m with
  | zero => omega
  | succ m =>
    cases a with
    | zero => omega
    | succ a => exact compactSupportProjection_comp l F W m a (by omega)

private theorem coefficientFiniteQuotient_map (W : Scheme.{u})
    (m a : ℕ) (hm : 1 ≤ m) (ha : 1 ≤ a) (h : a ≤ m) :
    PurCompactSupport.finiteQuotient l F m a hm ha h W =
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
        (CommRingCat.ofHom
          (show Padic.coefficientExtensionRing l F m →+* Padic.coefficientExtensionRing l F a
            from Ideal.Quotient.factor (Ideal.pow_le_pow_right h)).ulift) := by
  cases m with
  | zero => omega
  | succ m =>
    cases a with
    | zero => omega
    | succ a => rfl

/-- The two coefficient maps are equal, including their fixed finite projections.
Source: Bhatt--Scholze 6.8.2(1), coefficient-model argument Step 7
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: the ideal equality raised to the nth power gives `t^n B = v^(en) B`.
After projecting further to exponent a, both composites send a constant x to its
image in B/v^a. The completed map is fixed by its projections, and constant sections
locally generate every finite coefficient sheaf, proving the displayed equality. -/
theorem compactSupportCoefficientQuotient_square
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e)
    (n a : ℕ) (hn : 1 ≤ n) (ha : 1 ≤ a) (han : a ≤ e * n) (W : Scheme.{u}) :
    completedCoefficientMap l E F i W ≫ PurCompactSupport.projection l F a ha W =
      PurCompactSupport.projection l E n hn W ≫
        compactSupportCoefficientQuotientSheaf l E F i e he n a han W := by
  have hepos : 1 ≤ e := by
    by_contra h
    have : e = 0 := by omega
    simp only [this, zero_mul] at han
    omega
  have hen : 1 ≤ e * n := Nat.mul_pos hepos hn
  have h := congrArg
    (fun k ↦ k ≫ PurCompactSupport.finiteQuotient l F (e * n) a hen ha han W)
    (PurCompactSupport.ramified_reduction_square l E F i e he hepos n hn W)
  rw [Category.assoc, coefficientProjection_quotient l F W (e * n) a hen ha han] at h
  refine h.trans ?_
  rw [Category.assoc]
  congr 1
  change PurCompactSupport.ramifiedSheafMap l E F i e he n W ≫
    PurCompactSupport.finiteQuotient l F (e * n) a hen ha han W = _
  rw [coefficientFiniteQuotient_map l F W (e * n) a hen ha han]
  unfold PurCompactSupport.ramifiedSheafMap compactSupportCoefficientQuotientSheaf
    compactSupportCoefficientQuotient
  exact ((constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map_comp _ _).symm

/-- Inverse image preserves the completed coefficient inclusion and every finite
quotient, including arbitrary ramified reductions.
Source: Stacks 098T, 04D3; Bhatt--Scholze 6.8.2(1)
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: constant inverse-image maps send each constant basis section to itself and
commute with every ring homomorphism. Compose with all finite projections to identify
the completed comparison. Joint monicity gives the completed square. Naturality of
the same constant comparison gives the quotient square, including nonflat quotients. -/
theorem compactSupportCoefficientModels_inverseImage
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e)
    (n a : ℕ) (hn : 1 ≤ n) (ha : 1 ≤ a) (han : a ≤ e * n)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    ((PurCompactSupport.completed l E).pull g).hom ≫ completedCoefficientMap l E F i U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (completedCoefficientMap l E F i V) ≫
          ((PurCompactSupport.completed l F).pull g).hom ∧
    ((PurStrictScalar.constants l E).pull g).hom ≫ PurStrictScalar.constantMap l E F i U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (PurStrictScalar.constantMap l E F i V) ≫
          ((PurStrictScalar.constants l F).pull g).hom ∧
    ((PurCompactSupport.finite l E n hn).pull g).hom ≫
        compactSupportCoefficientQuotientSheaf l E F i e he n a han U =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (compactSupportCoefficientQuotientSheaf l E F i e he n a han V) ≫
          ((PurCompactSupport.finite l F a ha).pull g).hom := by
  refine ⟨PurCompactSupport.completedChange_square l E F i g,
    (PurStrictScalar.change l E F i).square g, ?_⟩
  exact (proEtaleConstantInverseImageMap_naturality g
    (CommRingCat.ofHom
      (compactSupportCoefficientQuotient l E F i e he n a han).ulift)).symm

/-- The canonical balanced reduction, defined by the tensor-unit normalized scalar
adjunctions. This is a natural isomorphism on the entire ambient derived category.
Source: Bhatt--Scholze 6.8.2(1), coefficient-model argument Step 7
(blueprint: lem-pur-compact-support-coefficient-models). -/
def compactSupportCoefficientBalancedReduction
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e)
    (n a : ℕ) (hn : 1 ≤ n) (ha : 1 ≤ a) (han : a ≤ e * n) (W : Scheme.{u}) :
    pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙
        pbcDerivedExtend (PurCompactSupport.projection l F a ha W) ≅
      pbcDerivedExtend (PurCompactSupport.projection l E n hn W) ⋙
        pbcDerivedExtend
          (compactSupportCoefficientQuotientSheaf l E F i e he n a han W) :=
  PurCompactSupport.tensorComposition _ _ _
      (compactSupportCoefficientQuotient_square l E F i e he n a hn ha han W) ≪≫
    (PurCompactSupport.tensorComposition _ _ _ rfl).symm

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionIdeal Padic.coefficientExtensionUniformizer
open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
private abbrev coefficientSectionModule
    (W : Scheme.{u}) (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (M : pbcModules W R) (V : W.ProEtᵒᵖ) : Module (R.obj.obj V) (M.val.obj V) :=
  ModuleCat.isModule (M.val.obj V)

attribute [local instance] coefficientSectionModule

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientTensor_hom_ext
    (W : Scheme.{u}) (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (M N H : pbcModules W R)
    (v w : ((proEtaleOrdinaryTensor W R).obj M).obj N ⟶ H)
    (h : ∀ (U : W.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      v.val.app U (proEtaleTensorPair W R M N U x y) =
        w.val.app U (proEtaleTensorPair W R M N U x y)) : v = w := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} W
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (𝟙 ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
      M N).inv).mp
  apply (adj.homEquiv _ H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  change v.val.app U ((SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
      M N).inv.val.app U
      ((adj.unit.app (M.val ⊗ N.val)).app U t)) =
    w.val.app U ((SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
      M N).inv.val.app U
      ((adj.unit.app (M.val ⊗ N.val)).app U t))
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => exact h U x y
  | add t s ht hs => simp only [map_add, ht, hs]

private theorem tensorCancellationUnique
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : pbcModules W R) (N L : pbcModules W S)
    (t : ∀ (U : W.ProEtᵒᵖ), S.obj.obj U → M.val.obj U → L.val.obj U)
    (β : ((proEtaleOrdinaryTensor W R).obj M).obj ((pbcRestrict φ).obj N) ≅
      (pbcRestrict φ).obj (((proEtaleOrdinaryTensor W S).obj L).obj N))
    (hβsec : ∀ (U : W.ProEtᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) (z : N.val.obj U),
      β.inv.val.app U (proEtaleTensorPair W S L N U (t U s x) z) =
        proEtaleTensorPair W R M ((pbcRestrict φ).obj N) U x (s • z)) :
    ∃! β' : (pbcRestrict φ).obj (((proEtaleOrdinaryTensor W S).obj L).obj N) ≅
      ((proEtaleOrdinaryTensor W R).obj M).obj ((pbcRestrict φ).obj N),
      ∀ (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) (z : N.val.obj U),
        β'.hom.val.app U (proEtaleTensorPair W S L N U (t U s x) z) =
          proEtaleTensorPair W R M ((pbcRestrict φ).obj N) U x (s • z) := by
  refine ⟨β.symm, ?_, ?_⟩
  · intro U s x z
    exact hβsec U x s z
  · intro β' hβ'
    apply Iso.ext
    apply (cancel_epi β.hom).mp
    simp only [Iso.symm_hom, Iso.hom_inv_id]
    apply coefficientTensor_hom_ext W _ M ((pbcRestrict φ).obj N)
    intro U x z
    let zN : N.val.obj U := z
    have hs := hβsec U x 1 zN
    have hz : (1 : S.obj.obj U) • zN = zN := by
      exact (ModuleCat.isModule (N.val.obj U)).one_smul zN
    rw [hz] at hs
    have hi := congrArg (β.hom.val.app U) hs
    have hid := congrArg (fun f ↦ f.val.app U
      (proEtaleTensorPair W _ L N U
        (t U 1 x) z)) β.inv_hom_id
    have hi' : β.hom.val.app U
        (proEtaleTensorPair W _ M ((pbcRestrict φ).obj N) U x z) =
      proEtaleTensorPair W _ L N U
        (t U 1 x) z := by
        change _ = _ at hid
        exact hi.symm.trans hid
    change β'.hom.val.app U (β.hom.val.app U
      (proEtaleTensorPair W _ M ((pbcRestrict φ).obj N) U x z)) = _
    rw [hi']
    change β'.hom.val.app U
      (proEtaleTensorPair W _ L N U
        (t U 1 x) z) =
      proEtaleTensorPair W _ M ((pbcRestrict φ).obj N) U x z
    simpa only [hz] using hβ' U 1 x zN

/-- The local tensor formula fixes the natural cancellation comparison uniquely. -/
private theorem coefficientBalancingNaturalIso_existsUnique
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (N : pbcModules W S) :
    ∃! α : pbcExtend φ ⋙ (proEtaleOrdinaryTensor W S).flip.obj N ⋙ pbcRestrict φ ≅
      (proEtaleOrdinaryTensor W R).flip.obj ((pbcRestrict φ).obj N),
      ∀ (M : pbcModules W R) (V : W.ProEtᵒᵖ) (s : S.obj.obj V)
        (x : M.val.obj V) (z : N.val.obj V),
        (α.hom.app M).val.app V
            (proEtaleTensorPair W S ((pbcExtend φ).obj M) N V
              (pbcTensorSection φ M V s x) z) =
          proEtaleTensorPair W R M ((pbcRestrict φ).obj N) V x (s • z) := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} W
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have hobj : ∀ M : pbcModules W R,
      (pbcExtend φ).obj M = SheafOfModules.changeOfRings φ M :=
    (pbcExtensionExistence φ).choose_spec.choose
  have hmap : ∀ {M M' : pbcModules W R} (f : M ⟶ M'),
      (pbcExtend φ).map f = eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj M').symm :=
    (pbcExtensionExistence φ).choose_spec.choose_spec.choose
  obtain ⟨b, hb, hbsec⟩ := CategoryTheory.ordinaryTensorCancellation.{u + 1, u, u + 1}
    φ (pbcExtend φ) hobj hmap
  let α : pbcExtend φ ⋙ (proEtaleOrdinaryTensor W S).flip.obj N ⋙ pbcRestrict φ ≅
      (proEtaleOrdinaryTensor W R).flip.obj ((pbcRestrict φ).obj N) :=
    NatIso.ofComponents (fun M ↦ (b M N).symm) (by
      intro M M' f
      have h := hb f (𝟙 N)
      rw [(siteTensorRestriction φ).map_id, tensorHom_id, tensorHom_id] at h
      change ((proEtaleOrdinaryTensor W R).map f).app ((pbcRestrict φ).obj N) ≫
        (b M' N).hom = (b M N).hom ≫
          (pbcRestrict φ).map
            (((proEtaleOrdinaryTensor W S).map ((pbcExtend φ).map f)).app N) at h
      change (pbcRestrict φ).map
        (((proEtaleOrdinaryTensor W S).map ((pbcExtend φ).map f)).app N) ≫ (b M' N).inv =
          (b M N).inv ≫ ((proEtaleOrdinaryTensor W R).map f).app ((pbcRestrict φ).obj N)
      apply (cancel_epi (b M N).hom).mp
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
        Category.comp_id] using congrArg (fun k ↦ k ≫ (b M' N).inv) h.symm)
  refine ⟨α, ?_, ?_⟩
  · intro M V s x z
    exact hbsec M N V x s z
  · intro α' hα'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have hu := tensorCancellationUnique W φ M N ((pbcExtend φ).obj M)
      (pbcTensorSection φ M) (b M N) (hbsec M N)
    have hc : α'.app M = α.app M := by
      apply hu.unique
      · exact hα' M
      · intro V s x z
        exact hbsec M N V x s z
    exact congrArg Iso.hom hc

/-- The natural comparison is fixed by its unique local tensor formula. -/
@[irreducible] private def coefficientBalancingNaturalIso
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (N : pbcModules W S) :
    pbcExtend φ ⋙ (proEtaleOrdinaryTensor W S).flip.obj N ⋙ pbcRestrict φ ≅
      (proEtaleOrdinaryTensor W R).flip.obj ((pbcRestrict φ).obj N) :=
  (coefficientBalancingNaturalIso_existsUnique W φ N).exists.choose

private theorem coefficientBalancingNaturalIso_tmul
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (N : pbcModules W S) (M : pbcModules W R) (V : W.ProEtᵒᵖ)
    (s : S.obj.obj V) (x : M.val.obj V) (z : N.val.obj V) :
    ((coefficientBalancingNaturalIso W φ N).hom.app M).val.app V
        (proEtaleTensorPair W S ((pbcExtend φ).obj M) N V
          (pbcTensorSection φ M V s x) z) =
      proEtaleTensorPair W R M ((pbcRestrict φ).obj N) V x (s • z) := by
  unfold coefficientBalancingNaturalIso
  exact (coefficientBalancingNaturalIso_existsUnique W φ N).exists.choose_spec M V s x z

private theorem coefficientModuleBalancing
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : pbcModules W R) (N : pbcModules W S) :
    ∃! β : (pbcRestrict φ).obj
        (((proEtaleOrdinaryTensor W S).obj ((pbcExtend φ).obj M)).obj N) ≅
      ((proEtaleOrdinaryTensor W R).obj M).obj ((pbcRestrict φ).obj N),
      ∀ (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) (z : N.val.obj U),
        β.hom.val.app U
          (proEtaleTensorPair W S ((pbcExtend φ).obj M) N U
            (pbcTensorSection φ M U s x) z) =
          proEtaleTensorPair W R M ((pbcRestrict φ).obj N) U x (s • z) := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} W
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact tensorCancellationUnique W φ M N ((pbcExtend φ).obj M)
    (pbcTensorSection φ M) ((coefficientBalancingNaturalIso W φ N).app M).symm
    (by
      intro V x s z
      exact coefficientBalancingNaturalIso_tmul W φ N M V s x z)

set_option backward.isDefEq.respectTransparency.types false in
/-- The section-normalized balancing map at a single module is unique.
This helper fixes the comparison used for the further derived tensor.
Source: Stacks 03EK, 06YY; coefficient-model argument Step 7
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: send `(s tensor x) tensor z` to `x tensor sz`, with inverse sending
`x tensor z` to `(1 tensor x) tensor z`. The tensor balancing relations give
inverse module maps; sheafification and local generation prove uniqueness. -/
theorem compactSupportCoefficientModels_moduleBalancing
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e)
    (n a : ℕ) (han : a ≤ e * n) (W : Scheme.{u})
    (M : pbcModules W (proEtaleConstantRing W (Padic.coefficientExtensionRing l E n)))
    (N : pbcModules W (proEtaleConstantRing W (Padic.coefficientExtensionRing l F a))) :
    ∃! β : (pbcRestrict
        (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).obj
        (((proEtaleOrdinaryTensor W
          (proEtaleConstantRing W (Padic.coefficientExtensionRing l F a))).obj
            ((pbcExtend
              (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).obj M)).obj N) ≅
      ((proEtaleOrdinaryTensor W
        (proEtaleConstantRing W (Padic.coefficientExtensionRing l E n))).obj M).obj
          ((pbcRestrict
            (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).obj N),
      ∀ (U : W.ProEtᵒᵖ)
        (s : (proEtaleConstantRing W (Padic.coefficientExtensionRing l F a)).obj.obj U)
        (x : M.val.obj U) (z : N.val.obj U),
        β.hom.val.app U
          (proEtaleTensorPair W
            (proEtaleConstantRing W (Padic.coefficientExtensionRing l F a))
            ((pbcExtend
              (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).obj M) N U
            (pbcTensorSection
              (compactSupportCoefficientQuotientSheaf l E F i e he n a han W) M U s x) z) =
          proEtaleTensorPair W
            (proEtaleConstantRing W (Padic.coefficientExtensionRing l E n)) M
            ((pbcRestrict
              (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).obj N) U x (s •
      z) := by
  exact coefficientModuleBalancing W
    (compactSupportCoefficientQuotientSheaf l E F i e he n a han W) M N

private theorem coefficientBalancingNaturalIso_app
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (N : pbcModules W S) (M : pbcModules W R) :
    (coefficientBalancingNaturalIso W φ N).app M =
      (coefficientModuleBalancing W φ M N).exists.choose := by
  have h := coefficientModuleBalancing W φ M N
  apply h.unique
  · intro V s x z
    exact coefficientBalancingNaturalIso_tmul W φ N M V s x z
  · exact h.exists.choose_spec

private theorem coefficientLocalizationUnique
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    (Q : CochainComplex C ℤ ⥤ D) {X Y H : CochainComplex C ℤ} {Z : D}
    (q : Z ≅ Q.obj X) (a : X ≅ H) (b : Y ≅ H)
    (f : ∀ k : ℤ, X.X k ⟶ H.X k) (hf : ∀ k : ℤ, f k = a.hom.f k) :
    ∃! δ : Z ≅ Q.obj Y, ∃ γ : X ≅ Y,
      δ = q ≪≫ Q.mapIso γ ∧ ∀ k : ℤ, f k = γ.hom.f k ≫ b.hom.f k := by
  let γ := a ≪≫ b.symm
  have h : γ.hom ≫ b.hom = a.hom := by
    change (a.hom ≫ b.inv) ≫ b.hom = a.hom
    rw [Category.assoc, b.inv_hom_id, Category.comp_id]
  have hγ (k : ℤ) : f k = γ.hom.f k ≫ b.hom.f k :=
    (hf k).trans (congrArg (fun t ↦ t.f k) h).symm
  refine ⟨q ≪≫ Q.mapIso γ, ⟨γ, rfl, hγ⟩, ?_⟩
  rintro δ' ⟨γ', rfl, hγ'⟩
  have hγeq : γ' = γ := by
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro k
    apply (cancel_mono (b.hom.f k)).mp
    exact (hγ' k).symm.trans (hγ k)
  rw [hγeq]

attribute [local irreducible] compactSupportCoefficientQuotientSheaf
  reductionChange reductionDerivedChange
  completedCoefficientMap

/-- Tensoring the balanced reduction with any degree-zero target module is the
source reduction tensored with the restricted module. The unique chain isomorphism
sends `(s tensor x) tensor z` to `x tensor sz`, fixing its derived localization.
Source: Stacks 06YY; Bhatt--Scholze 6.8.2(1), coefficient-model argument Step 7
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: the displayed rule is balanced and linear, commutes with restrictions, and has
inverse `x tensor z` mapped to `(1 tensor x) tensor z`. These inverse formulas pass to
sheafification and commute with differentials. A K-flat source representative remains
K-flat after extension; its tensor with the degree-zero module therefore computes the
left derived tensor even when the target quotient is nonflat over the source quotient.
The same source representative computes the right side. Use mapBifunctorSingle₂Iso
to identify total tensor with N in degree zero with the termwise tensor functor.
In each degree use the unique moduleBalancing isomorphism above; its normalization
implies naturality in P and hence compatibility with the differential. Conjugating
back gives the chain isomorphism γ. The equation for δ is exactly localization of γ
through the fixed exact-restriction factorization. Degreewise uniqueness of the
module maps gives uniqueness of γ, and then the localization equation gives uniqueness
of δ, independently of the representative. -/
theorem compactSupportCoefficientModels_furtherTensor
    (e : ℕ) (he : PurCompactSupport.Ramification l E F i e)
    (n a : ℕ) (han : a ≤ e * n) (W : Scheme.{u})
    (P : CochainComplex (pbcModules W (proEtaleConstantRing W
      (Padic.coefficientExtensionRing l E n))) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat.{u + 1, u}
      (R := proEtaleConstantRing W (Padic.coefficientExtensionRing l E n)) P)
    (N : pbcModules W (proEtaleConstantRing W (Padic.coefficientExtensionRing l F a))) :
    ∃! δ :
      (pbcDerivedRestrict
        (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).obj
        (DerivedCategory.Q.{u + 2}.obj
          ((coefficientTotalTensor.{0, u + 1, u} (ProEt.topology W)
            (proEtaleConstantRing W (Padic.coefficientExtensionRing l F a))).obj
            ((((pbcExtend
              (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P),
              ((CochainComplex.singleFunctor _ (0 : ℤ)).obj N)))) ≅
      DerivedCategory.Q.{u + 2}.obj
        ((coefficientTotalTensor.{0, u + 1, u} (ProEt.topology W)
          (proEtaleConstantRing W (Padic.coefficientExtensionRing l E n))).obj
          (P, (CochainComplex.singleFunctor _ (0 : ℤ)).obj
            ((pbcRestrict
              (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).obj N))),
      ∃ γ : ((pbcRestrict
          (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          ((coefficientTotalTensor.{0, u + 1, u} (ProEt.topology W)
            (proEtaleConstantRing W (Padic.coefficientExtensionRing l F a))).obj
            ((((pbcExtend
              (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P),
              ((CochainComplex.singleFunctor _ (0 : ℤ)).obj N))) ≅
        ((coefficientTotalTensor.{0, u + 1, u} (ProEt.topology W)
            (proEtaleConstantRing W (Padic.coefficientExtensionRing l E n))).obj
            (P, (CochainComplex.singleFunctor _ (0 : ℤ)).obj
              ((pbcRestrict
                (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).obj N))),
        δ = (pbcRestrict
            (compactSupportCoefficientQuotientSheaf l E F i e he n a han
              W)).mapDerivedCategoryFactors.app
            ((coefficientTotalTensor.{0, u + 1, u} (ProEt.topology W)
            (proEtaleConstantRing W (Padic.coefficientExtensionRing l F a))).obj
            ((((pbcExtend
              (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P),
              ((CochainComplex.singleFunctor _ (0 : ℤ)).obj N))) ≪≫ DerivedCategory.Q.mapIso γ ∧
        ∀ k : ℤ,
          (pbcRestrict
            (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).map
              ((CochainComplex.mapBifunctorSingle₂Iso
                (proEtaleOrdinaryTensor W
                  (proEtaleConstantRing W (Padic.coefficientExtensionRing l F a))) N
                (((pbcExtend
                  (compactSupportCoefficientQuotientSheaf l E F i e he n a han
                    W)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)).hom.f k) ≫
            (compactSupportCoefficientModels_moduleBalancing l E F i e he n a han W
              (P.X k) N).exists.choose.hom =
          γ.hom.f k ≫
            (CochainComplex.mapBifunctorSingle₂Iso
              (proEtaleOrdinaryTensor W
                (proEtaleConstantRing W (Padic.coefficientExtensionRing l E n)))
              ((pbcRestrict
                (compactSupportCoefficientQuotientSheaf l E F i e he n a han W)).obj N)
              P).hom.f k := by
  have _ := hP
  let R := proEtaleConstantRing W (Padic.coefficientExtensionRing l E n)
  let S := proEtaleConstantRing W (Padic.coefficientExtensionRing l F a)
  let φ := compactSupportCoefficientQuotientSheaf l E F i e he n a han W
  let U := pbcRestrict φ
  let T := pbcExtend φ
  let UC := U.mapHomologicalComplex (.up ℤ)
  let TC := T.mapHomologicalComplex (.up ℤ)
  let tR := proEtaleOrdinaryTensor W R
  let tS := proEtaleOrdinaryTensor W S
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} W
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let α := coefficientBalancingNaturalIso W φ N
  let ηS := CochainComplex.mapBifunctorSingle₂Iso tS N (TC.obj P)
  let ηR := CochainComplex.mapBifunctorSingle₂Iso tR (U.obj N) P
  let q := U.mapDerivedCategoryFactors.app
    ((coefficientTotalTensor.{0, u + 1, u} (ProEt.topology W) S).obj
      (TC.obj P, (CochainComplex.singleFunctor _ (0 : ℤ)).obj N))
  apply coefficientLocalizationUnique DerivedCategory.Q q
    (UC.mapIso ηS ≪≫ (NatIso.mapHomologicalComplex α (.up ℤ)).app P) ηR
  intro k
  have hchosen :
      (compactSupportCoefficientModels_moduleBalancing l E F i e he n a han W
        (P.X k) N).exists.choose = α.app (P.X k) :=
    (coefficientBalancingNaturalIso_app W φ N (P.X k)).symm
  rw [hchosen]
  rfl

attribute [local semireducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionIdeal Padic.coefficientExtensionUniformizer
attribute [local semireducible] compactSupportCoefficientQuotientSheaf
  reductionChange reductionDerivedChange
  completedAdicChangeData completedCoefficientMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Scalar extension preserves the intrinsic constructible complete domain and every
specified common Tor interval, not merely the existence of some interval.
Source: Bhatt--Scholze 6.8.2(1), coefficient-model argument Steps 7--8
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: use the balanced reduction above for a source exponent with en at least a.
Further tensor with an arbitrary degree-zero B/v^a module balances to the source
reduction tensored with its restricted module, so the original interval applies.
No quotient flatness is needed. The finite-free completed scalar comparison identifies
ordinary extension with strict-tower extension and proves completeness. The intrinsic
constructible scalar-extension theorem proves constructibility of the strict-tower
object. Transport this property across the normalized scalar comparison, using the
legacy comparison only to supply its completeness hypothesis. -/
theorem compactSupportCoefficientModels_scalar
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (e : ℕ) (hepos : 1 ≤ e) (he : PurCompactSupport.Ramification l E F i e)
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    finiteTorConstructibleIntegral l F X
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) ∧
      ∀ (a b : ℤ),
        (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
          ((scalarReductionDerivedExtension l E X n).obj M) a b) →
        ∀ m : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l F (m + 1))
          ((scalarReductionDerivedExtension l F X m).obj
            ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) a b := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    have hlegacy : integralCtfProperty D l hl E X M := by
      refine ⟨?_, hM.2⟩
      exact ⟨(sfDerivedComplete_iff_legacy l E X D hl M).mp hM.1.1, hM.1.2⟩
    have _ := hepos
    have he' : Ideal.map (integralScalarIntegerInclusion l E F i)
        (Ideal.span {Padic.coefficientExtensionUniformizer l E}) =
          Ideal.span {Padic.coefficientExtensionUniformizer l F} ^ e := by
      simpa only [PurCompactSupport.Ramification, Padic.coefficientExtensionIdeal, pow_one]
        using he
    have htor := purAdicScalarExtensionTorBound D l hl E F i e he' X M hlegacy
    have hc : IsDerivedCompleteUnrestricted l E X M := by
      obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
      let : Fact p.Prime := ⟨hprime⟩
      let D₀ : FiniteFieldDatum.{0} :=
        { p := p
          a := 1
          q := p
          prime := hprime
          exponent_pos := le_refl 1
          cardinality_eq := (pow_one p).symm
          k₀ := ZMod p
          card_base := by simp [Nat.card_eq_fintype_card]
          k := AlgebraicClosure (ZMod p) }
      have hl₀ : l ≠ D₀.p := by change l ≠ p; omega
      exact ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E X D₀ hl₀ M).mp hM.1.1⟩
    have := ((finiteFreeCompletedScalarComparison l E F i X).2.1 M hc).1
    have hout := sfIntegralScalarExtension_constructible D.p l hl E F i X M hM.1
    have hconstructible : sfIntegralConstructible l F X
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) :=
      (sfIntegralConstructible l F X).prop_of_iso
        (asIso ((completedScalarComparison l E F i X).app M)).symm hout
    refine ⟨⟨hconstructible, ?_⟩, htor⟩
    obtain ⟨a, b, hab, hbounds⟩ := hM.2
    exact ⟨a, b, hab, htor a b hbounds⟩

/-- The separately derived proper/open presentations of both integral compact-support
values are constructible and derived complete. Their identification with the recorded
reduction-limit functors has the prescribed finite Roos projections.
Source: Bhatt--Scholze Definition 6.7.6 and Lemmas 6.7.7, 6.8.2(1)
(blueprint: lem-pur-compact-support-coefficient-models).
Proof: first apply the scalar clause to M. For each coefficient field, the normalized
compact-support realization identifies the ambient proper/open image with the value
of the existing constructible integral compact-support functor. Transport its object
property across the realization isomorphism. Its specification supplies the prescribed
finite projections, and its uniqueness clause gives the two final assertions.
No smoothness or purity is used. -/
theorem compactSupportCoefficientModels
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (e : ℕ) (hepos : 1 ≤ e) (he : PurCompactSupport.Ramification l E F i e)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (M : DerivedCategory (scalarReductionSource l E X))
    (hM : finiteTorConstructibleIntegral l E X M) :
    sfIntegralConstructible l E Y ((PurCompactSupport.image
      (PurCompactSupport.completed l E) c).obj M) ∧
    sfIntegralConstructible l F Y ((PurCompactSupport.image
      (PurCompactSupport.completed l F) c).obj
        ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) ∧
    Nonempty ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj M ≅
      (sfIntegralCompactSupportValue l E D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
        c ⟨M, hM.1⟩).obj) ∧
    (∃! τ : (sfIntegralConstructible l E X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E) c ≅
      sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E ⋙ (sfIntegralConstructible l E Y).ι,
      SfQcqsCompactSupportRealizationSpec l E D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c τ) ∧
    (∃! τ : (sfIntegralConstructible l F X).ι ⋙
        PurCompactSupport.image (PurCompactSupport.completed l F) c ≅
      sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c F ⋙ (sfIntegralConstructible l F Y).ι,
      SfQcqsCompactSupportRealizationSpec l F D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c τ) := by
  let hunit := PurCompactSupport.coefficientPrimeUnit l D hl
  let KE : sfIntegralConstructibleCategory l E X := ⟨M, hM.1⟩
  have hF := (compactSupportCoefficientModels_scalar l E F i D hl e hepos he X M hM).1
  let KF : sfIntegralConstructibleCategory l F X :=
    ⟨(pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M, hF.1⟩
  obtain ⟨τE, hτE, huniqE⟩ := sfQcqsCompactSupportRealization_existsUnique l E D.k hunit c
  obtain ⟨τF, hτF, huniqF⟩ := sfQcqsCompactSupportRealization_existsUnique l F D.k hunit c
  have hEout := (sfIntegralConstructible l E Y).prop_of_iso (τE.app KE).symm
    ((sfCompactSupportFiniteIntegralFunctor l D.k hunit c E).obj KE).property
  have hFout := (sfIntegralConstructible l F Y).prop_of_iso (τF.app KF).symm
    ((sfCompactSupportFiniteIntegralFunctor l D.k hunit c F).obj KF).property
  refine ⟨hEout, hFout, ?_, ⟨τE, hτE, huniqE⟩, ⟨τF, hτF, huniqF⟩⟩
  exact ⟨τE.app KE ≪≫ (sfIntegralConstructible l E Y).ι.mapIso
    (eqToIso (sfCompactSupportFiniteIntegralFunctor_obj l D.k hunit c E KE))⟩

end WeilConjectures
