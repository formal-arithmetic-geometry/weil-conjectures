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
import Mathlib.Algebra.CharP.CharAndCard
import all Sheaf.Paper.SfIntegralDirectImageConstructible
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import all Sheaf.Paper.IntegralCoefficientCompletenessTransport
import all Sheaf.Paper.SfCompleteDirectImageReduction
import all Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.PbcUniformReductionCriterion
import Sheaf.Paper.PbcConstructibleReductionCriterion
import Sheaf.Paper.PbcConstructibleReductionPullback
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Sheaf.Paper.PbcScalarExtension
import all Sheaf.Paper.FdIntegralIdentityRationalEquivalence


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
set_option backward.isDefEq.respectTransparency.types false
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
  let I := ObjectProperty.ι (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))
  let a := Adjunction.ofIsRightAdjoint I
  let e : (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj ≅
      (pbcActualCompletedPull f (pbcIntegralDatum l E)).obj M.obj :=
    (purStrictPullComparison l E f).app M
  let H := (Iso.homCongr e (Iso.refl K.obj)).trans
    ((ObjectProperty.fullyFaithfulι
        (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))).homEquiv.symm.trans
      (a.homEquiv ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj M.obj) K))
  have hunit := (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) f).exists.choose_spec M
  have h (u : (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj ⟶ K.obj) :
      H u = (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app M.obj ≫ u := by
    change (pbcActualCompletedPullUnit f (pbcIntegralDatum l E)).app M.obj ≫
      (e.inv ≫ u ≫ 𝟙 K.obj) = _
    change (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app M.obj ≫
      e.hom = (pbcActualCompletedPullUnit f (pbcIntegralDatum l E)).app M.obj at hunit
    rw [← hunit]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Category.comp_id]
  constructor
  · intro u v huv
    apply H.injective
    have hv := ((pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).homEquiv
      M.obj K.obj).injective huv
    exact (h u).trans (hv.trans (h v).symm)
  · intro v
    obtain ⟨u, hu⟩ := H.surjective
      (((pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).homEquiv M.obj K.obj).symm v)
    refine ⟨u, ?_⟩
    exact (congrArg
      ((pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).homEquiv M.obj K.obj)
      ((h u).symm.trans hu)).trans (Equiv.apply_symm_apply _ v)



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
  let h := purOrdinaryHom l E f M K
  have hadd (u w) : h (u + w) = h u + h w := by
    change (pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).homEquiv _ _
      (_ ≫ (u + w)) = _
    simp only [Preadditive.comp_add, Adjunction.homEquiv_unit, Functor.map_add]
    rfl
  have hsmul (r : PbcIntegralRing l E) u : h (r • u) = r • h u := by
    change (pbcActualDerivedAdjunction f (pbcIntegralDatum l E)).homEquiv _ _
      (_ ≫ (r • u)) = _
    simp only [Linear.comp_smul, Adjunction.homEquiv_unit, Functor.map_smul]
    rfl
  refine ⟨hadd, hsmul, ?_, ?_⟩
  · intro v w
    apply h.injective
    rw [h.apply_symm_apply, hadd, h.apply_symm_apply, h.apply_symm_apply]
  · intro r v
    apply h.injective
    rw [h.apply_symm_apply, hsmul, h.apply_symm_apply]


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

private theorem coefficientMateHom
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {LE : C ⥤ D} {RE : D ⥤ C} {LL : C' ⥤ D'} {RL : D' ⥤ C'}
    {CY : C ⥤ C'} {VY : C' ⥤ C} {CX : D ⥤ D'} {VX : D' ⥤ D}
    (aE : LE ⊣ RE) (aL : LL ⊣ RL) (aY : CY ⊣ VY) (aX : CX ⊣ VX)
    (t : CY ⋙ LL ≅ LE ⋙ CX) (K : D) :
    aY.homEquiv _ _
        ((mateEquiv aE aL (TwoSquare.mk _ _ _ _ t.hom)).natTrans.app K) =
      RE.map (aX.unit.app K) ≫
        (conjugateIsoEquiv (aY.comp aL) (aE.comp aX) t.symm).inv.app (CX.obj K) := by
  let b := mateEquiv aE aL (TwoSquare.mk _ _ _ _ t.hom)
  have hi := iterated_mateEquiv_conjugateEquiv aE aL aY aX
    (TwoSquare.mk _ _ _ _ t.hom)
  have hu := unit_mateEquiv aX aY b K
  change RE.map (aX.unit.app K) ≫ (mateEquiv aX aY b).natTrans.app (CX.obj K) =
    aY.unit.app (RE.obj K) ≫ VY.map (b.natTrans.app K) at hu
  dsimp only [b] at hu
  rw [hi] at hu
  simpa only [Adjunction.homEquiv_unit, conjugateIsoEquiv_apply_inv,
    Iso.symm_inv] using hu.symm

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
  have h := coefficientMateHom
    (pbcActualDerivedAdjunction f (pbcIntegralDatum l E))
    (pbcActualDerivedAdjunction f (pbcIntegralDatum l L))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E L ι Y))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E L ι X))
    (pbcScalarOrdinaryPullIso l E L ι f) K
  simpa only [pbcScalarDirectImageIso, pbcScalarDirectImageMap,
    pbcActualScalarDirectImageMap, pbcScalarOrdinaryPullIso,
    purScalarRightDerivedComparison, asIso_hom] using h


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

private theorem tensorLinearEquivExistsUnique
    {R S A H H' : Type*} [CommRing R] [CommRing S]
    [AddCommGroup A] [Module R A] [Module S A] [SMulCommClass R S A]
    [AddCommGroup H] [AddCommGroup H'] [Module R H] [Module R H']
    (e : H ≃ₗ[R] H') :
    ∃! h : (A ⊗[R] H) ≃ₗ[S] (A ⊗[R] H'),
      ∀ a u, h (a ⊗ₜ u) = a ⊗ₜ e u := by
  let t := TensorProduct.congr (LinearEquiv.refl R A) e
  let h : _ ≃ₗ[S] _ :=
    { t.toAddEquiv with
      map_smul' := by
        intro a x
        change t (a • x) = a • t x
        induction x using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | tmul b u => rfl
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
  refine ⟨h, fun _ _ ↦ rfl, ?_⟩
  intro h' hh
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.toAddMonoidHom_injective
  apply AddMonoidHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a u => exact hh a u
  | add x y hx hy => simp only [map_add, hx, hy]

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
  exact tensorLinearEquivExistsUnique (purOrdinaryHomLinear l E f M K)


/-- The raw localized canonical adjunction, uniquely fixed on every pure tensor.
Source: fix-prop-adjunctions Step 1
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purRationalHom
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :=
  (purRationalHom_existsUnique l E f M K).exists.choose

private theorem purRationalHom_tmul
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E)))
    (a : Localization.Away (pbcUniformizer l E))
    (u : (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj ⟶ K.obj) :
    purRationalHom l E f M K (a ⊗ₜ u) = a ⊗ₜ purOrdinaryHom l E f M K u :=
  (purRationalHom_existsUnique l E f M K).exists.choose_spec a u

/-- The scalar map on the actual localized coefficient rings, including denominators.
Source: fix-prop-adjunctions Step 1
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purLocalizedCoefficientMap : Localization.Away (pbcUniformizer l E) →+*
    Localization.Away (pbcUniformizer l L) :=
  (pbcRationalCoefficientEquiv l L).symm.toRingHom.comp
    (ι.toRingHom.comp (pbcRationalCoefficientEquiv l E).toRingHom)

private theorem tensorSemilinearExistsUnique
    {R S A B H H' : Type*} [CommRing R] [CommRing S]
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module S B]
    [AddCommGroup H] [AddCommGroup H'] [Module R H] [Module S H']
    (φ : R →+* S) (k : A →+ B) (hk : ∀ r a, k (r • a) = φ r • k a)
    (g : H →+ H') (hg : ∀ r x, g (r • x) = φ r • g x) :
    ∃! e : (A ⊗[R] H) →+ (B ⊗[S] H'),
      ∀ a x, e (a ⊗ₜ x) = k a ⊗ₜ g x := by
  let b : A →+ H →+ (B ⊗[S] H') :=
    { toFun := fun a ↦
        { toFun := fun x ↦ k a ⊗ₜ g x
          map_zero' := by rw [g.map_zero, TensorProduct.tmul_zero]
          map_add' := fun x y ↦ by rw [g.map_add, TensorProduct.tmul_add] }
      map_zero' := by
        ext x
        change k 0 ⊗ₜ g x = 0
        rw [map_zero, TensorProduct.zero_tmul]
      map_add' := by
        intro a b
        ext x
        change k (a + b) ⊗ₜ g x = k a ⊗ₜ g x + k b ⊗ₜ g x
        rw [map_add, TensorProduct.add_tmul] }
  have hb (r : R) (a : A) (x : H) : b (r • a) x = b a (r • x) := by
    change k (r • a) ⊗ₜ g x = k a ⊗ₜ g (r • x)
    rw [hk, hg, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  refine ⟨TensorProduct.liftAddHom b hb, fun a x ↦ rfl, ?_⟩
  intro e he
  apply AddMonoidHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => exact he a x
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem purAmbientScalar_smul (W : Scheme.{u})
    {A B : PbcCompletedDerived W (pbcIntegralDatum l E)}
    (r : PbcIntegralRing l E) (g : A ⟶ B) :
    (pbcEmbeddingAmbientTensor l E L ι W).map (r • g) =
      pbcEmbeddingIntegerMap l E L ι r • (pbcEmbeddingAmbientTensor l E L ι W).map g := by
  exact scalarAdjunction (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E L ι W))
    r (pbcEmbeddingIntegerMap l E L ι r)
    (scalarExactDerived (pbcRestrict (pbcScalarCoefficientMap l E L ι W))
      (pbcEmbeddingIntegerMap l E L ι r) r (scalarRestrict l E L ι W r)) A B g

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
  have : (pbcDerivedRestrict (pbcScalarCoefficientMap l E L ι X)).Additive := by
    unfold pbcDerivedRestrict
    infer_instance
  have : (pbcDerivedRestrict (pbcScalarCoefficientMap l E L ι Y)).Additive := by
    unfold pbcDerivedRestrict
    infer_instance
  have : (pbcEmbeddingAmbientTensor l E L ι X).Additive :=
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E L ι X)).left_adjoint_additive
  have : (pbcEmbeddingAmbientTensor l E L ι Y).Additive :=
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E L ι Y)).left_adjoint_additive
  dsimp only [purScalarComplete]
  have hk (r : PbcIntegralRing l E) :
      purLocalizedCoefficientMap l E L ι
          (algebraMap _ (Localization.Away (pbcUniformizer l E)) r) =
        algebraMap _ (Localization.Away (pbcUniformizer l L))
          (pbcEmbeddingIntegerMap l E L ι r) := by
    apply (pbcRationalCoefficientEquiv l L).injective
    simp only [purLocalizedCoefficientMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, RingEquiv.apply_symm_apply, scalarRationalCoefficient]
    rfl
  have hks (r : PbcIntegralRing l E) (a : Localization.Away (pbcUniformizer l E)) :
      purLocalizedCoefficientMap l E L ι (r • a) =
        pbcEmbeddingIntegerMap l E L ι r • purLocalizedCoefficientMap l E L ι a := by
    change purLocalizedCoefficientMap l E L ι (r.down • a) =
      (pbcEmbeddingIntegerMap l E L ι r).down • purLocalizedCoefficientMap l E L ι a
    simp only [Algebra.smul_def]
    change purLocalizedCoefficientMap l E L ι (algebraMap _ _ r * a) =
      algebraMap _ _ (pbcEmbeddingIntegerMap l E L ι r) * _
    rw [map_mul, hk]
  let s : (((pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj M.obj) ⟶ K.obj) →+
      (((pbcActualStrictCompletedPull (pbcIntegralDatum l L) f).obj
        (purScalarComplete l E L ι Y M).obj) ⟶ (purScalarComplete l E L ι X K).obj) :=
    (Preadditive.leftComp ((pbcEmbeddingAmbientTensor l E L ι X).obj K.obj)
    (purScalarPullComparison l E f L ι M).inv).comp
      (pbcEmbeddingAmbientTensor l E L ι X).mapAddHom
  let t : (M.obj ⟶ (pbcActualDerivedPush f (pbcIntegralDatum l E)).obj K.obj) →+
      ((purScalarComplete l E L ι Y M).obj ⟶
        (pbcActualDerivedPush f (pbcIntegralDatum l L)).obj
          (purScalarComplete l E L ι X K).obj) :=
    (Preadditive.rightComp ((pbcEmbeddingAmbientTensor l E L ι Y).obj M.obj)
    ((pbcScalarDirectImageIso l E L ι f).hom.app K.obj)).comp
      (pbcEmbeddingAmbientTensor l E L ι Y).mapAddHom
  obtain ⟨a, ha, ua⟩ := tensorSemilinearExistsUnique
    (R := PbcIntegralRing l E) (S := PbcIntegralRing l L)
    (A := Localization.Away (pbcUniformizer l E))
    (B := Localization.Away (pbcUniformizer l L))
    (pbcEmbeddingIntegerMap l E L ι) (purLocalizedCoefficientMap l E L ι).toAddMonoidHom hks s
    (fun r u ↦ by
      change _ ≫ (pbcEmbeddingAmbientTensor l E L ι X).map (r • u) = _
      rw [purAmbientScalar_smul, Linear.comp_smul]; rfl)
  obtain ⟨b, hb, ub⟩ := tensorSemilinearExistsUnique
    (R := PbcIntegralRing l E) (S := PbcIntegralRing l L)
    (A := Localization.Away (pbcUniformizer l E))
    (B := Localization.Away (pbcUniformizer l L))
    (pbcEmbeddingIntegerMap l E L ι) (purLocalizedCoefficientMap l E L ι).toAddMonoidHom hks t
    (fun r u ↦ by
      change (pbcEmbeddingAmbientTensor l E L ι Y).map (r • u) ≫ _ = _
      rw [purAmbientScalar_smul, Linear.smul_comp]; rfl)
  refine ⟨(a, b), ⟨ha, hb⟩, ?_⟩
  rintro ⟨a', b'⟩ ⟨ha', hb'⟩
  exact Prod.ext (ua a' ha') (ub b' hb')


/-- The uniquely prescribed pair of rational scalar maps.
Source: fix-prop-adjunctions Step 1
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
def purRationalScalarMaps
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :=
  (purRationalScalarMaps_existsUnique l E f L ι M K).exists.choose


private theorem scalarMateHom
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {LE : C ⥤ D} {RE : D ⥤ C} {LL : C' ⥤ D'} {RL : D' ⥤ C'}
    (aE : LE ⊣ RE) (aL : LL ⊣ RL) (CY : C ⥤ C') (CX : D ⥤ D')
    (t : TwoSquare CY LE LL CX) {M : C} {K : D} (u : LE.obj M ⟶ K) :
    aL.homEquiv _ _ (t.app M ≫ CX.map u) =
      CY.map (aE.homEquiv M K u) ≫ (mateEquiv aE aL t).app K := by
  change aL.unit.app (CY.obj M) ≫ RL.map (t.natTrans.app M ≫ CX.map u) =
    CY.map (aE.unit.app M ≫ RE.map u) ≫ (mateEquiv aE aL t).natTrans.app K
  rw [CY.map_comp, RL.map_comp, Category.assoc]
  have hn := (mateEquiv aE aL t).natTrans.naturality u
  change CY.map (RE.map u) ≫ _ = _ ≫ RL.map (CX.map u) at hn
  rw [hn]
  have hh := (unit_mateEquiv aE aL t M).symm
  change aL.unit.app (CY.obj M) ≫ RL.map (t.natTrans.app M) =
    CY.map (aE.unit.app M) ≫ (mateEquiv aE aL t).natTrans.app (LE.obj M) at hh
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ RL.map (CX.map u)) hh

private theorem isoUnitConjugation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U P Q : C} {T R S : D} (e : P ≅ Q) (e' : R ≅ S) (b : S ≅ F.obj Q)
    (u : U ⟶ P) (u' : T ⟶ R) (v : U ⟶ Q) (v' : T ⟶ S) (θ : T ⟶ F.obj U)
    (h : u ≫ e.hom = v) (h' : u' ≫ e'.hom = v')
    (hc : v' ≫ b.hom = θ ≫ F.map v) :
    u' ≫ (e'.hom ≫ b.hom ≫ F.map e.inv) = θ ≫ F.map u := by
  rw [← Category.assoc u' e'.hom, h', ← Category.assoc, hc, Category.assoc,
    ← F.map_comp, ← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem purStrictScalarUnit
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E))) :
    (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l L) f).app
        (purScalarComplete l E L ι Y M).obj ≫ (purScalarPullComparison l E f L ι M).inv =
      (pbcScalarOrdinaryPullIso l E L ι f).hom.app M.obj ≫
        (pbcEmbeddingAmbientTensor l E L ι X).map
          ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app M.obj) := by
  have hE := (pbcActualCompletedPullback_tower (pbcIntegralDatum l E) f).exists.choose_spec M
  have hL := (pbcActualCompletedPullback_tower (pbcIntegralDatum l L) f).exists.choose_spec
    (purScalarComplete l E L ι Y M)
  have hh := isoUnitConjugation (pbcEmbeddingAmbientTensor l E L ι X)
    ((purStrictPullComparison l E f).app M)
    ((purStrictPullComparison l L f).app (purScalarComplete l E L ι Y M))
    ((pbcScalarCompletedPullIso l E L ι f).app M.obj)
    _ _ _ _ _ hE hL (scalarCompletedPull_unit l E L ι f M.obj)
  simpa only [purScalarPullComparison, Iso.trans_inv, Functor.mapIso_inv,
    Iso.symm_inv, Iso.app_inv, Iso.app_hom, Category.assoc] using hh

set_option linter.unusedVariables false in
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
  have forward (u : (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj
      M.obj ⟶ K.obj) :
      purOrdinaryHom l L f (purScalarComplete l E L ι Y M) (purScalarComplete l E L ι X K)
          ((purScalarPullComparison l E f L ι M).inv ≫
            (pbcEmbeddingAmbientTensor l E L ι X).map u) =
        (pbcEmbeddingAmbientTensor l E L ι Y).map (purOrdinaryHom l E f M K u) ≫
          (pbcScalarDirectImageIso l E L ι f).hom.app K.obj := by
    change (pbcActualDerivedAdjunction f (pbcIntegralDatum l L)).homEquiv _ _
      (_ ≫ ((purScalarPullComparison l E f L ι M).inv ≫ _)) = _
    rw [← Category.assoc, purStrictScalarUnit, Category.assoc, ← Functor.map_comp]
    have h := scalarMateHom (pbcActualDerivedAdjunction f (pbcIntegralDatum l E))
      (pbcActualDerivedAdjunction f (pbcIntegralDatum l L))
      (pbcEmbeddingAmbientTensor l E L ι Y) (pbcEmbeddingAmbientTensor l E L ι X)
      (TwoSquare.mk _ _ _ _ (pbcScalarOrdinaryPullIso l E L ι f).hom)
      ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app M.obj ≫ u)
    simpa only [purOrdinaryHom, Equiv.ofBijective_apply, pbcScalarDirectImageIso,
      pbcScalarDirectImageMap, pbcActualScalarDirectImageMap, pbcScalarOrdinaryPullIso,
      TwoSquare.mk, asIso_hom, purScalarComplete] using h
  refine ⟨forward, ?_⟩
  intro v
  apply (purOrdinaryHom l L f
    (purScalarComplete l E L ι Y M) (purScalarComplete l E L ι X K)).injective
  rw [Equiv.apply_symm_apply, forward, Equiv.apply_symm_apply]



private theorem purRationalScalarMaps_tmul
    (M : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete Y (pbcIntegralDatum l E)))
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete X (pbcIntegralDatum l E))) :
    (∀ a u, (purRationalScalarMaps l E f L ι M K).1 (a ⊗ₜ u) =
      purLocalizedCoefficientMap l E L ι a ⊗ₜ
        ((purScalarPullComparison l E f L ι M).inv ≫
          (pbcEmbeddingAmbientTensor l E L ι X).map u)) ∧
    (∀ a v, (purRationalScalarMaps l E f L ι M K).2 (a ⊗ₜ v) =
      purLocalizedCoefficientMap l E L ι a ⊗ₜ
        ((pbcEmbeddingAmbientTensor l E L ι Y).map v ≫
          (pbcScalarDirectImageIso l E L ι f).hom.app K.obj)) :=
  (purRationalScalarMaps_existsUnique l E f L ι M K).exists.choose_spec

attribute [local irreducible] purRationalHom purRationalScalarMaps
  purOrdinaryHomLinear

private theorem tensorSquare
    {R S A B H G H' G' : Type*} [CommRing R] [CommRing S]
    [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module S B]
    [AddCommGroup H] [AddCommGroup G] [AddCommGroup H'] [AddCommGroup G']
    [Module R H] [Module R G] [Module S H'] [Module S G']
    (e : A ⊗[R] H →+ A ⊗[R] G) (e' : B ⊗[S] H' →+ B ⊗[S] G')
    (a : A ⊗[R] H →+ B ⊗[S] H') (b : A ⊗[R] G →+ B ⊗[S] G')
    (k : A → B) (h : H → G) (h' : H' → G') (s : H → H') (t : G → G')
    (he : ∀ x u, e (x ⊗ₜ u) = x ⊗ₜ h u)
    (he' : ∀ x u, e' (x ⊗ₜ u) = x ⊗ₜ h' u)
    (ha : ∀ x u, a (x ⊗ₜ u) = k x ⊗ₜ s u)
    (hb : ∀ x u, b (x ⊗ₜ u) = k x ⊗ₜ t u)
    (hc : ∀ u, h' (s u) = t (h u)) : ∀ u, e' (a u) = b (e u) := by
  intro u
  induction u using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x u => rw [ha, he', he, hb, hc]
  | add u v hu hv => simp only [map_add, hu, hv]

private theorem inverseSquare
    {S T S' T' : Type*} (e : S ≃ T) (e' : S' ≃ T')
    (a : S → S') (b : T → T') (h : ∀ s, e' (a s) = b (e s)) :
    ∀ t, e'.symm (b t) = a (e.symm t) := by
  intro t
  apply e'.injective
  rw [Equiv.apply_symm_apply, h, Equiv.apply_symm_apply]


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
  have hE := purRationalHom_tmul l E f M K
  have hL := purRationalHom_tmul l L f
    (purScalarComplete l E L ι Y M) (purScalarComplete l E L ι X K)
  have hs := purRationalScalarMaps_tmul l E f L ι M K
  have forward := tensorSquare
    (purRationalHom l E f M K).toLinearMap.toAddMonoidHom
    (purRationalHom l L f (purScalarComplete l E L ι Y M)
      (purScalarComplete l E L ι X K)).toLinearMap.toAddMonoidHom
    (purRationalScalarMaps l E f L ι M K).1
    (purRationalScalarMaps l E f L ι M K).2
    (purLocalizedCoefficientMap l E L ι) _ _ _ _ hE hL hs.1 hs.2
    (purOrdinaryAdjunctionScalarCompatibility l E f L ι D hl M K).1
  exact ⟨forward, inverseSquare (purRationalHom l E f M K).toEquiv
    (purRationalHom l L f (purScalarComplete l E L ι Y M)
      (purScalarComplete l E L ι X K)).toEquiv
    (purRationalScalarMaps l E f L ι M K).1
    (purRationalScalarMaps l E f L ι M K).2 forward⟩



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

private theorem isoConjugationTower
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E) (σ : F ⋙ G ≅ H)
    {A₀ B₀ : C} {A₁ B₁ : D} {A₂ B₂ A₃ B₃ : E}
    (e₀ : A₀ ≅ B₀) (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂) (e₃ : A₃ ≅ B₃)
    (a : F.obj B₀ ≅ B₁) (b : G.obj B₁ ≅ B₂) (c : H.obj B₀ ≅ B₃)
    (t : A₂ ⟶ A₃) (t' : B₂ ⟶ B₃)
    (ht : t ≫ e₃.hom = e₂.hom ≫ t')
    (hc : G.map a.hom ≫ b.hom ≫ t' = σ.hom.app B₀ ≫ c.hom) :
    G.map (F.map e₀.hom ≫ a.hom ≫ e₁.inv) ≫
        (G.map e₁.hom ≫ b.hom ≫ e₂.inv) ≫ t =
      σ.hom.app A₀ ≫ (H.map e₀.hom ≫ c.hom ≫ e₃.inv) := by
  apply (cancel_mono e₃.hom).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [ht, Iso.inv_hom_id_assoc]
  rw [← G.map_comp_assoc e₁.inv e₁.hom, e₁.inv_hom_id, G.map_id,
    Category.id_comp, hc]
  have hn := σ.hom.naturality e₀.hom
  change G.map (F.map e₀.hom) ≫ σ.hom.app B₀ = σ.hom.app A₀ ≫ H.map e₀.hom at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem inverseIsoSquare
    {C : Type*} [Category C] {A B D E : C} (a : A ≅ B) (b : D ≅ E)
    (f : A ⟶ D) (g : B ⟶ E) (h : a.hom ≫ g = f ≫ b.hom) :
    a.inv ≫ f = g ≫ b.inv := by
  apply (cancel_epi a.hom).mp
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

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
  refine ⟨?_, pbcScalarDirectImage_coefficients l E L ι f N j K.obj⟩
  let F := pbcEmbeddingAmbientTensor l E L ι X
  let G := pbcEmbeddingAmbientTensor l L N j X
  let H := pbcEmbeddingAmbientTensor l E N (j.comp ι) X
  let σ := pbcAmbientScalarComp l E L N ι j X
  let e₀ := (purStrictPullComparison l E f).app M
  let e₁ := (purStrictPullComparison l L f).app (purScalarComplete l E L ι Y M)
  let e₂ := (purStrictPullComparison l N f).app
    (purScalarComplete l L N j Y (purScalarComplete l E L ι Y M))
  let e₃ := (purStrictPullComparison l N f).app
    (purScalarComplete l E N (j.comp ι) Y M)
  let a := (pbcScalarCompletedPullIso l E L ι f).symm.app M.obj
  let b := (pbcScalarCompletedPullIso l L N j f).symm.app
    (purScalarComplete l E L ι Y M).obj
  let c := (pbcScalarCompletedPullIso l E N (j.comp ι) f).symm.app M.obj
  let β := (pbcAmbientScalarComp l E L N ι j Y).hom.app M.obj
  have ht : (pbcActualStrictCompletedPull (pbcIntegralDatum l N) f).map β ≫ e₃.hom =
      e₂.hom ≫ (pbcActualCompletedPull f (pbcIntegralDatum l N)).map β := by
    exact (purStrictPullComparison l N f).hom.naturality (ObjectProperty.homMk
      (X := purScalarComplete l L N j Y (purScalarComplete l E L ι Y M))
      (Y := purScalarComplete l E N (j.comp ι) Y M) β)
  have hc : G.map a.hom ≫ b.hom ≫
      (pbcActualCompletedPull f (pbcIntegralDatum l N)).map β =
        σ.hom.app ((pbcActualCompletedPull f (pbcIntegralDatum l E)).obj M.obj) ≫ c.hom := by
    simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Category.assoc] using
      inverseIsoSquare (b.symm ≪≫ G.mapIso a.symm) c.symm
      ((pbcActualCompletedPull f (pbcIntegralDatum l N)).map β)
      (σ.hom.app ((pbcActualCompletedPull f (pbcIntegralDatum l E)).obj M.obj))
      (by simpa only [a, b, c, G, σ, β, purScalarComplete, Iso.trans_hom,
        Functor.mapIso_hom, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
        Category.assoc] using pbcScalarCompletedPull_coefficients l E L ι f N j M.obj)
  exact isoConjugationTower F G H σ e₀ e₁ e₂ e₃ a b c
    ((pbcActualStrictCompletedPull (pbcIntegralDatum l N) f).map β)
    ((pbcActualCompletedPull f (pbcIntegralDatum l N)).map β) ht hc


private theorem tensorSemilinearEquivExistsUnique
    {R S A B H H' : Type*} [CommRing R] [CommRing S]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module S B]
    [AddCommGroup H] [AddCommGroup H'] [Module R H] [Module S H']
    (φ : R ≃+* S) (k : A ≃+ B) (hk : ∀ r a, k (r • a) = φ r • k a)
    (g : H ≃+ H') (hg : ∀ r x, g (r • x) = φ r • g x) :
    ∃! e : (A ⊗[R] H) ≃+ (B ⊗[S] H'),
      ∀ a x, e (a ⊗ₜ x) = k a ⊗ₜ g x := by
  let : RingHomInvPair φ.toRingHom φ.symm.toRingHom := ⟨by
    ext x
    exact φ.symm_apply_apply x, by
    ext x
    exact φ.apply_symm_apply x⟩
  let : RingHomInvPair φ.symm.toRingHom φ.toRingHom := ⟨by
    ext x
    exact φ.apply_symm_apply x, by
    ext x
    exact φ.symm_apply_apply x⟩
  let a : LinearEquiv φ.toRingHom (σ' := φ.symm.toRingHom) A B := { k with map_smul' := hk }
  let h : LinearEquiv φ.toRingHom (σ' := φ.symm.toRingHom) H H' := { g with map_smul' := hg }
  refine ⟨(TensorProduct.congr a h).toAddEquiv, fun _ _ ↦ rfl, ?_⟩
  intro e he
  apply AddEquiv.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a x => exact he a x
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem purCoefficientModel_smul (W : Scheme.{u})
    {A B : PbcCompletedDerived W (pbcIntegralDatum l E)}
    (r : PbcIntegralRing l E) (g : A ⟶ B) :
    (purCoefficientModel l E W).functor.map (r • g) =
      r.down • (purCoefficientModel l E W).functor.map g := by
  have ht : ScalarLocalization.IsSemilinear
      (ULift.ringEquiv : PbcIntegralRing l E ≃+* _).symm.toRingHom
      (purCoefficientModel l E W).inverse := by
    intro A B a g
    change (integralDetailedTransport W l E).map (a • g) =
      ULift.up a • (integralDetailedTransport W l E).map g
    rw [(sfIntegralConstructible_linear l E W).1, Functor.map_comp,
      detailedTransport_action, Linear.smul_comp, Category.id_comp]
  exact inverseSemilinear
    (ULift.ringEquiv : PbcIntegralRing l E ≃+* _).symm
    (purCoefficientModel l E W).symm ht A B r g


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
  let Φ := purCoefficientModel l E W
  have : Φ.functor.Additive := by
    change (pbcRestrict (purCoefficientIso l E W).inv).mapDerivedCategory.Additive
    infer_instance
  let φ := (ULift.ringEquiv : PbcIntegralRing l E ≃+* Padic.coefficientExtensionIntegers l E)
  let k := (pbcRationalCoefficientEquiv l E).trans
    (sfRationalCoefficientEquiv l E).toRingEquiv.symm
  have hka (r : PbcIntegralRing l E) :
      k (algebraMap _ _ r) = algebraMap _ _ r.down := by
    apply (sfRationalCoefficientEquiv l E).injective
    change sfRationalCoefficientEquiv l E
      ((sfRationalCoefficientEquiv l E).symm
        (pbcRationalCoefficientEquiv l E (algebraMap _ _ r))) = _
    rw [AlgEquiv.apply_symm_apply, pbcCoefficient_algebraMap, AlgEquiv.commutes]
  have hk (r : PbcIntegralRing l E) (a : Localization.Away (pbcUniformizer l E)) :
      k (r • a) = φ r • k a := by
    change k (r.down • a) = r.down • k a
    simp only [Algebra.smul_def]
    change k (algebraMap _ _ r * a) = algebraMap _ _ r.down * k a
    rw [map_mul, hka]
  let g : (A ⟶ B) ≃+ (Φ.functor.obj A ⟶ Φ.functor.obj B) :=
    { Φ.fullyFaithfulFunctor.homEquiv with
      map_add' := fun x y ↦ Φ.functor.map_add (f := x) (g := y) }
  let h : (A ⟶ B) ≃+
      ((⟨Φ.functor.obj A, hA⟩ : sfIntegralConstructibleCategory l E W) ⟶
        ⟨Φ.functor.obj B, hB⟩) :=
    g.trans { ((sfIntegralConstructible l E W).fullyFaithfulι.homEquiv
      (X := ⟨Φ.functor.obj A, hA⟩) (Y := ⟨Φ.functor.obj B, hB⟩)).symm with
      map_add' := fun _ _ ↦ rfl }
  exact tensorSemilinearEquivExistsUnique φ k.toAddEquiv hk h
    (fun r g ↦ by
      apply ObjectProperty.hom_ext
      exact purCoefficientModel_smul l E W r g)


/-- Canonical coordinates in the actual raw constructible rational category.
Source: def-weil-rationalization-karoubi
(blueprint: lem-pur-ordinary-adjunction-scalar-compatibility). -/
@[irreducible]
def purRationalModelHom (W : Scheme.{u})
    (A B : PbcCompletedDerived W (pbcIntegralDatum l E))
    (hA : sfIntegralConstructible l E W ((purCoefficientModel l E W).functor.obj A))
    (hB : sfIntegralConstructible l E W ((purCoefficientModel l E W).functor.obj B)) :=
  (purRationalModelHom_existsUnique l E W A B hA hB).exists.choose

section BoundedProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem purBoundedIso (W : Scheme.{u})
    {A B : DerivedCategory (scalarReductionSource.{u, u} l E W)} (e : A ≅ B)
    (hA : sfIntegralConstructible l E W A) : sfIntegralConstructible l E W B := by
  obtain ⟨hc, a, b, hab, hr⟩ := hA
  refine ⟨complete_iso l E W e hc, a, b, hab, fun n ↦ ?_⟩
  let t := (scalarReductionDerivedExtension.{u, u} l E W n).mapIso e
  let Aₙ := Padic.coefficientExtensionRing l E (n + 1)
  let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  refine ⟨intrinsic_iso W Aₙ t (hr n).1, ?_⟩
  rw [← support_iso W Aₙ t]
  exact (hr n).2

private theorem purPushTowerIso
    (A : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hA : IsSfDerivedComplete l E X A)
    [HasProduct (sfDirectImageTerm l E f A)] (B : SfIntegralDirectImage l E f A) :
    Nonempty ((sfCompletedDerivedDirectImage l E f).obj A ≅ B.obj) := by
  let := completed_derived_products l E f
  let F := sfCompletedDerivedDirectImage l E f
  let a (n : ℕ) := (sfDerivedRestrictionComparison l E f n).app
    ((scalarReductionDerivedExtension.{u, u} l E X n).obj A)
  obtain ⟨hprod, δ, hδ⟩ := hA
  let := hprod
  let : HasProduct (fun n ↦ F.obj ((sfDerivedReductionRestricted l E X n).obj A)) :=
    hasProduct_of_equiv_of_iso (sfDirectImageTerm l E f A) _ (Equiv.refl ℕ) a
  obtain ⟨ε, hε⟩ := map_roos F
    (fun n ↦ (sfDerivedReductionTransition l E X n).app A) A
    (Pi.lift (fun n ↦ (sfDerivedReductionUnit l E X n).app A)) δ hδ
  let p (n : ℕ) := F.map ((sfDerivedReductionUnit l E X n).app A) ≫ (a n).hom
  have hR : ∃ hp : HasProduct (sfDirectImageTerm l E f A), let := hp
      ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f A)
        (F.obj A) (Pi.lift p) ε := by
    apply roos_transport
      (X := fun n ↦ F.obj ((sfDerivedReductionRestricted l E X n).obj A))
      (Y := sfDirectImageTerm l E f A)
      (fun n ↦ F.map ((sfDerivedReductionTransition l E X n).app A))
      (sfDirectImageTransition l E f A) (Iso.refl (F.obj A)) a
      (fun n ↦ F.map ((sfDerivedReductionUnit l E X n).app A)) p
    · intro n
      dsimp only [sfDirectImageTransition, a, Iso.app_hom, Iso.app_inv]
      simp only [Iso.hom_inv_id_app_assoc]
      rfl
    · intro n
      simp only [p, Iso.refl_hom, Category.id_comp]
    · refine ⟨inferInstance, ε, ?_⟩
      simpa only [Pi.lift_π] using hε
  obtain ⟨hp, ε', hε'⟩ := hR
  have hR' : ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f A)
      (F.obj A) (Pi.lift p) ε := by
    simpa only using (show ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E f A)
      (F.obj A) (Pi.lift p) ε from ⟨ε', hε'⟩)
  obtain ⟨ε'', hε''⟩ := hR'
  obtain ⟨e, _⟩ := roos_unique (sfDirectImageTransition l E f A)
    B.projection (Pi.lift p) B.boundary ε'' B.roos hε''
  exact ⟨e.symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem purPushCoefficientIso
    (A : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    Nonempty ((purCoefficientModel l E Y).functor.obj
      ((pbcActualDerivedPush f (pbcIntegralDatum l E)).obj A) ≅
      (sfCompletedDerivedDirectImage l E f).obj
        ((purCoefficientModel l E X).functor.obj A)) := by
  let P := pbcRestrict (purCoefficientIso l E X).hom
  let Q := pbcRestrict (purCoefficientIso l E Y).hom
  have hp (W : Scheme.{u}) :
      (pbcRestrict (purCoefficientIso l E W).hom).IsEquivalence :=
    restriction_isEquivalence ((adicLisseForget W).mapIso (purCoefficientIso l E W))
  let : P.IsEquivalence := hp X
  let : Q.IsEquivalence := hp Y
  let : P.Additive := pbcRestrict_additive _
  let : Q.Additive := pbcRestrict_additive _
  let : PreservesFiniteLimits P := pbcRestrict_limits _
  let : PreservesFiniteColimits P := pbcRestrict_colimits _
  let : PreservesFiniteLimits Q := pbcRestrict_limits _
  let : PreservesFiniteColimits Q := pbcRestrict_colimits _
  let : (completedModuleDirectImage f (pbcIntegralDatum l E)).Additive :=
    completedModuleDirectImage_additive f _
  obtain ⟨d, _⟩ := normalized_equivalence_square_exists.{u + 2, u + 1, u + 2}
    (sfCompletedModuleDirectImage l E f)
    (completedModuleDirectImage f (pbcIntegralDatum l E))
    P Q (completed_ordinary_comparison l E f)
  have transport (W : Scheme.{u}) :
      Nonempty ((pbcRestrict (purCoefficientIso l E W).hom).mapDerivedCategory ≅
        (purCoefficientModel l E W).inverse) := by
    let G := SheafOfModules.restrictScalars.{u + 1}
      (integralDetailedCoefficientComparison W l E).hom
    let : G.Additive := { map_add := fun {_ _} {_ _} ↦ rfl }
    let : PreservesFiniteLimits G := (integralDetailedCoefficientRestriction_exact W l E).1
    let : PreservesFiniteColimits G := (integralDetailedCoefficientRestriction_exact W l E).2
    have he := congrArg Iso.hom (purCoefficientIso_existsUnique l E W).exists.choose_spec
    change (adicLisseForget W).map (purCoefficientIso l E W).hom =
      (integralDetailedCoefficientComparison W l E).hom at he
    have hG : pbcRestrict (purCoefficientIso l E W).hom = G :=
      congrArg (fun φ ↦ SheafOfModules.restrictScalars φ) he
    have eG : pbcRestrict (purCoefficientIso l E W).hom ≅ G := eqToIso hG
    exact ⟨Functor.mapDerivedCategoryNatIso eG⟩
  let ΦX := purCoefficientModel l E X
  let ΦY := purCoefficientModel l E Y
  obtain ⟨tX⟩ := transport X
  obtain ⟨tY⟩ := transport Y
  let cX := tX.app (ΦX.functor.obj A)
  let cY := tY.app ((sfCompletedDerivedDirectImage l E f).obj (ΦX.functor.obj A))
  let e : (pbcActualDerivedPush f (pbcIntegralDatum l E)).obj A ≅
      ΦY.inverse.obj ((sfCompletedDerivedDirectImage l E f).obj (ΦX.functor.obj A)) :=
    (pbcActualDerivedPush f (pbcIntegralDatum l E)).mapIso (ΦX.unitIso.app A) ≪≫
      (pbcActualDerivedPush f (pbcIntegralDatum l E)).mapIso cX.symm ≪≫
      (d.app (ΦX.functor.obj A)).symm ≪≫ cY
  exact ⟨ΦY.functor.mapIso e ≪≫ ΦY.counitIso.app _⟩



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
  classical
  have hk : IsUnit (l : D.k) := by
    let := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    have : CharP D.k D.p :=
      charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)
  have hspec : IsUnit (l : Γ(Spec (.of D.k), ⊤)) := by
    simpa only [map_natCast] using hk.map (Scheme.ΓSpecIso (.of D.k)).inv.hom
  have hXi : IsUnit (l : Γ(X, ⊤)) := by
    simpa only [map_natCast] using hspec.map (X ↘ Spec (.of D.k)).appTop.hom
  have hYi : IsUnit (l : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using hspec.map (Y ↘ Spec (.of D.k)).appTop.hom
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of D.k))
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of D.k))
  have hXd := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
  have hYd := exists_topologicalKrullDim_le (Y ↘ Spec (.of D.k))
  have hXs (x : X) : IsUnit (l : X.presheaf.stalk x) := by
    simpa only [map_natCast] using hXi.map (X.presheaf.germ ⊤ x trivial).hom
  have hYs (y : Y) : IsUnit (l : Y.presheaf.stalk y) := by
    simpa only [map_natCast] using hYi.map (Y.presheaf.germ ⊤ y trivial).hom
  have hMb := (purCoefficientModel_bounded_predicate l E Y hYd hYi M.obj).mpr hM
  have hKb := (purCoefficientModel_bounded_predicate l E X hXd hXi K.obj).mpr hK
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (purCoefficientModel_bounded_predicate l E X hXd hXi _).mp
    let d := pbcIntegralDatum l E
    obtain ⟨a, b, hp⟩ := (pbcUniformReductionCriterion l E Y M.obj).mp
      ⟨hMb.2.1, hMb.2.2⟩
    have hb : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcCompletedReduction Y d n).obj M.obj)) := by
      intro n q hq
      let R := pbcRestrict (pbcLevelConstantComparison Y d n).hom
      have := (hp n).1
      have := (hp n).2.1
      have hz : IsZero ((DerivedCategory.homologyFunctor _ q).obj
          ((pbcConstantReduction Y d n).obj M.obj)) := by
        rcases hq with hq | hq
        · exact DerivedCategory.isZero_of_isGE _ a q hq
        · exact DerivedCategory.isZero_of_isLE _ b q hq
      have hz' := hz.of_iso ((R.mapDerivedCategoryHomologyFunctorIso q).app
        ((pbcCompletedReduction Y d n).obj M.obj))
      have : R.Faithful := by
        constructor
        intro A B α β h
        apply SheafOfModules.Hom.ext
        exact (PresheafOfModules.restrictScalars _).map_injective
          (congrArg SheafOfModules.Hom.val h)
      apply (IsZero.iff_id_eq_zero _).mpr
      apply R.map_injective
      simpa using (IsZero.iff_id_eq_zero _).mp hz'
    obtain ⟨hc, hcons, hbounds⟩ := pbc_constructible_reduction_pullback l E f a b M.obj
      M.property (fun n ↦ (hp n).2.2) hb
    exact (pbc_constructible_reduction_criterion l E X a b _ hbounds).mpr ⟨hc, hcons⟩
  · let : X.Over (Spec (.of D.k)) := ⟨f ≫ (Y ↘ Spec (.of D.k))⟩
    let : LocallyOfFiniteType (X ↘ Spec (.of D.k)) :=
      locallyOfFiniteType_comp f (Y ↘ Spec (.of D.k))
    let : QuasiCompact (X ↘ Spec (.of D.k)) :=
      quasiCompact_comp f (Y ↘ Spec (.of D.k))
    let : f.IsOver (Spec (.of D.k)) := ⟨rfl⟩
    let A := (purCoefficientModel l E X).functor.obj K.obj
    have hc := (purCoefficientModel_predicates l E X K.obj).2.mp K.property
    obtain ⟨hex, hcons, _⟩ := sfIntegralDirectImage_constructible D.k l hk E f A hK
    obtain ⟨hprod, ⟨B⟩⟩ := hex
    let := hprod
    obtain ⟨e⟩ := purPushTowerIso l E f A hc B
    obtain ⟨c⟩ := purPushCoefficientIso l E f K.obj
    exact purBoundedIso l E Y (c ≪≫ e).symm (hcons B).1
  · apply (purCoefficientModel_bounded_predicate l L Y hYd hYi _).mp
    exact pbcEmbeddingAmbientTensor_preserves l E L ι Y hYd hYs ⟨M.obj, hMb⟩
  · apply (purCoefficientModel_bounded_predicate l L X hXd hXi _).mp
    exact pbcEmbeddingAmbientTensor_preserves l E L ι X hXd hXs ⟨K.obj, hKb⟩


end BoundedProof

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

private theorem exists_transport_iff
    {I : Type*} {S : Type*} {T : Type*} {J : I → Prop}
    {S' : ∀ i, J i → Type*} {T' : ∀ i, J i → Type*}
    (e : S ≃ T) (e' : ∀ i h, S' i h ≃ T' i h)
    (a : ∀ i h, S → S' i h) (b : ∀ i h, T → T' i h)
    (hc : ∀ i h s, e' i h (a i h s) = b i h (e s)) (s t : S) :
    (∃ i h, a i h s = a i h t) ↔ (∃ i h, b i h (e s) = b i h (e t)) := by
  constructor
  · rintro ⟨i, h, heq⟩
    exact ⟨i, h, (hc i h s).symm.trans ((congrArg (e' i h) heq).trans (hc i h t))⟩
  · rintro ⟨i, h, heq⟩
    exact ⟨i, h, (e' i h).injective ((hc i h s).trans (heq.trans (hc i h t).symm))⟩

private theorem inverseRelation
    {S : Type*} {T : Type*} (e : S ≃ T) (r : S → S → Prop) (q : T → T → Prop)
    (h : ∀ s t, r s t ↔ q (e s) (e t)) :
    ∀ s t, q s t ↔ r (e.symm s) (e.symm t) := by
  intro s t
  simpa only [Equiv.apply_symm_apply] using (h (e.symm s) (e.symm t)).symm

attribute [local irreducible] AlgebraicallyClosedCoefficients.coefficientInclusion
  purScalarComplete purScalarPullComparison

set_option linter.unusedSectionVars false in
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
  have forward (s t) : purCommonStageSourceRelated l f Ω A M K s t ↔
      purCommonStageTargetRelated l f Ω A M K
        (purRationalHom l (Coefficient.{u} l Ω A) f M K s)
        (purRationalHom l (Coefficient.{u} l Ω A) f M K t) := by
    exact exists_transport_iff (I := Padic.FiniteCoefficientFields l Ω)
      (J := fun B ↦ A ≤ B)
      (purRationalHom l (Coefficient.{u} l Ω A) f M K).toEquiv
      (fun B h ↦ (purRationalHom l (Coefficient.{u} l Ω B) f
        (purScalarComplete l (Coefficient.{u} l Ω A) (Coefficient.{u} l Ω B)
          (coefficientInclusion l Ω A B h) Y M)
        (purScalarComplete l (Coefficient.{u} l Ω A) (Coefficient.{u} l Ω B)
          (coefficientInclusion l Ω A B h) X K)).toEquiv)
      (fun B h ↦ (purRationalScalarMaps l (Coefficient.{u} l Ω A) f
        (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h) M K).1)
      (fun B h ↦ (purRationalScalarMaps l (Coefficient.{u} l Ω A) f
        (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h) M K).2)
      (fun B h ↦ (purRationalAdjunctionScalarCompatibility l (Coefficient.{u} l Ω A) f
        (Coefficient.{u} l Ω B) (coefficientInclusion l Ω A B h) D hl M K).1) s t
  exact ⟨forward, inverseRelation
    (purRationalHom l (Coefficient.{u} l Ω A) f M K).toEquiv
    (purCommonStageSourceRelated l f Ω A M K)
    (purCommonStageTargetRelated l f Ω A M K) forward⟩



end CommonStage
end WeilConjectures
