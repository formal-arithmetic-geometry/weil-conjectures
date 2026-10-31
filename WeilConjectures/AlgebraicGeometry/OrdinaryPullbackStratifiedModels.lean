/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryIntegralPullbackConstruction
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReductionSupplement
import all WeilConjectures.AlgebraicGeometry.ScalarPerfectFiniteFree
import all WeilConjectures.AlgebraicGeometry.StrictPerfectRingedPullbackModel
import WeilConjectures.AlgebraicGeometry.OrdinaryCompletedPullbackExact
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
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
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.AlgebraicGeometry.CompletedCoefficientRingedCoherence
import all WeilConjectures.AlgebraicGeometry.FiniteProjectiveModelPullback

/-!
# Ordinary pullback of stratified perfect models

Source: Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15; Stacks Project,
Tags 0D6D, 04IF, 06YQ and 06YY
(blueprint: lem-tw-ordinary-pullback-stratified-models).

All functors below are ordinary ringed pullback, before completion. The published
ordinary coefficient map and its total derived functor are reused verbatim.
The comparisons retain their ordinary generators and derived computation counits.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.hasDerived
attribute [-instance] CategoryTheory.SubterminalImageCalculus.smallSheafify
attribute [-instance] CategoryTheory.SubterminalImageCalculus.smallLocalCriterion

attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralTowerHasDerivedCategory
attribute [-instance] WeilConjectures.integralCoefficientRingSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings

namespace WeilConjectures.OrdinaryStratifiedModels

private theorem modelCommSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} T

private theorem modelAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} T

private theorem modelAbWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  (modelAbSheafify T).isRightAdjoint

private theorem modelAbLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} T

private theorem modelCompose (T : Scheme.{u}) :
    (ProEt.topology T).HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := by
  infer_instance


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical completed coefficient map in inverse-image form.
Source: the projection formula defining c_f in the statement; Stacks 06YY
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def coefficientMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (proEtaleSheafInverseImage f RingCat.{u + 1}).obj
        (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      completedIntegralCoefficientSheafUnrestricted l E X :=
  ((proEtaleSheafAdjunction f RingCat.{u + 1}).homEquiv _ _).symm
    (ordinaryIntegralDirectRingMap l E f)

/-- The inverse-image compositor, the mate of fibre-product associativity on direct image.
Source: Stacks 03CB (blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def inverseComp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z) :
    proEtaleSheafInverseImage (h ≫ k) RingCat.{u + 1} ≅
      proEtaleSheafInverseImage k RingCat.{u + 1} ⋙
        proEtaleSheafInverseImage h RingCat.{u + 1} :=
  ((conjugateIsoEquiv
    (proEtaleSheafAdjunction (h ≫ k) RingCat.{u + 1})
    ((proEtaleSheafAdjunction k RingCat.{u + 1}).comp
      (proEtaleSheafAdjunction h RingCat.{u + 1}))).symm
    (Functor.sheafPushforwardContinuousComp'
      (eFG := (MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h k).symm)
      RingCat.{u + 1} (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)).symm).symm

private def directComp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z) :=
  Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k).symm
    RingCat.{u + 1} (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)

private theorem finiteDirect_comp {X Y Z : Scheme.{u}}
    (h : X ⟶ Y) (k : Y ⟶ Z) (n : ℕ) :
    ordinaryIntegralFiniteDirectRingMap l E k n ≫
      (proEtaleSheafDirectImage k RingCat.{u + 1}).map
        (ordinaryIntegralFiniteDirectRingMap l E h n) ≫
          (directComp h k).hom.app (integralCoefficientSheaf l E X n) =
      ordinaryIntegralFiniteDirectRingMap l E (h ≫ k) n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  exact congrArg (fun a ↦ (forget₂ CommRingCat RingCat).map (a.hom.app W))
    (completedDirect_comp.{u, u} h k (CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

private theorem directProjection {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ordinaryIntegralDirectRingMap l E f ≫
        (proEtaleSheafDirectImage f RingCat.{u + 1}).map
          (limit.π (integralCoefficientSheafSystem l E X) (op n)) =
      limit.π (integralCoefficientSheafSystem l E Y) (op n) ≫
        ordinaryIntegralFiniteDirectRingMap l E f n :=
  (ordinaryIntegralDirectRingMap_existsUnique l E f).exists.choose_spec n

private theorem direct_comp_projection
    {C D H : Type*} [Category C] [Category D] [Category H]
    (F : D ⥤ C) (G : H ⥤ D) (J : H ⥤ C) (α : G ⋙ F ⟶ J)
    {A A' : C} {B B' : D} {T T' : H}
    (a : A ⟶ F.obj B) (b : B ⟶ G.obj T)
    (a' : A' ⟶ F.obj B') (b' : B' ⟶ G.obj T')
    (p : A ⟶ A') (q : B ⟶ B') (r : T ⟶ T')
    (ha : a ≫ F.map q = p ≫ a') (hb : b ≫ G.map r = q ≫ b') :
    (a ≫ F.map b ≫ α.app T) ≫ J.map r = p ≫ a' ≫ F.map b' ≫ α.app T' := by
  simp only [Category.assoc]
  rw [← α.naturality, Functor.comp_map]
  rw [← F.map_comp_assoc, hb, F.map_comp]
  simp only [← Category.assoc]
  rw [ha]

private theorem direct_comp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z) :
    ordinaryIntegralDirectRingMap l E k ≫
      (proEtaleSheafDirectImage k RingCat.{u + 1}).map
        (ordinaryIntegralDirectRingMap l E h) ≫
          (directComp h k).hom.app (completedIntegralCoefficientSheafUnrestricted l E X) =
      ordinaryIntegralDirectRingMap l E (h ≫ k) := by
  apply (ordinaryIntegralDirectRingMap_existsUnique l E (h ≫ k)).unique
  · intro n
    exact (direct_comp_projection
      (proEtaleSheafDirectImage k RingCat.{u + 1})
      (proEtaleSheafDirectImage h RingCat.{u + 1})
      (proEtaleSheafDirectImage (h ≫ k) RingCat.{u + 1}) (directComp h k).hom
      (ordinaryIntegralDirectRingMap l E k) (ordinaryIntegralDirectRingMap l E h)
      (ordinaryIntegralFiniteDirectRingMap l E k n)
      (ordinaryIntegralFiniteDirectRingMap l E h n)
      (limit.π (integralCoefficientSheafSystem l E Z) (op n))
      (limit.π (integralCoefficientSheafSystem l E Y) (op n))
      (limit.π (integralCoefficientSheafSystem l E X) (op n))
      (directProjection l E k n) (directProjection l E h n)).trans
        (congrArg (fun m ↦ limit.π (integralCoefficientSheafSystem l E Z) (op n) ≫ m)
          (finiteDirect_comp l E h k n))
  · exact (ordinaryIntegralDirectRingMap_existsUnique l E (h ≫ k)).exists.choose_spec

private theorem coefficientMate
    {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L' ⊣ R')
    (d : R' ≅ R) {A : C} {B : D} (t : L'.obj A ⟶ B) :
    a.homEquiv A B
        (((conjugateIsoEquiv a b).symm d.symm).inv.app A ≫ t) =
      b.homEquiv A B t ≫ d.hom.app B := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc]
  change (a.unit.app A ≫
      R.map (((conjugateEquiv b a).symm d.hom).app A)) ≫ R.map t = _
  rw [← unit_conjugateEquiv_symm b a d.hom A, Category.assoc, ← d.hom.naturality]
  simp only [Category.assoc]

/-- Completed coefficient composition and all its finite projections.
Source: Stacks 03CB, 0H7J and the inverse limit defining B
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: apply constant-coefficient-composition at R/t^(n+1). Substitute the defining
projection equations for c_h and c_k. Naturality of the inverse-image compositor
identifies the result with the finite projection of c_(h k). Limit projections are
jointly monic, proving the coefficient equality. This also proves the displayed
projection equations. Apply this to the two equal composites of the pullback square. -/
theorem coefficientMap_comp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z) :
    coefficientMap l E (h ≫ k) =
      (inverseComp h k).hom.app (completedIntegralCoefficientSheafUnrestricted l E Z) ≫
        (proEtaleSheafInverseImage h RingCat.{u + 1}).map (coefficientMap l E k) ≫
          coefficientMap l E h ∧
    ∀ n : ℕ, coefficientMap l E (h ≫ k) ≫
        limit.π (integralCoefficientSheafSystem l E X) (op n) =
      (proEtaleSheafInverseImage (h ≫ k) RingCat.{u + 1}).map
          (limit.π (integralCoefficientSheafSystem l E Z) (op n)) ≫
        ((proEtaleSheafAdjunction (h ≫ k) RingCat.{u + 1}).homEquiv _ _).symm
          (ordinaryIntegralFiniteDirectRingMap l E (h ≫ k) n) := by
  constructor
  · let a := proEtaleSheafAdjunction (h ≫ k) RingCat.{u + 1}
    let b := (proEtaleSheafAdjunction k RingCat.{u + 1}).comp
      (proEtaleSheafAdjunction h RingCat.{u + 1})
    apply (a.homEquiv _ _).injective
    change a.homEquiv _ _ ((a.homEquiv _ _).symm _) = _
    rw [Equiv.apply_symm_apply]
    change _ = a.homEquiv _ _
      (((conjugateIsoEquiv a b).symm (directComp h k).symm).inv.app _ ≫ _)
    rw [coefficientMate, Adjunction.comp_homEquiv]
    change _ = (proEtaleSheafAdjunction k RingCat.{u + 1}).homEquiv _ _
      ((proEtaleSheafAdjunction h RingCat.{u + 1}).homEquiv _ _
        ((proEtaleSheafInverseImage h RingCat.{u + 1}).map (coefficientMap l E k) ≫
          coefficientMap l E h)) ≫ _
    rw [Adjunction.homEquiv_naturality_left]
    simp only [coefficientMap, Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_naturality_right]
    simp only [Equiv.apply_symm_apply]
    exact (direct_comp l E h k).symm
  · intro n
    let a := proEtaleSheafAdjunction (h ≫ k) RingCat.{u + 1}
    let πX : completedIntegralCoefficientSheafUnrestricted l E X ⟶
        integralCoefficientSheaf l E X n :=
      limit.π (integralCoefficientSheafSystem l E X) (op n)
    let πZ : completedIntegralCoefficientSheafUnrestricted l E Z ⟶
        integralCoefficientSheaf l E Z n :=
      limit.π (integralCoefficientSheafSystem l E Z) (op n)
    change coefficientMap l E (h ≫ k) ≫ πX =
      (proEtaleSheafInverseImage (h ≫ k) RingCat.{u + 1}).map πZ ≫
        (a.homEquiv _ _).symm (ordinaryIntegralFiniteDirectRingMap l E (h ≫ k) n)
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
    simp only [a, coefficientMap, Equiv.apply_symm_apply]
    exact directProjection l E (h ≫ k) n

/-- The existing constant-to-completion map, retaining commutativity.
Source: the constant quotient cone in completed coefficients
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def scalar (T : Scheme.{u}) :
    adicLisseConstantRing T (PbcIntegralRing l E) ⟶
      completedIntegralCommRingSheafUnrestricted l E T :=
  (sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).preimage
    (integralConstantToCompletionOfUniverses l E T)

/-- B_T tensor_R N, using the existing constant-module and scalar-extension functors.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def modelModule (T : Scheme.{u}) :
    ModuleCat.{u + 1} (PbcIntegralRing l E) ⥤ integralTowerModules l E T :=
  adicLisseConstantModules T (PbcIntegralRing l E) ⋙ completedConstantExtension T (scalar l E T)

/-- Additivity of the existing constant-module realization and scalar extension.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: the constant presheaf, its additive sheafification and extension of scalars
are additive. Their composite therefore preserves addition on module morphisms. -/
@[instance] theorem modelModule_additive (T : Scheme.{u}) :
    (modelModule l E T).Additive := by
  have := AlgebraicGeometry.Scheme.CompletedConstantReduction.constant_additive T
    (PbcIntegralRing l E)
  unfold modelModule
  infer_instance

/-- Termwise realization of a scalar complex; this uses ordinary sheaf tensor product.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def modelComplex (T : Scheme.{u}) :
    CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ ⥤
      CochainComplex (integralTowerModules l E T) ℤ :=
  completedConstantMapComplex (modelModule l E T) inferInstance

/-- The published scalar-extension witness has exactly the sheaf tensor objects.
Source: Stacks 03EK, 06YY (blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: this is the object specification in derived-change-of-rings, applied to
scalar; compose that specification with the constant-module functor. -/
theorem modelModule_obj (T : Scheme.{u}) (N : ModuleCat.{u + 1} (PbcIntegralRing l E)) :
    (modelModule l E T).obj N = SheafOfModules.changeOfRings (scalar l E T)
      ((adicLisseConstantModules T (PbcIntegralRing l E)).obj N) := by
  have : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let := HasDerivedCategory.standard
    (completedConstantModules T (adicLisseConstantRing T (PbcIntegralRing l E)))
  let := HasDerivedCategory.standard
    (completedConstantModules T (completedIntegralCommRingSheafUnrestricted l E T))
  exact (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (scalar l E T)).choose_spec.choose ((adicLisseConstantModules T
      (PbcIntegralRing l E)).obj N)

/-- The actual section b tensor x of the ordinary constant realization.
Source: Stacks 03EK; Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def modelSection (T : Scheme.{u}) (N : ModuleCat.{u + 1} (PbcIntegralRing l E))
    (W : T.ProEtᵒᵖ) (b : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj W)
    (x : N) : ((modelModule l E T).obj N).val.obj W :=
  (eqToHom (modelModule_obj l E T N).symm).val.app W
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf (scalar l E T)
        ((adicLisseConstantModules T (PbcIntegralRing l E)).obj N)).presheaf).app W
      (b ⊗ₜ[(adicLisseConstantRing T (PbcIntegralRing l E)).obj.obj W,
        ((scalar l E T).hom.app W).hom]
          completedConstantGenerator T (PbcIntegralRing l E) N W x))

section TensorModels

attribute [local instance] modelCommSheafify modelAbSheafify modelAbWeakSheafify
  modelAbLocallyBijective modelCompose

private abbrev tensorModel (T : Scheme.{u}) :
    ModuleCat.{u + 1} (PbcIntegralRing l E) ⥤ integralTowerModules l E T :=
  SheafOfModules.scalarPerfectFunctor.{u + 1, u, u + 1} (ProEt.topology T) (PbcIntegralRing l E)
    (scalar l E T)

private instance tensorModelAdditive (T : Scheme.{u}) : (tensorModel l E T).Additive :=
  SheafOfModules.scalarPerfectFunctor_additive.{u + 1, u, u + 1} _ _ _

private def tensorModelUnitIso (T : Scheme.{u}) :
    (tensorModel l E T).obj (ModuleCat.of (PbcIntegralRing l E) (PbcIntegralRing l E)) ≅
      SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T) := by
  have := SheafOfModules.constantUnitHom_isIso.{u + 1, u, u + 1}
    (ProEt.topology T) (PbcIntegralRing l E)
  exact (SheafOfModules.scalarPerfectExtensionFunctor.{u + 1, u, u + 1} (ProEt.topology T)
    (scalar l E T)).mapIso
      (asIso (SheafOfModules.constantUnitHom.{u + 1, u, u + 1}
        (ProEt.topology T) (PbcIntegralRing l E))) ≪≫
        SheafOfModules.scalarExtensionUnitIso.{u + 1, u, u + 1} (scalar l E T)

private def tensorModelFreeIso (T : Scheme.{u}) (n : ℕ) :
    (tensorModel l E T).obj
        (ModuleCat.of (PbcIntegralRing l E) (Fin n → PbcIntegralRing l E)) ≅
      ∏ᶜ fun _ : Fin n ↦
        SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E T) :=
  (tensorModel l E T).mapIso (ModuleCat.piIsoPi
    (fun _ : Fin n ↦ ModuleCat.of (PbcIntegralRing l E) (PbcIntegralRing l E))).symm ≪≫
      PreservesProduct.iso (tensorModel l E T)
        (fun _ : Fin n ↦ ModuleCat.of (PbcIntegralRing l E) (PbcIntegralRing l E)) ≪≫
      Pi.mapIso (fun _ : Fin n ↦ tensorModelUnitIso l E T)

private theorem tensorModel_flat (T : Scheme.{u})
    (N : ModuleCat.{u + 1} (PbcIntegralRing l E))
    [Module.Finite (PbcIntegralRing l E) N]
    [Module.Projective (PbcIntegralRing l E) N] :
    SheafOfModules.IsFlatOnSite
      (J := ProEt.topology T) (R := completedIntegralCommRingSheafUnrestricted l E T)
      ((tensorModel l E T).obj N) := by
  obtain ⟨n, p, i, _, _, h⟩ :=
    Module.Finite.exists_comp_eq_id_of_projective (PbcIntegralRing l E) N
  let i' : N ⟶ ModuleCat.of (PbcIntegralRing l E) (Fin n → PbcIntegralRing l E) :=
    ModuleCat.ofHom i
  let p' : ModuleCat.of (PbcIntegralRing l E) (Fin n → PbcIntegralRing l E) ⟶ N :=
    ModuleCat.ofHom p
  have hip : i' ≫ p' = 𝟙 N := ModuleCat.hom_ext h
  apply SheafOfModules.flat_finiteFree_retract
    (completedIntegralCommRingSheafUnrestricted l E T) _ n
    ((tensorModel l E T).map i' ≫ (tensorModelFreeIso l E T n).hom)
    ((tensorModelFreeIso l E T n).inv ≫ (tensorModel l E T).map p')
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hip]
  exact (tensorModel l E T).map_id N

private def modelObjectIso (T : Scheme.{u})
    (N : ModuleCat.{u + 1} (PbcIntegralRing l E)) :
    (modelModule l E T).obj N ≅ (tensorModel l E T).obj N := by
  refine eqToIso (modelModule_obj l E T N) ≪≫ ?_
  apply (PresheafOfModules.sheafification (𝟙 _)).mapIso
  exact PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro V W i
    apply ModuleCat.hom_ext
    ext t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul b x =>
      exact (Classical.choose_spec
        (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1}
          (scalar l E T) _ i) b x).trans
        (SheafOfModules.changeOfRingsMap_tmulOfUniverses
          (scalar l E T) _ i b x).symm)

end TensorModels

section ModelComparison

attribute [local instance] modelCommSheafify modelAbSheafify modelAbWeakSheafify
  modelAbLocallyBijective modelCompose

private theorem modelMap (T : Scheme.{u})
    {M N : ModuleCat.{u + 1} (PbcIntegralRing l E)} (f : M ⟶ N) :
    (modelModule l E T).map f = eqToHom (modelModule_obj l E T M) ≫
      SheafOfModules.changeOfRingsHom (scalar l E T) _
        ((adicLisseConstantModules T (PbcIntegralRing l E)).map f) ≫
      eqToHom (modelModule_obj l E T N).symm := by
  have : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _
  let := HasDerivedCategory.standard
    (completedConstantModules T (adicLisseConstantRing T (PbcIntegralRing l E)))
  let := HasDerivedCategory.standard
    (completedConstantModules T (completedIntegralCommRingSheafUnrestricted l E T))
  exact (SheafOfModules.derivedChangeOfRingsIndependentCoefficients.{u + 2, u + 1, u + 1, u}
    (scalar l E T)).choose_spec.choose_spec.choose
      ((adicLisseConstantModules T (PbcIntegralRing l E)).map f)

private def modelFunctorIso (T : Scheme.{u}) :
    modelModule l E T ≅ FiniteProjectivePullback.model l E T :=
  NatIso.ofComponents (fun M ↦ modelObjectIso l E T M) (by
    intro M N f
    rw [modelMap]
    dsimp only [modelObjectIso, Iso.trans_hom, eqToIso.hom]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    congr 1
    let F := PresheafOfModules.sheafification
      (𝟙 (completedIntegralCoefficientSheafUnrestricted l E T).obj)
    change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1)

private theorem modelFunctorIso_section (T : Scheme.{u})
    (M : ModuleCat.{u + 1} (PbcIntegralRing l E)) (W : T.ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj W) (x : M) :
    ((modelFunctorIso l E T).hom.app M).val.app W (modelSection l E T M W b x) =
      FiniteProjectivePullback.modelSection l E T M W b x := by
  dsimp only [modelFunctorIso, NatIso.ofComponents_hom_app, modelObjectIso, Iso.trans_hom,
    eqToIso.hom, modelSection]
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply]
  simp only [← ConcreteCategory.comp_apply, ← PresheafOfModules.comp_app,
    ← SheafOfModules.comp_val, eqToHom_trans, eqToHom_refl,
    Category.id_comp]
  change (toSheafify (D := AddCommGrpCat.{u + 1}) (ProEt.topology T) _ ≫ _).app W _ = _
  erw [← toSheafify_naturality]
  rfl

private theorem modelFunctorIso_inv_section (T : Scheme.{u})
    (M : ModuleCat.{u + 1} (PbcIntegralRing l E)) (W : T.ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted l E T).obj.obj W) (x : M) :
    ((modelFunctorIso l E T).inv.app M).val.app W
      (FiniteProjectivePullback.modelSection l E T M W b x) =
        modelSection l E T M W b x := by
  rw [← modelFunctorIso_section l E T M W b x]
  exact ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.val.app W) ((modelFunctorIso l E T).app M).hom_inv_id)
      (modelSection l E T M W b x)

private theorem modelGenerator_ext (T : Scheme.{u})
    (N : ModuleCat.{u + 1} (PbcIntegralRing l E)) (M : integralTowerModules l E T)
    (a b : (modelModule l E T).obj N ⟶ M)
    (h : ∀ x : N, a.val.app (op (⊤_ T.ProEt))
        (modelSection l E T N (op (⊤_ T.ProEt)) 1 x) =
      b.val.app (op (⊤_ T.ProEt))
        (modelSection l E T N (op (⊤_ T.ProEt)) 1 x)) : a = b := by
  apply (cancel_epi ((modelFunctorIso l E T).inv.app N)).1
  apply ((FiniteProjectivePullback.modelAdjunction l E T (⊤_ T.ProEt)
    terminalIsTerminal).homEquiv N M).injective
  ext x
  simp only [FiniteProjectivePullback.modelAdjunction_apply, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply, modelFunctorIso_inv_section]
  exact h x

end ModelComparison

attribute [local irreducible] modelFunctorIso
  FiniteProjectivePullback.allComparison

/-- The ordinary model comparison, uniquely normalized on constant generators.
Its naturality applies to every splitting and every idempotent matrix over R, so
it restricts to precisely the same finite-projective summand.
Source: Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15; Stacks 03EK
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: on a finite free module send b tensor (a e_j) to b c_f(a) e_j, with
inverse b e_j mapped to b tensor e_j. The coefficient map preserves every constant
R-scalar at every finite projection, hence preserves the matrix of an idempotent.
Restrict both inverse maps to its image. More generally the same balanced-tensor
formula works for every scalar module, and commutes with every scalar linear map.
Sheafification gives the natural isomorphism. The adjunction-unit images generate
pullback locally, proving uniqueness from the displayed equation. -/
theorem modelPullback_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! γ : modelModule l E Y ⋙ ordinaryIntegralModulePull l E f ≅ modelModule l E X,
      ∀ (N : ModuleCat.{u + 1} (PbcIntegralRing l E)) (W : Y.ProEt) (x : N),
        ((γ.hom.app N).val.app (op ((proEtaleBaseChange f).obj W)))
          ((((ordinaryIntegralModuleAdjunction l E f).unit.app
              ((modelModule l E Y).obj N)).val.app (op W))
            (modelSection l E Y N (op W) 1 x)) =
          modelSection l E X N (op ((proEtaleBaseChange f).obj W)) 1 x := by
  let γ : modelModule l E Y ⋙ ordinaryIntegralModulePull l E f ≅ modelModule l E X :=
    Functor.isoWhiskerRight (modelFunctorIso l E Y) (ordinaryIntegralModulePull l E f) ≪≫
      FiniteProjectivePullback.allComparison l E f ≪≫ (modelFunctorIso l E X).symm
  have hn : ∀ (N : ModuleCat.{u + 1} (PbcIntegralRing l E)) (W : Y.ProEt) (x : N),
      ((γ.hom.app N).val.app (op ((proEtaleBaseChange f).obj W)))
        ((((ordinaryIntegralModuleAdjunction l E f).unit.app
            ((modelModule l E Y).obj N)).val.app (op W))
          (modelSection l E Y N (op W) 1 x)) =
        modelSection l E X N (op ((proEtaleBaseChange f).obj W)) 1 x := by
    intro N W x
    have h := congrArg (fun a ↦ a.val.app (op W) (modelSection l E Y N (op W) 1 x))
      ((ordinaryIntegralModuleAdjunction l E f).unit.naturality
        ((modelFunctorIso l E Y).hom.app N))
    simp only [Functor.id_map, Functor.comp_map, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ConcreteCategory.comp_apply] at h
    erw [modelFunctorIso_section l E Y N (op W) 1 x] at h
    change ((modelFunctorIso l E X).inv.app N).val.app _
      (((FiniteProjectivePullback.allComparison l E f).hom.app N).val.app _
        (((ordinaryIntegralModulePull l E f).map
          ((modelFunctorIso l E Y).hom.app N)).val.app _
            ((((ordinaryIntegralModuleAdjunction l E f).unit.app
              ((modelModule l E Y).obj N)).val.app (op W))
                (modelSection l E Y N (op W) 1 x)))) = _
    erw [← h]
    exact (congrArg (fun z ↦ ((modelFunctorIso l E X).inv.app N).val.app
      (op ((proEtaleBaseChange f).obj W)) z)
      (FiniteProjectivePullback.allComparison_normalized l E f N W x)).trans
        (modelFunctorIso_inv_section l E X N (op ((proEtaleBaseChange f).obj W)) 1 x)
  refine ⟨γ, hn, ?_⟩
  intro δ hδ
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply ((ordinaryIntegralModuleAdjunction l E f).homEquiv _ _).injective
  apply modelGenerator_ext l E Y N
  intro x
  simp only [Adjunction.homEquiv_unit, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply]
  exact (hδ N (⊤_ Y.ProEt) x).trans (hn N (⊤_ Y.ProEt) x).symm

/-- The uniquely generator-normalized ordinary model isomorphism.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def modelPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (modelPullback_existsUnique l E f).exists.choose

/-- Its degreewise application, retaining the same scalar differential and idempotents.
Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def modelPullbackComplex {X Y : Scheme.{u}} (f : X ⟶ Y) :
    modelComplex l E Y ⋙ ordinaryIntegralPullComplex l E f ≅ modelComplex l E X :=
  NatIso.mapHomologicalComplex (modelPullback l E f) (.up ℤ)

/-- The last local isomorphism is the ordinary computation counit followed by
localization of the normalized termwise model isomorphism, before completion.
Source: Stacks 06YQ, 06YY; Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: each finite projective term is a retract of finite free modules. Its
realization is consequently a retract of a finite free B-module and is flat.
Boundedness makes the realized complex K-flat by bounded-above-flat-kflat-site.
Ringed-topoi-derived-pullback makes its specified computation counit invertible.
The termwise comparison is invertible by modelPullback_existsUnique; localization
preserves that isomorphism. The composite has exactly the required normalization. -/
theorem perfectModelPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ)
    (_hfinite : ∀ q : ℤ, Module.Finite (PbcIntegralRing l E) (L.X q))
    (_hprojective : ∀ q : ℤ, Module.Projective (PbcIntegralRing l E) (L.X q))
    (_hbounded : ∃ a b : ℤ, ∀ q : ℤ, q < a ∨ b < q → IsZero (L.X q)) :
    IsIso (ordinaryIntegralPullComplexCounit l E f ((modelComplex l E Y).obj L)) ∧
      IsIso (ordinaryIntegralPullComplexCounit l E f ((modelComplex l E Y).obj L) ≫
        DerivedCategory.Q.map ((modelPullbackComplex l E f).hom.app L)) := by
  have hflat (q : ℤ) : SheafOfModules.IsFlatOnSite
      (J := ProEt.topology Y) (R := completedIntegralCommRingSheafUnrestricted l E Y)
      (((modelComplex l E Y).obj L).X q) := by
    have := _hfinite q
    have := _hprojective q
    let R := completedIntegralCommRingSheafUnrestricted l E Y
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    have hf := tensorModel_flat l E Y (L.X q)
    have hc := SheafOfModules.flat_to_cat R _ hf
    have hm := (ObjectProperty.flat (A := integralTowerModules l E Y)).prop_of_iso
      (modelObjectIso l E Y (L.X q)).symm hc
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm hm.2
  obtain ⟨_a, b, hb⟩ := _hbounded
  have : CochainComplex.IsStrictlyLE ((modelComplex l E Y).obj L) b :=
    (CochainComplex.isStrictlyLE_iff _ b).2
      (fun q hq ↦ (modelModule l E Y).map_isZero (hb q (Or.inr hq)))
  have hk := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    (completedIntegralCommRingSheafUnrestricted l E Y) ((modelComplex l E Y).obj L) b
    hflat
  have hi := ordinaryIntegralPullComplexCounit_isIso l E f
    ⟨(modelComplex l E Y).obj L, hk, hflat⟩
  refine ⟨hi, ?_⟩
  infer_instance

/-- The actual fibre-product associativity comparison on the two covering slices.
Source: Stacks 03CB, 04IF (blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def squareSite {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :
    proEtaleBaseChange i ⋙ proEtaleBaseChange (pullback.snd f i) ≅
      proEtaleBaseChange f ⋙ proEtaleBaseChange (pullback.fst f i) :=
  (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    (pullback.snd f i) i (fg := pullback.fst f i ≫ f)
    (hfg := pullback.condition)).symm ≪≫
  MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) (pullback.fst f i) f

/-- The canonical inverse-image generator 1 tensor x, given by the module adjunction unit.
Source: Stacks 03D2 (blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def pullGenerator {X Y : Scheme.{u}} (f : X ⟶ Y) (M : integralTowerModules l E Y)
    (W : Y.ProEt) (x : M.val.obj (op W)) :
    ((ordinaryIntegralModulePull l E f).obj M).val.obj
      (op ((proEtaleBaseChange f).obj W)) :=
  (((ordinaryIntegralModuleAdjunction l E f).unit.app M).val.app (op W)) x

private def modelPushComp {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    {hk : X ⟶ Z} (hhk : hk = h ≫ k) :
    ordinaryIntegralModulePush l E h ⋙ ordinaryIntegralModulePush l E k ≅
      ordinaryIntegralModulePush l E hk := by
  subst hk
  letI := ProEt.isContinuous_overPullback h
  letI := ProEt.isContinuous_overPullback k
  letI := ProEt.isContinuous_overPullback (h ≫ k)
  letI := Functor.isContinuous_comp (proEtaleBaseChange k) (proEtaleBaseChange h)
    (ProEt.topology Z) (ProEt.topology Y) (ProEt.topology X)
  refine SheafOfModules.pushforwardComp
    (ordinaryIntegralDirectRingMap l E k) (ordinaryIntegralDirectRingMap l E h) ≪≫ ?_
  apply SheafOfModules.pushforwardCongr₂
    (e := MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) h k)
  exact direct_comp l E h k

private theorem modelPushComp_sections {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    {hk : X ⟶ Z} (hhk : hk = h ≫ k)
    (N : integralTowerModules l E X) (W : Z.ProEt)
    (x : ((ordinaryIntegralModulePush l E h ⋙
      ordinaryIntegralModulePush l E k).obj N).val.obj (op W)) :
    ((modelPushComp l E h k hhk).hom.app N).val.app (op W) x =
      N.val.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h k (fg := hk) (hfg := hhk)).hom.app W).op x := by
  subst hk
  unfold modelPushComp
  simp only [Iso.trans_hom, NatTrans.comp_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    SheafOfModules.pushforwardCongr₂, SheafOfModules.pushforwardNatIso_hom,
    SheafOfModules.pushforwardNatTrans_app_val_app_apply]
  rfl

private theorem modelPushComp_inv_sections {X Y Z : Scheme.{u}} (h : X ⟶ Y) (k : Y ⟶ Z)
    {hk : X ⟶ Z} (hhk : hk = h ≫ k)
    (N : integralTowerModules l E X) (W : Z.ProEt)
    (x : ((ordinaryIntegralModulePush l E hk).obj N).val.obj (op W)) :
    ((modelPushComp l E h k hhk).inv.app N).val.app (op W) x =
      N.val.map ((MorphismProperty.Over.pullbackComp
        (P := @WeaklyEtale) (Q := ⊤) h k (fg := hk) (hfg := hhk)).inv.app W).op x := by
  subst hk
  unfold modelPushComp
  simp only [Iso.trans_inv, NatTrans.comp_app, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
    SheafOfModules.pushforwardCongr₂, SheafOfModules.pushforwardNatIso_inv,
    SheafOfModules.pushforwardCongr_hom_app_val_app,
    SheafOfModules.pushforwardNatTrans_app_val_app_apply]
  rfl

private def modelDirectSquare {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :
    ordinaryIntegralModulePush l E (pullback.fst f i) ⋙ ordinaryIntegralModulePush l E f ≅
      ordinaryIntegralModulePush l E (pullback.snd f i) ⋙ ordinaryIntegralModulePush l E i :=
  modelPushComp l E (pullback.fst f i) f rfl ≪≫
    (modelPushComp l E (pullback.snd f i) i pullback.condition).symm

private theorem modelDirectSquare_sections {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y)
    (N : integralTowerModules l E (pullback f i)) (W : Y.ProEt)
    (x : ((ordinaryIntegralModulePush l E (pullback.fst f i) ⋙
      ordinaryIntegralModulePush l E f).obj N).val.obj (op W)) :
    ((modelDirectSquare l E f i).hom.app N).val.app (op W) x =
      N.val.map ((squareSite f i).hom.app W).op x := by
  change ((modelPushComp l E (pullback.snd f i) i pullback.condition).inv.app N).val.app
    (op W) (((modelPushComp l E (pullback.fst f i) f rfl).hom.app N).val.app (op W) x) = _
  rw [modelPushComp_inv_sections, modelPushComp_sections]
  change (N.val.presheaf.map _ ≫ N.val.presheaf.map _) x = _
  rw [← Functor.map_comp]
  rfl


/-- The ordinary square comparison is uniquely fixed on iterated inverse-image generators.
Source: Stacks 03CB, 03D2 and 0D6D
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: coefficientMap_comp identifies the structural maps of the two equal composites,
including all finite projections. Compose the ordinary tensor pullback comparisons.
On iterated generators both composites insert one twice, and squareSite gives the
canonical restriction between the iterated fibre products. Tensor relations and
sheafification give the isomorphism. These generators locally span the pullback
module, so their displayed values determine its components and the natural isomorphism. -/
theorem moduleSquare_existsUnique {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :
    ∃! γ : ordinaryIntegralModulePull l E i ⋙
          ordinaryIntegralModulePull l E (pullback.snd f i) ≅
        ordinaryIntegralModulePull l E f ⋙
          ordinaryIntegralModulePull l E (pullback.fst f i),
      ∀ (M : integralTowerModules l E Y) (W : Y.ProEt) (x : M.val.obj (op W)),
        ((γ.hom.app M).val.app
            (op ((proEtaleBaseChange (pullback.snd f i)).obj ((proEtaleBaseChange i).obj W))))
          (pullGenerator l E (pullback.snd f i) ((ordinaryIntegralModulePull l E i).obj M)
            ((proEtaleBaseChange i).obj W) (pullGenerator l E i M W x)) =
          (((ordinaryIntegralModulePull l E (pullback.fst f i)).obj
              ((ordinaryIntegralModulePull l E f).obj M)).val.map
            ((squareSite f i).hom.app W).op)
              (pullGenerator l E (pullback.fst f i) ((ordinaryIntegralModulePull l E f).obj M)
                ((proEtaleBaseChange f).obj W) (pullGenerator l E f M W x)) := by
  let a := (ordinaryIntegralModuleAdjunction l E f).comp
    (ordinaryIntegralModuleAdjunction l E (pullback.fst f i))
  let b := (ordinaryIntegralModuleAdjunction l E i).comp
    (ordinaryIntegralModuleAdjunction l E (pullback.snd f i))
  let d := modelDirectSquare l E f i
  let γ := (conjugateIsoEquiv a b).symm d
  have hmate (M : integralTowerModules l E Y) :
      b.unit.app M ≫ (ordinaryIntegralModulePush l E (pullback.snd f i) ⋙
        ordinaryIntegralModulePush l E i).map (γ.hom.app M) =
      a.unit.app M ≫ d.hom.app
        ((ordinaryIntegralModulePull l E f ⋙
          ordinaryIntegralModulePull l E (pullback.fst f i)).obj M) :=
    (unit_conjugateEquiv_symm a b d.hom M).symm
  have normalize : ∀ (M : integralTowerModules l E Y) (W : Y.ProEt) (x : M.val.obj (op W)),
        ((γ.hom.app M).val.app
            (op ((proEtaleBaseChange (pullback.snd f i)).obj ((proEtaleBaseChange i).obj W))))
          (pullGenerator l E (pullback.snd f i) ((ordinaryIntegralModulePull l E i).obj M)
            ((proEtaleBaseChange i).obj W) (pullGenerator l E i M W x)) =
          (((ordinaryIntegralModulePull l E (pullback.fst f i)).obj
              ((ordinaryIntegralModulePull l E f).obj M)).val.map
            ((squareSite f i).hom.app W).op)
              (pullGenerator l E (pullback.fst f i) ((ordinaryIntegralModulePull l E f).obj M)
                ((proEtaleBaseChange f).obj W) (pullGenerator l E f M W x)) := by
    intro M W x
    have h := congrArg (fun q ↦ q.val.app (op W) x) (hmate M)
    simp only [a, b, Adjunction.comp_unit_app, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ConcreteCategory.comp_apply] at h
    exact h.trans (modelDirectSquare_sections l E f i _ W _)
  refine ⟨γ, normalize, ?_⟩
  intro δ hδ
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (b.homEquiv M _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  ext x
  exact (hδ M W.unop x).trans (normalize M W.unop x).symm

/-- The generator-normalized square comparison of ordinary module functors.
Source: Stacks 03D2, 0D6D (blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def moduleSquare {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :=
  (moduleSquare_existsUnique l E f i).exists.choose

/-- Its termwise action on cochain complexes.
Source: Stacks 0D6D (blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def complexSquare {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :
    ordinaryIntegralPullComplex l E i ⋙ ordinaryIntegralPullComplex l E (pullback.snd f i) ≅
      ordinaryIntegralPullComplex l E f ⋙ ordinaryIntegralPullComplex l E (pullback.fst f i) :=
  NatIso.mapHomologicalComplex (moduleSquare l E f i) (.up ℤ)

section ExactModels

attribute [local instance] modelCommSheafify modelAbSheafify modelAbWeakSheafify
  modelAbLocallyBijective modelCompose

attribute [local semireducible] OrdinaryImmersionChart.Rings

private theorem chartRingMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    OrdinaryImmersionChart.directRingMap l E f = ordinaryIntegralDirectRingMap l E f := by
  apply (ordinaryIntegralDirectRingMap_existsUnique l E f).unique
  · intro n
    have h := congrArg ((completedRingAdj.{u, u} f).homEquiv _ _)
      (completedMap_projection l E f n)
    rw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_naturality_left] at h
    simp only [completedRingConstantMap, integralCoefficientCommRingSheaf,
      Equiv.apply_symm_apply] at h
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    exact congrArg (fun q ↦ (forget₂ CommRingCat RingCat).map (q.hom.app W)) h
  · exact (ordinaryIntegralDirectRingMap_existsUnique l E f).exists.choose_spec

private def chartPullIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    OrdinaryImmersionChart.pull l E f ≅ ordinaryIntegralModulePull l E f :=
  (conjugateIsoEquiv (ordinaryIntegralModuleAdjunction l E f)
    (OrdinaryImmersionChart.adj l E f)).symm
      (SheafOfModules.pushforwardCongr (chartRingMap l E f).symm)

private theorem ordinaryPull_limits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (ordinaryIntegralModulePull l E f) := by
  have := OrdinaryImmersionChart.ordinaryCompletedPullbackExact l E f
  exact preservesFiniteLimits_of_natIso (chartPullIso l E f)

private theorem ordinaryPull_colimits {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (ordinaryIntegralModulePull l E f) := by
  have := (ordinaryIntegralModuleAdjunction l E f).leftAdjoint_preservesColimits
  infer_instance

private theorem ordinaryCounitExact {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    IsIso (ordinaryIntegralPullComplexCounit l E f P) := by
  let := HasDerivedCategory.standard (integralTowerModules l E X)
  let := HasDerivedCategory.standard (integralTowerModules l E Y)
  have := ordinaryPull_limits l E f
  have := ordinaryPull_colimits l E f
  let F := ordinaryIntegralModulePull l E f
  let W := HomotopyCategory.quasiIso (integralTowerModules l E Y) (.up ℤ)
  have hF : W.IsInvertedBy (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso W F.mapDerivedCategoryFactorsh]
    exact MorphismProperty.IsInvertedBy.of_comp W DerivedCategory.Qh
      (Localization.inverts DerivedCategory.Qh W) F.mapDerivedCategory
  have : (ordinaryIntegralDerivedPull l E f).IsLeftDerivedFunctor
      (ordinaryIntegralPullCounit l E f) W := by
    dsimp only [ordinaryIntegralDerivedPull, ordinaryIntegralPullCounit, W]
    infer_instance
  have := Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (ordinaryIntegralDerivedPull l E f) (ordinaryIntegralPullCounit l E f) hF
  unfold ordinaryIntegralPullComplexCounit
  infer_instance

end ExactModels

private def exactComplexCounit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Q ⋙ ordinaryIntegralDerivedPull l E f ⟶
      ordinaryIntegralPullComplex l E f ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).inv
      (ordinaryIntegralDerivedPull l E f) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient _ _)
      (ordinaryIntegralPullCounit l E f) ≫
    Functor.whiskerRight
      ((ordinaryIntegralModulePull l E f).mapHomotopyCategoryFactors (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (ordinaryIntegralPullComplex l E f)
      (DerivedCategory.quotientCompQhIso _).hom

private theorem exactComplexCounit_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (exactComplexCounit l E f).app P = ordinaryIntegralPullComplexCounit l E f P := rfl

private instance exactComplexCounit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (exactComplexCounit l E f) := by
  have (P : CochainComplex (integralTowerModules l E Y) ℤ) :
      IsIso ((exactComplexCounit l E f).app P) := by
    rw [exactComplexCounit_app]
    exact ordinaryCounitExact l E f P
  exact NatIso.isIso_of_isIso_app _

/-- The ordinary derived square comparison retains its computation-counit equation.
Source: Stacks 0D6D and 06YY
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: choose a flat-term K-flat resolution. Ordinary ringed pullback preserves this
class. Apply the two ordinary derived composition comparisons and the two-isomorphism
transport for the equal composites, using moduleSquare for their termwise comparison.
The normalized comparison on representatives gives the displayed counit equation.
Descent gives it for arbitrary complexes. On good resolutions all computation maps
are invertible; every derived object has such a resolution. This proves uniqueness. -/
theorem derivedSquare_existsUnique {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :
    ∃! β : ordinaryIntegralDerivedPull l E f ⋙
          ordinaryIntegralDerivedPull l E (pullback.fst f i) ≅
        ordinaryIntegralDerivedPull l E i ⋙
          ordinaryIntegralDerivedPull l E (pullback.snd f i),
      ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
        β.hom.app (DerivedCategory.Q.obj P) ≫
            (ordinaryIntegralDerivedPull l E (pullback.snd f i)).map
              (ordinaryIntegralPullComplexCounit l E i P) ≫
            ordinaryIntegralPullComplexCounit l E (pullback.snd f i)
              ((ordinaryIntegralPullComplex l E i).obj P) ≫
            DerivedCategory.Q.map ((complexSquare l E f i).hom.app P) =
          (ordinaryIntegralDerivedPull l E (pullback.fst f i)).map
              (ordinaryIntegralPullComplexCounit l E f P) ≫
            ordinaryIntegralPullComplexCounit l E (pullback.fst f i)
              ((ordinaryIntegralPullComplex l E f).obj P) := by
  let Q := DerivedCategory.Q (C := integralTowerModules l E Y)
  let W := HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)
  let F := ordinaryIntegralDerivedPull l E f ⋙
    ordinaryIntegralDerivedPull l E (pullback.fst f i)
  let G := ordinaryIntegralDerivedPull l E i ⋙
    ordinaryIntegralDerivedPull l E (pullback.snd f i)
  let a : Q ⋙ F ≅
      (ordinaryIntegralPullComplex l E f ⋙
        ordinaryIntegralPullComplex l E (pullback.fst f i)) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (asIso (exactComplexCounit l E f))
        (ordinaryIntegralDerivedPull l E (pullback.fst f i)) ≪≫
      Functor.isoWhiskerLeft (ordinaryIntegralPullComplex l E f)
        (asIso (exactComplexCounit l E (pullback.fst f i)))
  let b : Q ⋙ G ≅
      (ordinaryIntegralPullComplex l E f ⋙
        ordinaryIntegralPullComplex l E (pullback.fst f i)) ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerRight (asIso (exactComplexCounit l E i))
        (ordinaryIntegralDerivedPull l E (pullback.snd f i)) ≪≫
      Functor.isoWhiskerLeft (ordinaryIntegralPullComplex l E i)
        (asIso (exactComplexCounit l E (pullback.snd f i))) ≪≫
      Functor.isoWhiskerRight (complexSquare l E f i) DerivedCategory.Q
  let β : F ≅ G := Localization.liftNatIso Q W (Q ⋙ F) (Q ⋙ G) F G (a ≪≫ b.symm)
  have hβ (P : CochainComplex (integralTowerModules l E Y) ℤ) :
      β.hom.app (Q.obj P) ≫ b.hom.app P = a.hom.app P := by
    dsimp only [β]
    simp only [Localization.liftNatIso_hom, Localization.liftNatTrans_app,
      Localization.Lifting.compLeft, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
      Category.id_comp, Category.comp_id, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  refine ⟨β, ?_, ?_⟩
  · intro P
    simpa only [a, b, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      asIso_hom, exactComplexCounit_app, Category.assoc] using hβ P
  · intro γ hγ
    apply Iso.ext
    apply Localization.natTrans_ext Q W
    intro P
    apply (cancel_mono (b.hom.app P)).1
    rw [hβ]
    simpa only [a, b, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      asIso_hom, exactComplexCounit_app, Category.assoc] using hγ P

/-- The unique ordinary derived square comparison with this representative normalization.
Source: Stacks 0D6D (blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def derivedSquare {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y) :=
  (derivedSquare_existsUnique l E f i).exists.choose

/-- For immersions ordinary pullback is exact restriction, with its ordinary counit.
Source: Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: immersion-completed-pullback-comparison identifies the projection-defined
coefficient map with the canonical immersion coefficient isomorphism. Its ordinary
module functor is exact inverse image. Thus every complex computes the left derived
functor; the ordinary computation counit is invertible without completeness. -/
theorem immersionExact {X Y : Scheme.{u}} (i : X ⟶ Y) [IsImmersion i] :
    PreservesFiniteLimits (ordinaryIntegralModulePull l E i) ∧
      PreservesFiniteColimits (ordinaryIntegralModulePull l E i) ∧
      ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
        IsIso (ordinaryIntegralPullComplexCounit l E i P) := by
  exact ⟨ordinaryPull_limits l E i, ordinaryPull_colimits l E i,
    ordinaryCounitExact l E i⟩

/-- Restriction to a pro-etale covering object is exact ordinary pullback.
This identifies the site-of-U notation used below with the corresponding slice
restriction, retaining the same ordinary computation counit.
Source: Stacks 04IF and proetale localization; Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-tw-ordinary-pullback-stratified-models).
Proof: weakly-etale-localization identifies the small site of U with the slice.
Constant rings restrict by the identity on constant sections. Limits on the slice
are sectionwise, so the completed ring and every finite projection restrict to
those on U. The projection-defined ring map is therefore this identification.
Module restriction is exact, and exact termwise restriction computes its derived
functor on every complex; its ordinary computation counit is invertible. -/
theorem weaklyEtaleExact {X Y : Scheme.{u}} (i : X ⟶ Y) [WeaklyEtale i] :
    PreservesFiniteLimits (ordinaryIntegralModulePull l E i) ∧
      PreservesFiniteColimits (ordinaryIntegralModulePull l E i) ∧
      ∀ P : CochainComplex (integralTowerModules l E Y) ℤ,
        IsIso (ordinaryIntegralPullComplexCounit l E i P) := by
  exact ⟨ordinaryPull_limits l E i, ordinaryPull_colimits l E i,
    ordinaryCounitExact l E i⟩

/-- The canonical local composition and covering-slice restriction comparison.
The covering object U is a weakly etale scheme over the stratum S; its pullback
is literally the chart V = (X times_Y S) times_S U.
Source: Stacks 0D6D, 04IF; Bhatt--Scholze, Remark 6.8.15
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def localExchange {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y)
    (U : S.ProEt) (K : DerivedCategory (integralTowerModules l E Y)) :
    (ordinaryIntegralDerivedPull l E
        (pullback.fst (pullback.snd f i) U.hom)).obj
      ((ordinaryIntegralDerivedPull l E (pullback.fst f i)).obj
        ((ordinaryIntegralDerivedPull l E f).obj K)) ≅
    (ordinaryIntegralDerivedPull l E
        (pullback.snd (pullback.snd f i) U.hom)).obj
      ((ordinaryIntegralDerivedPull l E U.hom).obj
        ((ordinaryIntegralDerivedPull l E i).obj K)) :=
  (ordinaryIntegralDerivedPull l E (pullback.fst (pullback.snd f i) U.hom)).mapIso
      ((derivedSquare l E f i).app K) ≪≫
    (derivedSquare l E (pullback.snd f i) U.hom).app
      ((ordinaryIntegralDerivedPull l E i).obj K)

/-- The specified local-model map: composition and slice comparisons, the given
chart isomorphism, the ordinary K-flat counit, and the termwise tensor comparison.
Source: Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15
(blueprint: lem-tw-ordinary-pullback-stratified-models). -/
def localComparison {X Y S : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ Y)
    (U : S.ProEt) (K : DerivedCategory (integralTowerModules l E Y))
    (L : CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ)
    (e : (ordinaryIntegralDerivedPull l E U.hom).obj
          ((ordinaryIntegralDerivedPull l E i).obj K) ≅
        DerivedCategory.Q.obj ((modelComplex l E U.left).obj L)) :
    (ordinaryIntegralDerivedPull l E
        (pullback.fst (pullback.snd f i) U.hom)).obj
      ((ordinaryIntegralDerivedPull l E (pullback.fst f i)).obj
        ((ordinaryIntegralDerivedPull l E f).obj K)) ⟶
      DerivedCategory.Q.obj
        ((modelComplex l E (pullback (pullback.snd f i) U.hom)).obj L) :=
  (localExchange l E f i U K).hom ≫
    (ordinaryIntegralDerivedPull l E (pullback.snd (pullback.snd f i) U.hom)).map e.hom ≫
    ordinaryIntegralPullComplexCounit l E (pullback.snd (pullback.snd f i) U.hom)
      ((modelComplex l E U.left).obj L) ≫
    DerivedCategory.Q.map
      ((modelPullbackComplex l E (pullback.snd (pullback.snd f i) U.hom)).hom.app L)

set_option linter.unusedVariables false in
/-- Ordinary pullback transports the given stratification, covers and perfect local
models. The index bijection deletes exactly the empty base-changed strata. The
map asserted invertible is localComparison, with its prescribed basis/idempotent
and ordinary computation-counit normalization, rather than a comparison after completion.

Source: Bhatt--Scholze, Proposition 6.6.11 and Remark 6.8.15
(blueprint: lem-tw-ordinary-pullback-stratified-models).

Proof (the eight steps of the DAG):
1. Base change the finite locally closed stratification. Constructible-preimage
makes its images constructible; the ranges are disjoint and cover X. Delete
empty images and enumerate the remaining finite index set. Weakly etale and
fpqc base change preserve the given covering families.
2. Constant-coefficient-composition at every finite R/t^(n+1), followed by the
limit universal property, gives coefficientMap_comp for both equal composites.
3. Weakly-etale-localization identifies the pro-etale slice at U with the site
of its underlying scheme, and similarly for V. Constant rings and their limit
projections agree there. Localize-ringed-site-morphism identifies the restricted
structural map with the projection-defined map for v.
4. Ringed-derived-monoidal-comparisons gives the two ordinary composition
isomorphisms and their two-isomorphism transport. Immersion-completed-pullback-
comparison is used only for unconditional exact immersion restriction. This
is derivedSquare, with the displayed ordinary counit equation.
5. The ordinary unbounded sheaf-slice comparison, pro-etale subcanonicity and
site-representable-algebraic-pullback identify the pulled representable h_U with
h_V. Localizing the comparison gives localExchange; apply P_v to the given e.
6. Split each finite projective scalar term off finite free R-modules. Tensoring
its realization with an exact sequence is a split summand of a finite direct
sum of that sequence, hence exact: the terms are flat B-modules.
7. The realized bounded flat complex is K-flat by bounded-above-flat-kflat-site.
Ringed-topoi-derived-pullback makes the ordinary computation counit invertible.
8. On free bases the termwise balanced-tensor map sends b tensor (a e_j) to
b c_v(a) e_j; its inverse inserts one. Constant scalar preservation makes this
commute with the same idempotent and every differential, yielding modelPullback.
Its localization, composed with the counit and localExchange, is precisely the
map in the conclusion. No flatness of c_f or completeness of P_f K is used. -/
theorem ordinaryPullbackStratifiedModels
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y)
    (K : DerivedCategory (integralTowerModules l E Y))
    (s : FiniteLocallyClosedStratification Y)
    (_hs : ∀ i : Fin s.n, Topology.IsConstructible (s.stratum i))
    (A : Fin s.n → Type v) (U : ∀ i : Fin s.n, A i → (s.domain i).ProEt)
    (_hcover : ∀ i : Fin s.n,
      Sieve.generate (Presieve.ofArrows (U i) (fun a ↦ terminal.from (U i a))) ∈
        ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt))
    (L : ∀ (i : Fin s.n) (a : A i),
      CochainComplex (ModuleCat.{u + 1} (PbcIntegralRing l E)) ℤ)
    (_hfinite : ∀ (i : Fin s.n) (a : A i) (q : ℤ),
      Module.Finite (PbcIntegralRing l E) ((L i a).X q))
    (_hprojective : ∀ (i : Fin s.n) (a : A i) (q : ℤ),
      Module.Projective (PbcIntegralRing l E) ((L i a).X q))
    (_hbounded : ∀ (i : Fin s.n) (a : A i),
      ∃ b c : ℤ, ∀ q : ℤ, q < b ∨ c < q → IsZero ((L i a).X q))
    (e : ∀ (i : Fin s.n) (a : A i),
      (ordinaryIntegralDerivedPull l E (U i a).hom).obj
          ((ordinaryIntegralDerivedPull l E (s.immersion i)).obj K) ≅
        DerivedCategory.Q.obj ((modelComplex l E (U i a).left).obj (L i a))) :
    (∃ sX : FiniteLocallyClosedStratification X,
      ∃ b : Fin sX.n ≃ {i : Fin s.n // Nonempty (pullback f (s.immersion i) : Scheme.{u})},
        (∀ k : Fin sX.n, Topology.IsConstructible (sX.stratum k)) ∧
        (∀ k : Fin sX.n, sX.stratum k = f.base ⁻¹' s.stratum (b k).val) ∧
        ∀ k : Fin sX.n,
          ∃ α : sX.domain k ≅ pullback f (s.immersion (b k).val),
            α.hom ≫ pullback.fst f (s.immersion (b k).val) = sX.immersion k) ∧
      ∀ i : Fin s.n, Nonempty (pullback f (s.immersion i) : Scheme.{u}) →
        (Sieve.generate (Presieve.ofArrows
          (fun a : A i ↦ (proEtaleBaseChange (pullback.snd f (s.immersion i))).obj (U i a))
          (fun a : A i ↦ terminal.from
            ((proEtaleBaseChange (pullback.snd f (s.immersion i))).obj (U i a)))) ∈
          ProEt.topology (pullback f (s.immersion i)) (⊤_ (pullback f (s.immersion i)).ProEt)) ∧
        ∀ a : A i, IsIso (localComparison l E f (s.immersion i) (U i a) K (L i a) (e i a)) := by
  classical
  let I := {i : Fin s.n // Nonempty (pullback f (s.immersion i) : Scheme.{u})}
  let b : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let sX : FiniteLocallyClosedStratification X :=
    { n := Fintype.card I
      stratum := fun k ↦ f.base ⁻¹' s.stratum (b k).val
      isLocallyClosed_stratum := fun k ↦
        (s.isLocallyClosed_stratum (b k).val).preimage f.continuous
      iUnion_stratum_eq_univ := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
        have hx : f x ∈ ⋃ i, s.stratum i := by rw [s.iUnion_stratum_eq_univ]; trivial
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        have hx' : x ∈ Set.range (pullback.fst f (s.immersion i)) := by
          rw [Pullback.range_fst, s.range_immersion]
          exact hi
        obtain ⟨z, _⟩ := hx'
        let j : I := ⟨i, ⟨z⟩⟩
        refine ⟨b.symm j, ?_⟩
        change f x ∈ s.stratum (b (b.symm j)).val
        simpa only [Equiv.apply_symm_apply] using hi
      pairwise_disjoint_stratum := by
        intro k k' hkk'
        exact (s.pairwise_disjoint_stratum
          (fun h ↦ hkk' (b.injective (Subtype.ext h)))).preimage _
      domain := fun k ↦ pullback f (s.immersion (b k).val)
      immersion := fun k ↦ pullback.fst f (s.immersion (b k).val)
      isImmersion := fun k ↦ by
        have := s.isImmersion (b k).val
        infer_instance
      range_immersion := fun k ↦ by rw [Pullback.range_fst, s.range_immersion] }
  refine ⟨⟨sX, b, fun k ↦ f.isConstructible_preimage (_hs (b k).val),
    fun _ ↦ rfl, fun _ ↦ ⟨Iso.refl _, Category.id_comp _⟩⟩, ?_⟩
  intro i _
  constructor
  · let F := proEtaleBaseChange (pullback.snd f (s.immersion i))
    let J := ProEt.topology (pullback f (s.immersion i))
    apply (GrothendieckTopology.pullback_mem_iff_of_isIso
      (i := terminalComparison F)).mp
    have hc := (proEtaleBaseChangeCoverPreserving
      (pullback.snd f (s.immersion i))).cover_preserve (_hcover i)
    apply J.superset_covering ?_ hc
    rw [Sieve.functorPushforward_ofArrows]
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨a⟩
    change Sieve.ofArrows _ _ (F.map (terminal.from (U i a)) ≫ terminalComparison F)
    have ht : F.map (terminal.from (U i a)) ≫ terminalComparison F =
        terminal.from (F.obj (U i a)) := terminalIsTerminal.hom_ext _ _
    rw [ht]
    exact Sieve.ofArrows_mk _ _ a
  · intro a
    have h := perfectModelPullback l E
      (pullback.snd (pullback.snd f (s.immersion i)) (U i a).hom)
      (L i a) (_hfinite i a) (_hprojective i a) (_hbounded i a)
    have htail := h.2
    have hhead : IsIso ((localExchange l E f (s.immersion i) (U i a) K).hom) := by
      infer_instance
    have hmid : IsIso ((ordinaryIntegralDerivedPull l E
        (pullback.snd (pullback.snd f (s.immersion i)) (U i a).hom)).map (e i a).hom) := by
      infer_instance
    dsimp only [localComparison]
    exact IsIso.comp_isIso' hhead (IsIso.comp_isIso' hmid htail)

end WeilConjectures.OrdinaryStratifiedModels
