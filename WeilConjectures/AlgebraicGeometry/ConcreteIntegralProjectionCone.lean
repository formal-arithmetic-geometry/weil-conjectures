/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.SixFunctorOperationDatum
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.SfProEtaleProjectionFormula
public import WeilConjectures.AlgebraicGeometry.FiniteProjectionOperationPresentation
import all WeilConjectures.AlgebraicGeometry.SfProEtaleProjectionFormula
import all WeilConjectures.AlgebraicGeometry.IntegralCompactSupportCoefficientData
import all WeilConjectures.AlgebraicGeometry.SfIntegralReductionTowerSupplement
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.AlgebraicGeometry.CompactSupportProjectionCoefficientChange
import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportFiniteComparison
import WeilConjectures.Algebra.Homology.DerivedScalarExtensionCounitShift
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.AlgebraicGeometry.IntegralResidueTor
import WeilConjectures.AlgebraicGeometry.IntegralOperationsPreserveConstructible
import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.IntegralReductionTowerWellDefinedUnrestricted

/-! # Complete endpoints and reduced cones of the specified integral projection

Source: main-20261015, fix-prop-projection-formula.proof.md, concrete integral
endpoint, actual-map reduction and cone obligations
(blueprint: lem-sf-concrete-integral-projection-cone).

## Main declarations

* `concreteIntegralProjectionCone`: complete constructible endpoints and the reduction
  and cone assertions, including the actual derived quotient transitions.
* `sourceComparison`, `targetComparison`: the specified operation comparisons.
* `derivedConeComparison`, `restrictedDerivedConeComparison`: the canonical derived
  counit and signed-cone comparisons used in the transition equation.

The projection is the existing completed-unit extension of the proper-counit/open
composite. Its finite endpoint comparisons below are composites of the normalized
scalar tensor, compact-support, and pullback comparisons, rather than arbitrary maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
  WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConcreteIntegralProjection
open PurCompactSupport
open CochainComplex

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  finiteReductionIso scalarTensor scalarPull SheafOfModules.monoidalCategory

private instance product_isIso {A B : Type*} [Category A] [Category B]
    {M M' : A} {N N' : B} (a : M ⟶ M') (b : N ⟶ N') [IsIso a] [IsIso b] :
    IsIso (Prod.mkHom a b) :=
  (isIso_prod_iff A B).2 ⟨inferInstance, inferInstance⟩

private theorem projection_naturality (R : Coefficients.{u})
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (a : ProEtaleTensorModel X (R.ring X))
    (b : ProEtaleTensorModel c.Z (R.ring c.Z))
    (t : ProEtaleTensorModel Y (R.ring Y))
    (hc : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))
    {K K' : DerivedCategory (pbcModules X (R.ring X))}
    {L L' : DerivedCategory (pbcModules Y (R.ring Y))} (α : K ⟶ K') (β : L ⟶ L') :
    (((projectionMap R c a b t hc).app K).app L) ≫
        (image R c).map (a.tensor.map (Prod.mkHom α ((pull R f).map β))) =
      t.tensor.map (Prod.mkHom ((image R c).map α) β) ≫
        (((projectionMap R c a b t hc).app K').app L') := by
  have hK := NatTrans.congr_app ((projectionMap R c a b t hc).naturality α) L
  have hL := ((projectionMap R c a b t hc).app K').naturality β
  change t.tensor.map (Prod.mkHom ((image R c).map α) (𝟙 L)) ≫
      (((projectionMap R c a b t hc).app K').app L) =
    (((projectionMap R c a b t hc).app K).app L) ≫
      (image R c).map (a.tensor.map (Prod.mkHom α (𝟙 _))) at hK
  change t.tensor.map (Prod.mkHom (𝟙 _) β) ≫
      (((projectionMap R c a b t hc).app K').app L') =
    (((projectionMap R c a b t hc).app K').app L) ≫
      (image R c).map (a.tensor.map (Prod.mkHom (𝟙 _) ((pull R f).map β))) at hL
  calc
    _ = (((projectionMap R c a b t hc).app K).app L) ≫
        (image R c).map (a.tensor.map (Prod.mkHom α (𝟙 _))) ≫
        (image R c).map (a.tensor.map (Prod.mkHom (𝟙 _) ((pull R f).map β))) := by
      simp only [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id]
    _ = _ := by
      erw [← Category.assoc, ← hK, Category.assoc, ← hL,
        ← Category.assoc, ← Functor.map_comp]
      simp only [prod_comp, Category.id_comp]
      erw [Category.comp_id]

private theorem cone_naturality
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [HasBinaryBiproducts A] [HasBinaryBiproducts B]
    (F G : A ⥤ B) [F.Additive] [G.Additive] (τ : F ⟶ G)
    {P Q : CochainComplex A ℤ} (v : P ⟶ Q) :
    (NatTrans.mapHomologicalComplex τ (.up ℤ)).app (CochainComplex.mappingCone v) ≫
        (CochainComplex.mappingCone.mapHomologicalComplexIso v G).hom =
      (CochainComplex.mappingCone.mapHomologicalComplexIso v F).hom ≫
        CochainComplex.mappingCone.map
          ((F.mapHomologicalComplex (.up ℤ)).map v)
          ((G.mapHomologicalComplex (.up ℤ)).map v)
          ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P)
          ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app Q)
          ((NatTrans.mapHomologicalComplex τ (.up ℤ)).naturality v) := by
  ext i
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    CochainComplex.mappingCone.mapHomologicalComplexIso,
    HomologicalComplex.Hom.isoOfComponents_hom_f,
    CochainComplex.mappingCone.mapHomologicalComplexXIso,
    CochainComplex.mappingCone.mapHomologicalComplexXIso'_hom,
    Preadditive.comp_add, Preadditive.add_comp, Category.assoc,
    CochainComplex.mappingCone.map, CochainComplex.mappingCone.inl_v_desc_f,
    CochainComplex.mappingCone.inr_f_desc_f, HomComplex.Cochain.zero_cochain_comp_v,
    HomComplex.Cochain.ofHom_v, HomologicalComplex.comp_f,
    NatTrans.mapHomologicalComplex_app_f,
    ← τ.naturality_assoc]


private theorem scalar_triangulated (W : Scheme.{u})
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (φ : R ⟶ S) :
    (pbcDerivedExtend φ).IsTriangulated := by
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} _
  have := pbcDerivedExtension_universal φ
  obtain ⟨σ, hσ, huniq, hadd, htri⟩ :=
    SheafOfModules.derivedScalarExtension_counitShift φ (pbcExtend φ)
      (pbcExtensionExistence φ).choose_spec.choose
      (pbcExtensionExistence φ).choose_spec.choose_spec.choose
      (pbcDerivedExtend φ) (pbcExtensionCounit φ)
  have : NatTrans.CommShift (pbcExtensionCounit φ) ℤ :=
    (scalarCommShift_existsUnique φ).exists.choose_spec
  have he : (pbcDerivedExtend φ).commShiftIso (1 : ℤ) = σ := by
    apply huniq
    intro P
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      NatTrans.shift_app_comm (pbcExtensionCounit φ) (1 : ℤ) P
  constructor
  intro T hT
  simpa only [Functor.mapTriangle_obj, he] using htri T hT

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The specified finite projection evaluated at the actual reductions of K and L.
Source: def-exchange-projection, finite projection composite
(blueprint: lem-sf-concrete-integral-projection-cone). -/
def finiteArrow
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    Arrow (proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1))) :=
  { left := (pullbackTensorFiniteModel l E Y n).tensor.obj
      ((image (finite l E (n + 1) (Nat.succ_pos n)) c).obj
        ((scalarReductionDerivedExtension l E X n).obj K),
        (scalarReductionDerivedExtension l E Y n).obj L)
    right := (image (finite l E (n + 1) (Nat.succ_pos n)) c).obj
      ((pullbackTensorFiniteModel l E X n).tensor.obj
        ((scalarReductionDerivedExtension l E X n).obj K,
          (pull (finite l E (n + 1) (Nat.succ_pos n)) f).obj
            ((scalarReductionDerivedExtension l E Y n).obj L)))
    hom := finiteReductionProjection l E n c
      ((scalarReductionDerivedExtension l E X n).obj K)
      ((scalarReductionDerivedExtension l E Y n).obj L) }

/-- Tensor reduction, followed by compact-support reduction in the first factor.
The initial and final transports are the canonical scalar-adjunction comparisons.
Source: concrete integral reduction step 3; Stacks 06YY and 07A4
(blueprint: lem-sf-concrete-integral-projection-cone). -/
def ordinarySourceComparison
    (aY : SfProEtaleProjection.TensorModel l E Y)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj
        (SfProEtaleProjection.ordinarySource l E c aY K L) ⟶
      (finiteArrow l E c K L n).left :=
  (finiteReductionIso l E Y n).inv.app _ ≫
    (scalarTensor ((reduction l E (n + 1) (Nat.succ_pos n)).map Y)
      aY (pullbackTensorFiniteModel l E Y n)).hom.app
        ((image (completed l E) c).obj K, L) ≫
    (pullbackTensorFiniteModel l E Y n).tensor.map (Prod.mkHom
      ((comparison (reduction l E (n + 1) (Nat.succ_pos n)) c).app K ≫
        (image (finite l E (n + 1) (Nat.succ_pos n)) c).map
          ((finiteReductionIso l E X n).hom.app K))
      ((finiteReductionIso l E Y n).hom.app L))

/-- Compact-support reduction, tensor reduction, and pullback reduction in this order.
Source: concrete integral reduction step 3; Stacks 06YY and 07A4
(blueprint: lem-sf-concrete-integral-projection-cone). -/
def ordinaryTargetComparison
    (aX : SfProEtaleProjection.TensorModel l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj
        ((image (completed l E) c).obj
          (SfProEtaleProjection.ordinaryInner l E f aX K L)) ⟶
      (finiteArrow l E c K L n).right :=
  (finiteReductionIso l E Y n).inv.app _ ≫
    (comparison (reduction l E (n + 1) (Nat.succ_pos n)) c).app _ ≫
    (image (finite l E (n + 1) (Nat.succ_pos n)) c).map
      ((scalarTensor ((reduction l E (n + 1) (Nat.succ_pos n)).map X)
          aX (pullbackTensorFiniteModel l E X n)).hom.app
            (K, (pull (completed l E) f).obj L) ≫
        (pullbackTensorFiniteModel l E X n).tensor.map (Prod.mkHom
          ((finiteReductionIso l E X n).hom.app K)
          ((scalarPull (reduction l E (n + 1) (Nat.succ_pos n)) f).hom.app L ≫
            (pull (finite l E (n + 1) (Nat.succ_pos n)) f).map
              ((finiteReductionIso l E Y n).hom.app L))))

private theorem ordinary_square
    (aX : SfProEtaleProjection.TensorModel l E X)
    (aZ : SfProEtaleProjection.TensorModel l E c.Z)
    (aY : SfProEtaleProjection.TensorModel l E Y)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).map
        (((projectionMap (completed l E) c aX aZ aY
          (completedPull_comp l E c.i c.g)).app K).app L) ≫
      ordinaryTargetComparison l E c aX K L n =
        ordinarySourceComparison l E c aY K L n ≫ (finiteArrow l E c K L n).hom := by
  let bX := pullbackTensorFiniteModel l E X n
  let bZ := pullbackTensorFiniteModel l E c.Z n
  let bY := pullbackTensorFiniteModel l E Y n
  let R := finite l E (n + 1) (Nat.succ_pos n)
  let hc := (proEtaleConstantRingCompositeCoefficients_eq c.i c.g
    (Padic.coefficientExtensionRing l E (n + 1))).symm
  let ξX := (finiteReductionIso l E X n).hom.app K
  let ξY := (finiteReductionIso l E Y n).hom.app L
  have hcoeff := compactSupportProjectionCoefficientChange
    (reduction l E (n + 1) (Nat.succ_pos n)) c aX aZ aY bX bZ bY
    (completedPull_comp l E c.i c.g) hc K L
  have hnat := projection_naturality R c bX bZ bY hc ξX ξY
  dsimp only [ordinarySourceComparison, ordinaryTargetComparison]
  erw [(finiteReductionIso l E Y n).inv.naturality_assoc
    (((projectionMap (completed l E) c aX aZ aY
      (completedPull_comp l E c.i c.g)).app K).app L)]
  have h := congrArg (fun z ↦
    (finiteReductionIso l E Y n).inv.app
        (SfProEtaleProjection.ordinarySource l E c aY K L) ≫ z ≫
      (image R c).map (bX.tensor.map (Prod.mkHom ξX ((pull R f).map ξY)))) hcoeff
  simp only [Category.assoc] at h
  erw [hnat] at h
  dsimp only [R, bX, bY, bZ, ξX, ξY] at h
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, prod_comp,
    Category.id_comp, Category.assoc] at h
  with_unfolding_all dsimp only [finiteArrow, Arrow.hom, Arrow.right,
    finiteReductionProjection, reduction, SfProEtaleProjection.ordinarySource,
    SfProEtaleProjection.ordinaryInner, PurCompactSupport.image, tensorCurried,
    Functor.comp_obj, Functor.curry, Functor.curryObj] at h ⊢
  with_unfolding_all simpa only [Category.assoc] using h

/-- Finite reduction of the target completion unit, inverted using its stated
invertibility witness. Source: concrete integral reduction step 3
(blueprint: lem-sf-concrete-integral-projection-cone). -/
def targetComparison
    (aX : SfProEtaleProjection.TensorModel l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) (n : ℕ)
    (h : IsIso ((scalarReductionDerivedExtension l E Y n).map
      ((image (completed l E) c).map ((IntegralOnSlice.completionUnit l E X none).app
        (SfProEtaleProjection.ordinaryInner l E f aX K L))))) :
    (scalarReductionDerivedExtension l E Y n).obj
        (SfProEtaleProjection.completedTarget l E c aX K L) ⟶
      (finiteArrow l E c K L n).right :=
  @inv _ _ _ _ _ h ≫ ordinaryTargetComparison l E c aX K L n

/-- The signed cone isomorphism for termwise quotient extension and restriction.
Source: concrete cone-transition step 5; Stacks 014E
(blueprint: lem-sf-concrete-integral-projection-cone). -/
def coneComparison (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (v : P ⟶ Q) (n : ℕ) :
    ((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mappingCone v) ≅
      CochainComplex.mappingCone
        (((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).map v) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso v (sfReductionRestricted l E W n)

/-- The map of cones induced by the actual quotient transitions on both summands.
Source: concrete cone-transition step 5; Stacks 014E
(blueprint: lem-sf-concrete-integral-projection-cone). -/
def coneTransition (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (v : P ⟶ Q) (n : ℕ) :
    CochainComplex.mappingCone
        (((sfReductionRestricted l E W (n + 1)).mapHomologicalComplex (.up ℤ)).map v) ⟶
      CochainComplex.mappingCone
        (((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).map v) :=
  CochainComplex.mappingCone.map
    (((sfReductionRestricted l E W (n + 1)).mapHomologicalComplex (.up ℤ)).map v)
    (((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).map v)
    (unrestrictedTowerTransition l E W P n) (unrestrictedTowerTransition l E W Q n)
    (by
      apply HomologicalComplex.hom_ext
      intro i
      exact congrArg (fun a ↦ a.f i) ((unrestrictedIntegralTransition l E W n).naturality v))

/-- Finite derived cone comparison obtained from the universal reduction counit,
then the signed cone comparison. The input is an actual identification with C.
Source: concrete integral cone step 5; Stacks 06YY and 014E
(blueprint: lem-sf-concrete-integral-projection-cone). -/
def derivedConeComparison (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (v : P ⟶ Q)
    {C : DerivedCategory (scalarReductionSource l E W)}
    (e : DerivedCategory.Q.obj (CochainComplex.mappingCone v) ≅ C) (n : ℕ) :
    (scalarReductionDerivedExtension l E W n).obj C ⟶
      DerivedCategory.Q.obj (CochainComplex.mappingCone
        (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).map v)) :=
  (scalarReductionDerivedExtension l E W n).map e.inv ≫
    (scalarReductionDerivedExtension l E W n).map
      ((DerivedCategory.quotientCompQhIso (scalarReductionSource l E W)).inv.app
        (CochainComplex.mappingCone v)) ≫
    (scalarReductionCounit l E W n).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj (CochainComplex.mappingCone v)) ≫
    DerivedCategory.Qh.map
      (((scalarReductionExtension l E W n).mapHomotopyCategoryFactors (.up ℤ)).hom.app
        (CochainComplex.mappingCone v)) ≫
    (DerivedCategory.quotientCompQhIso (scalarReductionTarget l E W n)).hom.app
      (((scalarReductionExtension l E W n).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mappingCone v)) ≫
    DerivedCategory.Q.map
      (CochainComplex.mappingCone.mapHomologicalComplexIso v
        (scalarReductionExtension l E W n)).hom

/-- The same cone identification after scalar restriction, written using the canonical
representative comparison so that its quotient-transition equation is unambiguous.
Source: concrete integral cone step 5; Bhatt--Scholze Definition 3.5.2
(blueprint: lem-sf-concrete-integral-projection-cone). -/
def restrictedDerivedConeComparison (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (v : P ⟶ Q)
    {C : DerivedCategory (scalarReductionSource l E W)}
    (e : DerivedCategory.Q.obj (CochainComplex.mappingCone v) ≅ C) (n : ℕ) :
    (sfDerivedReductionRestricted l E W n).obj C ⟶
      DerivedCategory.Q.obj (CochainComplex.mappingCone
        (((sfReductionRestricted l E W n).mapHomologicalComplex (.up ℤ)).map v)) :=
  (sfDerivedReductionRestricted l E W n).map e.inv ≫
    sfReductionRepresentativeComparison l E W n (CochainComplex.mappingCone v) ≫
    DerivedCategory.Q.map (coneComparison l E W v n).hom

attribute [irreducible] coneComparison coneTransition
  derivedConeComparison restrictedDerivedConeComparison

private theorem transition_eq (W : Scheme.{u})
    (P : CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) :
    unrestrictedTowerTransition l E W P n =
      (NatTrans.mapHomologicalComplex (sfReductionTransition l E W n) (.up ℤ)).app P := by
  apply HomologicalComplex.hom_ext
  intro i
  apply sfReductionTensor_hom_ext l E W (n + 1) (P.X i)
  intro U s x
  exact ((unrestrictedIntegralTransition_existsUnique l E W n).exists.choose_spec
    P i U s x).trans
      ((sfReductionTransition_existsUnique l E W n).exists.choose_spec (P.X i) U s x).symm

private theorem cone_transition (W : Scheme.{u})
    {P Q : CochainComplex (scalarReductionSource l E W) ℤ} (v : P ⟶ Q) (n : ℕ) :
    unrestrictedTowerTransition l E W (CochainComplex.mappingCone v) n ≫
        (coneComparison l E W v n).hom =
      (coneComparison l E W v (n + 1)).hom ≫ coneTransition l E W v n := by
  simpa only [coneComparison, coneTransition, transition_eq] using
    cone_naturality (sfReductionRestricted l E W (n + 1))
      (sfReductionRestricted l E W n) (sfReductionTransition l E W n) v

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence

/-- Shift structure on reduction transported from the universal scalar extension.
Source: Stacks 06YY, exact coefficient change
(blueprint: lem-sf-concrete-integral-projection-cone). -/
@[instance_reducible]
def reductionShift (W : Scheme.{u}) (n : ℕ) :
    (scalarReductionDerivedExtension l E W n).CommShift ℤ :=
  Functor.CommShift.ofIso (finiteReductionIso l E W n) ℤ

private theorem flat_cone_model (W : Scheme.{u})
    {S T C : DerivedCategory (scalarReductionSource l E W)}
    (u : S ⟶ T) (g : T ⟶ C) (d : C ⟶ S⟦(1 : ℤ)⟧)
    (hC : Triangle.mk u g d ∈ distTriang _) :
    ∃ (P Q : CochainComplex (scalarReductionSource l E W) ℤ) (v : P ⟶ Q),
      proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P ∧
      proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) Q ∧
      ∃ (eP : DerivedCategory.Q.obj P ≅ S) (eQ : DerivedCategory.Q.obj Q ≅ T),
        DerivedCategory.Q.map v ≫ eQ.hom = eP.hom ≫ u ∧
        ∃ eC : DerivedCategory.Q.obj (CochainComplex.mappingCone v) ≅ C,
          (∀ n : ℕ, IsIso (derivedConeComparison l E W v eC n)) ∧
          (∀ n : ℕ, IsIso (restrictedDerivedConeComparison l E W v eC n)) ∧
          (∀ n : ℕ,
            (sfDerivedReductionTransition l E W n).app C ≫
                restrictedDerivedConeComparison l E W v eC n =
              restrictedDerivedConeComparison l E W v eC (n + 1) ≫
                DerivedCategory.Q.map (coneTransition l E W v n)) ∧
          ∀ n : ℕ,
            unrestrictedTowerTransition l E W (CochainComplex.mappingCone v) n ≫
                (coneComparison l E W v n).hom =
              (coneComparison l E W v (n + 1)).hom ≫ coneTransition l E W v n := by
  classical
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{u} _
  obtain ⟨P₀, ⟨e₀⟩⟩ := SfProEtaleProjection.goodRepresentative l E W S
  obtain ⟨Q₀, ⟨eQ⟩⟩ := SfProEtaleProjection.goodRepresentative l E W T
  obtain ⟨M, s, hs, t, ht⟩ := DerivedCategory.right_fac (e₀.hom ≫ u ≫ eQ.inv)
  obtain ⟨P, r, hP, hflat, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) M
  have : IsIso (DerivedCategory.Q.map r) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ r).2 hr
  let v := r ≫ t
  let eP : DerivedCategory.Q.obj P ≅ S :=
    asIso (DerivedCategory.Q.map r) ≪≫ asIso (DerivedCategory.Q.map s) ≪≫ e₀
  have hv : DerivedCategory.Q.map v ≫ eQ.hom = eP.hom ≫ u := by
    dsimp only [v, eP, Iso.trans_hom, asIso_hom]
    have he := congrArg (fun z ↦ DerivedCategory.Q.map r ≫
      DerivedCategory.Q.map s ≫ z ≫ eQ.hom) ht
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      IsIso.hom_inv_id_assoc, Functor.map_comp] using he.symm
  have hPflat : proEtaleFlatRepresentatives W
      (completedIntegralCommRingSheafUnrestricted l E W) P := by
    refine ⟨hP, fun i ↦ ?_⟩
    exact ObjectProperty.prop_of_iso (exactFunctor _ _)
      (SheafOfModules.siteSheafTensorRightIso
        (completedIntegralCommRingSheafUnrestricted l E W) (P.X i)).symm (hflat i)
  have hQflat : proEtaleFlatRepresentatives W
      (completedIntegralCommRingSheafUnrestricted l E W) Q₀.obj := Q₀.property
  refine ⟨P, Q₀.obj, v, hPflat, hQflat, eP, eQ, hv, ?_⟩
  let q := HomotopyCategory.quotient (scalarReductionSource l E W) (.up ℤ)
  let ξ := DerivedCategory.quotientCompQhIso (scalarReductionSource l E W)
  let e₁ := ξ.app P ≪≫ eP
  let e₂ := ξ.app Q₀.obj ≪≫ eQ
  have hsquare : (DerivedCategory.Qh.mapTriangle.obj
      (CochainComplex.mappingCone.triangleh v)).mor₁ ≫ e₂.hom =
      e₁.hom ≫ u := by
    dsimp only [e₁, e₂, Iso.trans_hom]
    change DerivedCategory.Qh.map (q.map v) ≫ (ξ.hom.app Q₀.obj ≫ eQ.hom) = _
    erw [ξ.hom.naturality_assoc]
    rw [hv, Category.assoc]
    rfl
  let eT := isoTriangleOfIso₁₂ _ _
    (DerivedCategory.Qh.map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished v)) hC e₁ e₂ hsquare
  let eC : DerivedCategory.Q.obj (CochainComplex.mappingCone v) ≅ C :=
    (ξ.app (CochainComplex.mappingCone v)).symm ≪≫ Triangle.π₃.mapIso eT
  have hcflat : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W)
      (CochainComplex.mappingCone v) :=
    SheafOfModules.isKFlat_mappingCone_independent v hP Q₀.property.1
  refine ⟨eC, ?_, ?_, ?_, cone_transition l E W v⟩
  · intro n
    have : IsIso ((scalarReductionCounit l E W n).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj (CochainComplex.mappingCone v))) :=
      (scalarReductionDerivedExistence l E W n).choose_spec.choose_spec.2.2
        (CochainComplex.mappingCone v) hcflat
    simp only [derivedConeComparison]
    infer_instance
  · intro n
    have := sfComparison_isIso l E W n (CochainComplex.mappingCone v) hcflat
    simp only [restrictedDerivedConeComparison]
    infer_instance
  · intro n
    have ht := (sfDerivedReductionTransition_existsUnique l E W n).exists.choose_spec
      (CochainComplex.mappingCone v)
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mp hcflat)
    change (sfDerivedReductionTransition l E W n).app
      (DerivedCategory.Q.obj (CochainComplex.mappingCone v)) ≫
        sfReductionRepresentativeComparison l E W n (CochainComplex.mappingCone v) = _ at ht
    simp only [restrictedDerivedConeComparison, Category.assoc]
    erw [← (sfDerivedReductionTransition l E W n).naturality_assoc eC.inv]
    rw [← Category.assoc _ _ (DerivedCategory.Q.map (coneComparison l E W v n).hom), ht]
    rw [Category.assoc, ← Functor.map_comp, ← transition_eq, cone_transition]
    simpa only [Category.assoc] using congrArg
      (fun z ↦ (sfDerivedReductionRestricted l E W (n + 1)).map eC.inv ≫
        sfReductionRepresentativeComparison l E W (n + 1) (CochainComplex.mappingCone v) ≫ z)
      (DerivedCategory.Q.map_comp
        (coneComparison l E W v (n + 1)).hom (coneTransition l E W v n))

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Source reduction through the inverse completion unit and the specified tensor/support
comparison. Source: concrete integral reduction step 3
(blueprint: lem-sf-concrete-integral-projection-cone). -/
def sourceComparison
    (aX : SfProEtaleProjection.TensorModel l E X)
    (aY : SfProEtaleProjection.TensorModel l E Y)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y) (n : ℕ) :
    (scalarReductionDerivedExtension l E Y n).obj
        (SfProEtaleProjection.completedSource l E c aY K.obj L.obj) ⟶
      (finiteArrow l E c K.obj L.obj n).left :=
  (scalarReductionDerivedExtension l E Y n).map
      (@inv _ _ _ _ ((IntegralOnSlice.completionUnit l E Y none).app
        (SfProEtaleProjection.ordinarySource l E c aY K.obj L.obj))
        (SfProEtaleProjection.integralDomains l E D hl f c aX aY K L).1) ≫
    ordinarySourceComparison l E c aY K.obj L.obj n

/-- The target completion comparison before reduction. Its inverse after finite reduction
is the canonical completed target comparison. Source: concrete integral reduction step 3
(blueprint: lem-sf-concrete-integral-projection-cone). -/
def targetUnit
    (aX : SfProEtaleProjection.TensorModel l E X)
    (K : DerivedCategory (scalarReductionSource l E X))
    (L : DerivedCategory (scalarReductionSource l E Y)) :
    (image (completed l E) c).obj (SfProEtaleProjection.ordinaryInner l E f aX K L) ⟶
      SfProEtaleProjection.completedTarget l E c aX K L :=
  (image (completed l E) c).map ((IntegralOnSlice.completionUnit l E X none).app
    (SfProEtaleProjection.ordinaryInner l E f aX K L))

/-- Complete endpoints, reduction of the specified integral arrow, and its derived cones.
Source: fix-prop-projection-formula.proof.md, concrete integral steps 1--5
(blueprint: lem-sf-concrete-integral-projection-cone).

Proof:
1. Choose finite cohomological intervals for the first reductions of K and L.
   The residue-Tor theorem gives the same Tor intervals at every positive quotient,
   in particular for arbitrary integral constructible K (lem-coef-integral-residue-tor).
2. Completed pullback and tensor preserve integral constructibility. Compact support
   does so by its prescribed-reductions theorem, using finite dimension of X and the
   uniform Tor interval. Apply these facts to the inner tensor and both endpoints.
   Apply residue-Tor again to each output. No structure morphism is assumed separated.
   Tools: lem-pur-integral-operations-preserve-constructible, lem-kun-dimension-finite-type,
   lem-coef-integral-compact-support, def-weil-derived-complete-integral-detailed.
3. Fix c. Reduce the actual proper counit mate followed by the open tensor map.
   Operation reduction preserves its tensor comparisons, unit, counit and composition
   maps, giving the square with the displayed normalized endpoint comparisons.
   Compact-support successive reduction and the integral-stage comparison datum retain
   the quotient transitions. No invertibility of projection or faithfulness of
   reduction is used. Tools: def-exchange-projection, lem-fix-operation-reduction,
   lem-coef-integral-compact-support.
4. Integral constructibles are triangulated; hence a distinguished cone is complete
   constructible. Exact derived scalar extension sends its triangle to a triangle
   beginning with finite PF under the preceding square. TR3 and the third-isomorphism
   lemma identify its third vertex with any chosen cone of finite PF.
   Tools: lem-weil-integral-constructible-triangulated, lem-pur-derived-change-of-rings,
   lem-sf-triangle-morphism-iso.
5. Choose a flat-term K-flat target representative and use Mathlib right fractions
   to represent the arrow into it. Resolve the source of the roof by a flat-term
   K-flat complex and compose the chain maps. The roof equation gives the required
   endpoint identity, and TR3 identifies its cone with the chosen cone. The cone
   is K-flat by the existing coefficient-independent cone-closure lemma. Scalar extension
   commutes with the signed two-summand cone: both terms and the off-diagonal map
   are tensored with the quotient. Restriction and quotient transitions act on each
   summand. The canonical cone isomorphisms therefore commute with those transitions.
   Resolution independence identifies these with the canonical derived reductions.
   Tools: lem-pc-kflat-resolution, Mathlib DerivedCategory.right_fac,
   lem-pur-derived-change-of-rings, lem-weil-integral-reduction-tower-well-defined. -/
theorem concreteIntegralProjectionCone
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (r : ℕ) (hr : 1 ≤ r)
    (_operations : SixFunctorOperationDatum D
      ({ l := l, different := hl, Qbar := Ω } :
        D.CoefficientDatum)
      E r hr)
    (aX : SfProEtaleProjection.TensorModel l E X)
    (aZ : SfProEtaleProjection.TensorModel l E c.Z)
    (aY : SfProEtaleProjection.TensorModel l E Y)
    (K : sfIntegralConstructibleCategory l E X)
    (L : sfIntegralConstructibleCategory l E Y)
    (_hL : finiteTorConstructibleIntegral l E Y L.obj) :
    finiteTorConstructibleIntegral l E X K.obj ∧
    finiteTorConstructibleIntegral l E X ((integralDerivedPullback l E f).obj L.obj) ∧
    finiteTorConstructibleIntegral l E X
      ((IntegralOnSlice.completion l E X none).obj
        (SfProEtaleProjection.ordinaryInner l E f aX K.obj L.obj)) ∧
    finiteTorConstructibleIntegral l E Y ((image (completed l E) c).obj K.obj) ∧
    finiteTorConstructibleIntegral l E Y
      (SfProEtaleProjection.completedSource l E c aY K.obj L.obj) ∧
    finiteTorConstructibleIntegral l E Y
      (SfProEtaleProjection.completedTarget l E c aX K.obj L.obj) ∧
    ∃ h : ∀ n : ℕ, IsIso ((scalarReductionDerivedExtension l E Y n).map
        (targetUnit l E c aX K.obj L.obj)),
      (∀ n : ℕ,
        IsIso (sourceComparison l E c D hl aX aY K L n) ∧
        IsIso (targetComparison l E c aX K.obj L.obj n (h n)) ∧
        (scalarReductionDerivedExtension l E Y n).map
            (SfProEtaleProjection.integralMap l E D hl f c aX aZ aY K L).hom ≫
          targetComparison l E c aX K.obj L.obj n (h n) =
        sourceComparison l E c D hl aX aY K L n ≫
          (finiteArrow l E c K.obj L.obj n).hom) ∧
      (∀ (C : DerivedCategory (scalarReductionSource l E Y))
        (g : SfProEtaleProjection.completedTarget l E c aX K.obj L.obj ⟶ C)
        (d : C ⟶ (SfProEtaleProjection.completedSource l E c aY K.obj L.obj)⟦(1 : ℤ)⟧),
        Triangle.mk (SfProEtaleProjection.integralMap l E D hl f c aX aZ aY K L).hom
          g d ∈ distTriang _ →
        sfIntegralConstructible l E Y C ∧
        (∀ (n : ℕ)
          (Cn : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)))
          (gn : (finiteArrow l E c K.obj L.obj n).right ⟶ Cn)
          (dn : Cn ⟶ (finiteArrow l E c K.obj L.obj n).left⟦(1 : ℤ)⟧),
          Triangle.mk (finiteArrow l E c K.obj L.obj n).hom gn dn ∈ distTriang _ →
          ∃ e : (@Functor.mapTriangle _ _ _ _ _ _
              (scalarReductionDerivedExtension l E Y n)
              (reductionShift l E Y n)).obj
                (Triangle.mk
                  (SfProEtaleProjection.integralMap l E D hl f c aX aZ aY K L).hom
                  g d) ≅ Triangle.mk (finiteArrow l E c K.obj L.obj n).hom gn dn,
            e.hom.hom₁ = sourceComparison l E c D hl aX aY K L n ∧
            e.hom.hom₂ = targetComparison l E c aX K.obj L.obj n (h n)) ∧
        ∃ (P Q : CochainComplex (scalarReductionSource l E Y) ℤ) (v : P ⟶ Q),
          proEtaleFlatRepresentatives Y (completedIntegralCommRingSheafUnrestricted l E Y) P ∧
          proEtaleFlatRepresentatives Y (completedIntegralCommRingSheafUnrestricted l E Y) Q ∧
          ∃ (eP : DerivedCategory.Q.obj P ≅
              SfProEtaleProjection.completedSource l E c aY K.obj L.obj)
            (eQ : DerivedCategory.Q.obj Q ≅
              SfProEtaleProjection.completedTarget l E c aX K.obj L.obj),
            DerivedCategory.Q.map v ≫ eQ.hom = eP.hom ≫
              (SfProEtaleProjection.integralMap l E D hl f c aX aZ aY K L).hom ∧
            ∃ eC : DerivedCategory.Q.obj (CochainComplex.mappingCone v) ≅ C,
              (∀ n : ℕ, IsIso (derivedConeComparison l E Y v eC n)) ∧
              (∀ n : ℕ, IsIso (restrictedDerivedConeComparison l E Y v eC n)) ∧
              (∀ n : ℕ,
                (sfDerivedReductionTransition l E Y n).app C ≫
                    restrictedDerivedConeComparison l E Y v eC n =
                  restrictedDerivedConeComparison l E Y v eC (n + 1) ≫
                    DerivedCategory.Q.map (coneTransition l E Y v n)) ∧
              ∀ n : ℕ,
                unrestrictedTowerTransition l E Y (CochainComplex.mappingCone v) n ≫
                    (coneComparison l E Y v n).hom =
                  (coneComparison l E Y v (n + 1)).hom ≫ coneTransition l E Y v n) := by
  classical
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of D.k))
  have : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of D.k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k))
  have : CompactSpace Y :=
    QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of D.k))
  have : IsNoetherian X := ⟨⟩
  have : IsNoetherian Y := ⟨⟩
  let (x : X) : Invertible (l : X.residueField x) :=
    (SfProEtaleProjection.residue_unit l D hl X x).invertible
  let (y : Y) : Invertible (l : Y.residueField y) :=
    (SfProEtaleProjection.residue_unit l D hl Y y).invertible
  have torX (M : DerivedCategory (scalarReductionSource l E X))
      (hM : sfIntegralConstructible l E X M) : finiteTorConstructibleIntegral l E X M := by
    rw [← (integral_residue_tor D l hl E X).2]
    exact hM
  have torY (M : DerivedCategory (scalarReductionSource l E Y))
      (hM : sfIntegralConstructible l E Y M) : finiteTorConstructibleIntegral l E Y M := by
    rw [← (integral_residue_tor D l hl E Y).2]
    exact hM
  have support (M : sfIntegralConstructibleCategory l E X) :
      sfIntegralConstructible l E Y ((image (completed l E) c).obj M.obj) :=
    (sfIntegralConstructible l E Y).prop_of_iso
      ((sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) c).app M).symm
      ((sfCompactSupportFiniteIntegralFunctor l D.k
        (coefficientPrimeUnit l D hl) c E).obj M).property
  have hp := SfProEtaleProjection.pull_domains l E f
    (SfProEtaleProjection.finite_dimension D X) (SfProEtaleProjection.finite_dimension D Y)
    (SfProEtaleProjection.scheme_unit l D hl X)
    (SfProEtaleProjection.scheme_unit l D hl Y) L.obj L.property
  have hi := SfProEtaleProjection.tensor_domains l E X
    (SfProEtaleProjection.scheme_unit l D hl X) aX _ _ K.property hp
  have hd := SfProEtaleProjection.integralDomains l E D hl f c aX aY K L
  have hinner : sfIntegralConstructible l E X
      (SfProEtaleProjection.ordinaryInner l E f aX K.obj L.obj) := hi.1
  have hinnerUnit : IsIso ((IntegralOnSlice.completionUnit l E X none).app
      (SfProEtaleProjection.ordinaryInner l E f aX K.obj L.obj)) := hi.2.1
  have hu : ∀ n : ℕ, IsIso ((scalarReductionDerivedExtension l E Y n).map
      (targetUnit l E c aX K.obj L.obj)) := by
    intro n
    dsimp only [targetUnit]
    infer_instance
  have hfinite (n : ℕ) :
      IsIso (sourceComparison l E c D hl aX aY K L n) ∧
      IsIso (targetComparison l E c aX K.obj L.obj n (hu n)) ∧
      (scalarReductionDerivedExtension l E Y n).map
          (SfProEtaleProjection.integralMap l E D hl f c aX aZ aY K L).hom ≫
        targetComparison l E c aX K.obj L.obj n (hu n) =
      sourceComparison l E c D hl aX aY K L n ≫
        (finiteArrow l E c K.obj L.obj n).hom := by
    have hcK := (sfQcqsCompactSupport_finiteComparison l E D.k
      (coefficientPrimeUnit l D hl) c K).2 n
    have hcI := (sfQcqsCompactSupport_finiteComparison l E D.k
      (coefficientPrimeUnit l D hl) c ⟨_, hinner⟩).2 n
    have : IsIso ((IntegralOnSlice.completionUnit l E Y none).app
        (SfProEtaleProjection.ordinarySource l E c aY K.obj L.obj)) := hd.1
    have := hu n
    have hs : IsIso (sourceComparison l E c D hl aX aY K L n) := by
      dsimp only [sourceComparison, ordinarySourceComparison]
      infer_instance
    have ht : IsIso (targetComparison l E c aX K.obj L.obj n (hu n)) := by
      dsimp only [targetComparison, ordinaryTargetComparison]
      infer_instance
    refine ⟨hs, ht, ?_⟩
    dsimp only [SfProEtaleProjection.integralMap, ObjectProperty.homMk_hom,
      targetComparison, sourceComparison, targetUnit]
    simp only [Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
    rw [ordinary_square l E c aX aZ aY K.obj L.obj n]
  refine ⟨torX _ K.property,
    torX _ ((integralOperations_preserve_constructible l E f).1 _ L.property).1,
    torX _ hi.2.2, torY _ (support K), torY _ hd.2.1, torY _ hd.2.2, hu, hfinite, ?_⟩
  intro C g d hC
  refine ⟨(sfIntegralConstructible l E Y).ext_of_isTriangulatedClosed₃
    _ hC hd.2.1 hd.2.2, ?_, ?_⟩
  · intro n Cn gn dn hn
    have := scalar_triangulated Y (projection l E (n + 1) (Nat.succ_pos n) Y)
    let : (scalarReductionDerivedExtension l E Y n).CommShift ℤ := reductionShift l E Y n
    have : NatTrans.CommShift (finiteReductionIso l E Y n).hom ℤ :=
      Functor.CommShift.ofIso_compatibility (finiteReductionIso l E Y n) ℤ
    have : (scalarReductionDerivedExtension l E Y n).IsTriangulated :=
      Functor.isTriangulated_of_iso (finiteReductionIso l E Y n)
    have hs := (hfinite n).1
    have ht := (hfinite n).2.1
    refine ⟨isoTriangleOfIso₁₂ _ _
      ((scalarReductionDerivedExtension l E Y n).map_distinguished _ hC) hn
      (asIso (sourceComparison l E c D hl aX aY K L n))
      (asIso (targetComparison l E c aX K.obj L.obj n (hu n)))
      (hfinite n).2.2, ?_, ?_⟩ <;> rfl
  · exact flat_cone_model l E Y _ g d hC

end WeilConjectures.ConcreteIntegralProjection
