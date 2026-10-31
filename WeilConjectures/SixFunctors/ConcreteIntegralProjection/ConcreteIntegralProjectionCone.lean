/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
public import WeilConjectures.SixFunctors.Finite.FiniteProjectionOperationPresentation
import all WeilConjectures.SixFunctors.SfProEtaleProjection.SfProEtaleProjectionFormula
import all WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import all WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import WeilConjectures.SixFunctors.PurCompactSupport.CompactSupportProjectionCoefficientChange
import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportFiniteComparison
import WeilConjectures.Algebra.Homology.Derived.DerivedScalarExtensionCounitShift
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.SixFunctors.Integral.IntegralReductionTowerWellDefinedUnrestricted

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

attribute [local irreducible] scalarReductionExistence scalarReductionDerivedExistence

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

end WeilConjectures.ConcreteIntegralProjection
