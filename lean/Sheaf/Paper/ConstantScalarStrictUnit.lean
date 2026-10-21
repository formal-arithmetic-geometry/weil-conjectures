/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM, SHEAF group NL
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import Sheaf.Paper.IntegralScalarExtensionUniverses
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Homology.BifunctorShift

/-! # The normalized strict scalar unit of the regular completed coefficient complex

Source: Bhatt--Scholze, Definition 3.5.2 and Lemma 6.8.2(1), and the agent-written
regular-module and strict-cone calculation extracted from blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit).

Positive exponent m is indexed by n = m-1. The recorded interface is retained;
site objects have universe t+1, morphisms t, and coefficients max u (t+1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ConstantScalarStrictUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : Scheme.{t})

/-- The single regular complex R_E[0]. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
abbrev regularComplex :=
  (CochainComplex.singleFunctor (integralTowerModules l E Y) 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))

/-- Its degree-zero identification. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
abbrev regularZeroIso :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))

/-- A section in degree zero. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
def regularSection (V : Y.ProEt)
    (r : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V)) :
    ((regularComplex l E Y).X 0).val.obj (op V) :=
  (regularZeroIso l E Y).inv.val.app (op V) r

/-- The finite regular single complex. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
abbrev finiteRegularComplex (n : ℕ) :=
  (CochainComplex.singleFunctor (integralOperationsFiniteModules l E Y n) 0).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E Y n))

/-- Its degree-zero identification. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
abbrev finiteZeroIso (n : ℕ) :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (integralCoefficientSheaf l E Y n))

/-- The linear limit projection, given by the section one of its restricted target.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def projectionModule (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      (scalarReductionRestriction l E Y n).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (1 : (integralCoefficientSheaf l E Y n).obj.obj U))
      (fun {_ _} f ↦ map_one ((integralCoefficientSheaf l E Y n).obj.map f).hom))

/-- The same projection as a single-complex map with restriction transport.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def projectionComplex (n : ℕ) :
    regularComplex l E Y ⟶
      ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).obj
        (finiteRegularComplex l E Y n) :=
  (CochainComplex.singleFunctor (integralTowerModules l E Y) 0).map
      (projectionModule l E Y n) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (scalarReductionRestriction l E Y n) (ComplexShape.up ℤ) 0).inv.app
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n))

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The strict scalar tower's termwise 1-s. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
def boundary :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj
      (regularComplex l E Y)).obj (op n))
    (integralOperationsTowerStep
      ((integralScalarTowerFunctor l E L ι Y).obj (regularComplex l E Y)))

/-- A degree-zero quotient coordinate of the strict first component.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def coordinate
    (η : regularComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) (n : ℕ) :=
  η.f 0 ≫ (CochainComplex.mappingCocone.fst (boundary l E Y L ι)).f 0 ≫
    (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E L ι Y).obj
      (regularComplex l E Y)).obj (op m)) n).f 0

/-- Full section normalization. The API orders tensors z tensor r.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def quotientCoordinates
    (η : regularComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) : Prop :=
  ∀ (n : ℕ) (V : Y.ProEt)
    (s : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj (op V)),
    (coordinate l E Y L ι η n).val.app (op V) (regularSection l L Y V s) =
      integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) (op V)
        ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app (op V) s)
        (regularSection l E Y V 1)

/-- The equivalent unit-only normalization. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
def unitCoordinates
    (η : regularComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) : Prop :=
  ∀ (n : ℕ) (V : Y.ProEt),
    (coordinate l E Y L ι η n).val.app (op V) (regularSection l L Y V 1) =
      integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) (op V) 1
        (regularSection l E Y V 1)

/-- Vanishing of the graded shifted component. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
def zeroSecondComponent
    (η : regularComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) : Prop :=
  ∀ i : ℤ, η.f i ≫
    (CochainComplex.mappingCocone.snd (boundary l E Y L ι)).v i (i - 1) (by omega) = 0

/-- Multiplication, inverse and reduction formulas for the finite tensors.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def finiteMultiplication : Prop :=
    (∃ u : ∀ n : ℕ,
      (integralScalarFiniteComplex l E L ι Y n).obj (regularComplex l E Y) ≅
        finiteRegularComplex l L Y n,
      (∀ (n : ℕ) (V : Y.ProEt)
        (r : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
        (z : (integralCoefficientSheaf l L Y n).obj.obj (op V)),
        (((u n).hom.f 0 ≫ (finiteZeroIso l L Y n).hom).val.app (op V))
          (integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) (op V)
            z (regularSection l E Y V r)) =
          @Mul.mul ((integralCoefficientCommRingSheaf l L Y n).obj.obj (op V)) _
            ((integralScalarRho l E L ι Y n).hom.app (op V) r) z) ∧
      (∀ (n : ℕ) (V : Y.ProEt)
        (z : (integralCoefficientSheaf l L Y n).obj.obj (op V)),
        (((finiteZeroIso l L Y n).inv ≫ (u n).inv.f 0).val.app (op V)) z =
          integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) (op V)
            z (regularSection l E Y V 1)) ∧
      (∀ (n : ℕ) (V : Y.ProEt)
        (x : (((integralScalarFiniteComplex l E L ι Y (n + 1)).obj
          (regularComplex l E Y)).X 0).val.obj (op V)),
        (((u n).hom.f 0 ≫ (finiteZeroIso l L Y n).hom).val.app (op V))
          (((((integralScalarTransition l E L ι Y n).app
            (regularComplex l E Y)).f 0).val.app (op V)) x) =
        (integralCoefficientSheafTransition l L Y n).hom.app (op V)
          ((((u (n + 1)).hom.f 0 ≫ (finiteZeroIso l L Y (n + 1)).hom).val.app (op V)) x)))

/-- The canonical derived tensor comparison is invertible on the regular complex.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def finiteDerivedComputation : Prop :=
    (∀ n : ℕ, IsIso
      (((integralScalarReductionWitness l E L ι Y n).choose_spec.choose_spec
        |>.choose_spec.choose_spec.2.2).choose_spec.choose.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (regularComplex l E Y))))

/-- Identity-extension reduction units are precisely the limit projections.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def reductionUnits : Prop :=
    (∀ n : ℕ, ∃ v : unrestrictedTowerFiniteComplex l E Y n (regularComplex l E Y) ≅
        finiteRegularComplex l E Y n,
      (∀ (V : Y.ProEt) (z : (integralCoefficientSheaf l E Y n).obj.obj (op V)),
        (((finiteZeroIso l E Y n).inv ≫ v.inv.f 0).val.app (op V)) z =
          unrestrictedTowerTensorSection l E Y n ((regularComplex l E Y).X 0) (op V)
            z (regularSection l E Y V 1)) ∧
      unrestrictedTowerUnit l E Y (regularComplex l E Y) n ≫
        ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).map v.hom =
          projectionComplex l E Y n ∧
      (∀ hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E Y)
        (𝟙 (regularComplex l E Y)),
        canonicalIntegralReductionTowerMap l E Y (𝟙 (regularComplex l E Y)) hq n ≫
          DerivedCategory.Q.map
            (((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).map v.hom) =
          DerivedCategory.Q.map (projectionComplex l E Y n)))

/-- The strict-unit assertion, including all multiplication and reduction formulas.
Source: Bhatt--Scholze, Definition 3.5.2 and Lemma 6.8.2(1), background for the
agent-written strict calculation in blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit).

Proof:
1. Sectionwise balancing gives M tensor R_E isomorphic to M, with inverse x to x tensor 1.
The maps commute with restrictions and descend through sheafification. Thus the regular
and zero sheaves are flat (def-pc-flat-sheaf-modules). The direct-sum total tensor with
R_E[0] is the original complex with its original differential
(def-pc-tensor-complex-sheaves), proving K-flatness (def-pc-kflat-complex).
2. Multiplication sends r tensor z to rho_n(r)z and has inverse z to 1 tensor z.
Balancing proves inverse identities before and after sheafification
(def-pur-sheaf-tensor-product, def-weil-presheaf-modules-sheafification). The complexes
are single complexes. The identity K-flat resolution computes derived scalar extension
by def-weil-integral-scalar-extension.
3. Reduction sends rho_(n+1)(r)z to rho_n(r)red(z), proving transition compatibility.
For the identity coefficient extension gamma sends r to r tensor 1, so multiplication
composed with gamma is pi_n. With q=id the c_n formula in
 def-weil-integral-reduction-tower is exactly the localized gamma using
 def-weil-integral-derived-reduction.
4. Set h_n(s)=1 tensor pi_n(s). It is R_L-linear under restriction along pi_n.
Reduction compatibility gives t_n h_(n+1)=h_n, so its product h is killed by 1-shift.
Products are sectionwise; no exactness or surjectivity of products is used.
5. The normalized strict mapping-cocone differential is (dx,(1-s)x-dy).
The pair (h,0) therefore defines a chain map from R_L[0], with all other source
components zero (def-weil-abstract-derived-category).
6. The product coordinates and two graded cone projections determine the map.
Linearity gives h_n(b)=b h_n(1), proving the equivalent unit-only normalization
also when 1=0 (def-weil-sheaf-of-modules-category).
-/
theorem regular_scalar_strict_unit (D : FiniteFieldDatum.{d}) (_hl : l ≠ D.p) :
    integralOperationsGoodComplex l E Y (regularComplex l E Y) ∧
    finiteMultiplication l E Y L ι ∧
    finiteDerivedComputation l E Y L ι ∧
    reductionUnits l E Y ∧
    (∃! η : regularComplex l L Y ⟶
        (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y),
      quotientCoordinates l E Y L ι η ∧ zeroSecondComponent l E Y L ι η) ∧
    (∀ η : regularComplex l L Y ⟶
        (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y),
      quotientCoordinates l E Y L ι η ↔ unitCoordinates l E Y L ι η) := by
  sorry

end WeilConjectures.ConstantScalarStrictUnit
