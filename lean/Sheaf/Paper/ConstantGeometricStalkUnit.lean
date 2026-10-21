/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.Paper.IsomorphismDerivedPullback

public import Sheaf.Paper.FiniteFieldFiber

public import Sheaf.Paper.ConstantWeilStructure
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison
public import Sheaf.AlgebraicGeometry.FrobeniusDetailed
import Sheaf.FieldTheory.UniqueSubfieldOfClosure
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
public import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections
public import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingComposition
import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.FiniteRegularCoefficientComparisons
public import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.Paper.InverseImagePullbackComparisonDerived
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.ConstantCoefficientScalarNormalization
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.Paper.IntegralPointTransportTowerPowers
public import Sheaf.Paper.SfRationalizationKaroubi

/-! # Constant geometric stalks and the coefficient unit

Source: main-20261015, sec-zeta-weil/sk-thm-tracetodeterminant,
prop-every-iterate-trace.proof.md, constant-sheaf clause, reviewed expansion step 5
(blueprint: lem-zl-constant-geometric-stalk-unit).

All finite indices denote exponent m+1. The integral coefficient is the completed
ring sheaf. The maps below retain the actual adjunction units and strict Roos model.

## Main statements

* `embeddingPoint_return`: the semilinear return for every allowed embedding.
* `finiteStalkUnit`, `integralStalkUnit`, `rationalStalkUnit`: coefficient-unit coordinates.
* `finiteOperator_unit`, `integralOperator_unit`, `rationalOperator_unit`: identity operators.
* `finiteUnit_reduction`, `integralUnit_projection`, `section_reductions`: actual quotient squares.
* `rationalStalkUnit_existsUnique`, `rationalOperator_scalar`: rationalization squares.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.ConstantGeometricStalkUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Multiplication on the finite coefficient unit, as the adjoint of the constant section one.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteUnitHom {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    (sfIntrinsicPullback (Padic.coefficientExtensionRing l E (m + 1)) f).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E Y m)) ⟶
      SheafOfModules.unit (integralCoefficientSheaf l E X m) :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
  ((sfIntrinsicConstantModuleAdjunction f
    (Padic.coefficientExtensionRing l E (m + 1))).homEquiv _ _).symm
      ((SheafOfModules.unitHomEquiv _).symm
        (PresheafOfModules.sectionsMk (fun U ↦ (1 : (integralCoefficientSheaf l E X m).obj.obj
          ((proEtaleBaseChange f).op.obj U)))
          (fun {_ _} a ↦ map_one ((integralCoefficientSheaf l E X m).obj.map
            ((proEtaleBaseChange f).op.map a)).hom)))

/-- The finite multiplication is invertible, including the first positive quotient.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: in tensor coordinates the map is z tensor b ↦ c_f(z)b; its inverse sends b to
1 tensor b. The balancing relation makes the two composites identities. The intrinsic
realization and adjunction preserve this unit-normalized map. -/
theorem finiteUnitHom_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    IsIso (finiteUnitHom l E f m) := by
  sorry

/-- The finite derived unit comparison, with its exact single-complex comparison.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteUnit {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) :
    (finiteDerivedPullback l E m f).obj (finiteConstantCoefficientObject l E Y m) ≅
      finiteConstantCoefficientObject l E X m :=
  letI := Padic.finite_coefficientExtensionRing l E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
  ((sfIntrinsicPullback
    (Padic.coefficientExtensionRing l E (m + 1)) f).mapDerivedCategorySingleFunctor
      0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (@asIso _ _ _ _ (finiteUnitHom l E f m) (finiteUnitHom_isIso l E f m))

/-- The normalized strict unit for arbitrary scheme maps, extending the same owning-node
construction used for the Weil automorphism.
Source: reviewed expansion steps 2, 5 and 6
(blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the compatible finite generators are the adjunction images of 1 tensor 1.
Their product is killed by 1-shift. Use mappingCocone.lift with zero shifted component.
Maps from the regular module are determined by the global section one; the terminal
object is a base-change object. This proves existence and uniqueness with the displayed
normalization, without choosing a filler in a triangulated homotopy limit. -/
theorem integralChainUnit_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! η : constantWeilIntegralComplex l E X ⟶
        (integralOperationsPullbackComplexFunctor l E f).obj
          (constantWeilIntegralComplex l E Y),
      (∀ (m : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (constantWeilPullbackRoosEndomorphism l E f)).f 0 ≫
          (Pi.π (fun j ↦ (constantWeilPullbackTower l E f).obj (op j)) m).f 0).val.app
            (op ((proEtaleBaseChange f).obj V)))
          (constantWeilUnitSection l E X ((proEtaleBaseChange f).obj V)) =
        integralOperationsPullbackGenerator l E f m
          (((unrestrictedIntegralFiniteComplex l E Y m).obj
            (constantWeilIntegralComplex l E Y)).X 0) V
          (constantWeilReducedUnitSection l E Y m V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (constantWeilPullbackRoosEndomorphism l E f)).v i (i - 1) (by omega) = 0) := by
  sorry

/-- The uniquely specified strict chain map, with real cochain data.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralChainUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (integralChainUnit_existsUnique l E f).exists.choose

/-- The strict coefficient unit is a quasi-isomorphism for arbitrary pullback.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: finite multiplication identifies the entire pulled quotient system with the
constant quotient system on X, including its actual transitions. Its surjective tower
has limit the completed ring sheaf. The zero-homotopy map above is its Roos comparison;
the surjective-tower derived-limit theorem makes it a quasi-isomorphism. -/
theorem integralChainUnit_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (DerivedCategory.Q.map (integralChainUnit l E f)) := by
  sorry

/-- The integral unit identification uses the inverse normalized strict-cone map.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralDerivedPullback l E f).obj (integralConstantCoefficientObject l E Y) ≅
      integralConstantCoefficientObject l E X :=
  (integralDerivedPullbackComparison l E f).app (constantWeilIntegralGood l E Y) ≪≫
    (@asIso _ _ _ _ (DerivedCategory.Q.map (integralChainUnit l E f))
      (integralChainUnit_isIso l E f)).symm



/-- The intrinsic finite multiplication is exactly c_m composed with lambda_m,
using the canonical unit-preserving comparison of the two pullback presentations.
Source: reviewed expansion steps 2 and 3
(blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the model comparison is uniqueness of left adjoints preserving their units.
The inverse tensor-unit map lambda_m is multiplication, and c_m acts on each constant
coefficient by that same coefficient. Both sides send every adjunction generator
z tensor b to c_m(z)b. They agree before localization and hence in the derived category. -/
theorem finiteUnit_canonicalWeil {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (m : ℕ) :
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    (finiteRegularKappa l E g m).f 0 ≫
      (inverseImageFiniteIntrinsicPullbackComparison g
        (Padic.coefficientExtensionRing l E (m + 1))).hom.app
          ((finiteRegularCoefficientComplex l E Y m).X 0) ≫
        finiteUnitHom l E g m =
      (finiteRegularComparison l E g m).hom.f 0 := by
  sorry

/-- The generalized strict unit agrees with the recorded canonical integral Weil map.
Source: reviewed expansion steps 6 and 7
(blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: both strict units have the same finite generators and zero shifted component.
The uniqueness clause of constantWeilChainUnit_existsUnique identifies their chain maps.
Their good-representative comparisons coincide, and c composed with lambda cancels
the two inverse coefficient comparisons in constantWeilIntegralTheta. -/
theorem integralUnit_canonicalWeil {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    integralUnit l E g = constantWeilIntegralTheta l E g := by
  sorry

/-- Multiplication respects every finite quotient on every pullback generator.
Source: reviewed expansion steps 2 and 5
(blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the adjunction unit sends a to a tensor 1, multiplication sends this to the
constant section a, and constant sheafification is natural in the quotient ring map.
These are all generators after the sheafified tensor construction, so the equation
is the actual reduction square, before exact single and section functors are applied. -/
theorem finiteUnit_reduction {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) (V : Y.ProEt)
    (a : (integralCoefficientSheaf l E Y (m + 1)).obj.obj (op V)) :
    letI := Padic.finite_coefficientExtensionRing l E (m + 2) (by omega)
    letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    (integralCoefficientSheafTransition l E X m).hom.app
        (op ((proEtaleBaseChange f).obj V))
      (((finiteUnitHom l E f (m + 1)).val.app
        (op ((proEtaleBaseChange f).obj V)))
          (((sfIntrinsicConstantModuleAdjunction f
            (Padic.coefficientExtensionRing l E (m + 2))).unit.app
              (SheafOfModules.unit (integralCoefficientSheaf l E Y (m + 1)))).val.app
                (op V) a)) =
      (finiteUnitHom l E f m).val.app (op ((proEtaleBaseChange f).obj V))
        (((sfIntrinsicConstantModuleAdjunction f
          (Padic.coefficientExtensionRing l E (m + 1))).unit.app
            (SheafOfModules.unit (integralCoefficientSheaf l E Y m))).val.app (op V)
              ((integralCoefficientSheafTransition l E Y m).hom.app (op V) a)) := by
  sorry

/-- The strict integral unit's actual nth Roos projection on every regular section.
Source: reviewed expansion steps 5--7 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the regular-module map is linear and its value on one is the normalized
finite generator. Scalar action on the nth restricted tower term factors through
its actual quotient projection. Thus the formula follows for every regular section.
Together with the zero shifted component, this determines the entire strict cone
map and all projections, rather than just its finite isomorphism classes. -/
theorem integralUnit_projection {X Y : Scheme.{u}} (f : X ⟶ Y) (m : ℕ) (V : Y.ProEt)
    (a : (completedIntegralCoefficientSheafUnrestricted l E X).obj.obj
      (op ((proEtaleBaseChange f).obj V))) :
    ((integralChainUnit l E f).f 0 ≫
      (CochainComplex.mappingCocone.fst
        (constantWeilPullbackRoosEndomorphism l E f)).f 0 ≫
      (Pi.π (fun j ↦ (constantWeilPullbackTower l E f).obj (op j)) m).f 0).val.app
        (op ((proEtaleBaseChange f).obj V))
      (((HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X))).inv.val.app
          (op ((proEtaleBaseChange f).obj V))) a) =
      @SMul.smul
        ((integralCoefficientSheaf l E X m).obj.obj
          (op ((proEtaleBaseChange f).obj V)))
        (((integralOperationsLevelPullback l E f m).obj
          (((unrestrictedIntegralFiniteComplex l E Y m).obj
            (constantWeilIntegralComplex l E Y)).X 0)).val.obj
              (op ((proEtaleBaseChange f).obj V))) inferInstance
        ((limit.π (integralCoefficientSheafSystem l E X) (op m)).hom.app
          (op ((proEtaleBaseChange f).obj V)) a)
          (integralOperationsPullbackGenerator l E f m
            (((unrestrictedIntegralFiniteComplex l E Y m).obj
              (constantWeilIntegralComplex l E Y)).X 0) V
            (constantWeilReducedUnitSection l E Y m V)) := by
  sorry

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The coefficient-to-section map at the finite point, preserving every constant a.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteSection (m : ℕ) :
    ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) m)) :=
  ModuleCat.ofHom
    (Y := (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).obj
      (SheafOfModules.unit (integralCoefficientSheaf l E (Spec (.of D.k)) m)))
    { toFun := pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (m + 1))
      map_add' := map_add _
      map_smul' := fun a b ↦ by
        change _ = (pointConstantSectionMap D.k
          (Padic.coefficientExtensionRing l E (m + 1)) a) *
            (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (m + 1)) b)
        exact map_mul _ a b }

/-- The coefficient-to-section map for completed integral scalars.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralSection :
    ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      (pointIntegralSections l E D.k).obj
        (SheafOfModules.unit
          (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))) :=
  ModuleCat.ofHom
    (Y := (pointIntegralSections l E D.k).obj
      (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))
    { toFun := pointIntegralSectionMap l E D.k
      map_add' := map_add _
      map_smul' := fun a b ↦ by
        change _ = pointIntegralSectionMap l E D.k a * pointIntegralSectionMap l E D.k b
        exact map_mul _ a b }

/-- Both section maps are invertible with the canonical coefficient actions.
Source: reviewed expansion steps 2 and 6 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: Spec k has one point. Finite constant sections are the coefficient ring by
constant functions and evaluation. Limits of sheaves are sectionwise, so completed
sections are lim A_m. Completeness of the coefficient DVR identifies this limit with
O_E via its actual quotient maps; uniqueness follows from separatedness. -/
theorem section_isIso :
    (∀ m : ℕ, IsIso (finiteSection l E D m)) ∧ IsIso (integralSection l E D) := by
  sorry

/-- Finite sections identified with the regular coefficient module in degree zero.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteSectionsUnit (m : ℕ) :
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.obj
        (finiteConstantCoefficientObject l E (Spec (.of D.k)) m) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))) :=
  ((pointFiniteSections D.k
    (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategorySingleFunctor
    0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (@asIso _ _ _ _ (finiteSection l E D m) ((section_isIso l E D).1 m)).symm

/-- Completed integral sections in coefficient-unit coordinates.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralSectionsUnit :
    (pointFibreIntegralAmbient D l E).obj (integralConstantCoefficientObject l E (Spec (.of D.k))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  ((pointIntegralSections l E D.k).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (@asIso _ _ _ _ (integralSection l E D) (section_isIso l E D).2).symm

/-- The actual section coordinates preserve quotient transitions and completion projections.
Source: reviewed expansion steps 5, 6 and 8
(blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: naturality of constant sheafification gives the first equation. The defining
limit lift of integralConstantToCompletion has the actual quotient cone as its legs,
which gives the second equation after evaluation at the final object. -/
theorem section_reductions (m : ℕ) :
    (∀ a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 2)),
      (integralCoefficientSheafTransition l E (Spec (.of D.k)) m).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (finiteSection l E D (m + 1) a) =
          finiteSection l E D m (ULift.up
            (Padic.coefficientExtensionTransition l E (m + 1) a.down))) ∧
    (∀ a : ULift.{u + 1} (Padic.coefficientExtensionIntegers l E),
      (limit.π (integralCoefficientSheafSystem l E (Spec (.of D.k))) (op m)).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of D.k))))) (integralSection l E D a) =
          finiteSection l E D m (ULift.up
            (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (m + 1)) a.down))) := by
  sorry

variable (Y₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The canonical finite geometric stalk identification, before any Frobenius calculation.
Source: reviewed expansion step 2 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteStalkUnit (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m : ℕ) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.mapIso
    (finiteUnit l E x m) ≪≫ finiteSectionsUnit l E D m

/-- The canonical completed integral geometric stalk identification.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralStalkUnit (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  (pointFibreIntegralAmbient D l E).mapIso (integralUnit l E x) ≪≫ integralSectionsUnit l E D

/-- Iteration of the actual finite Weil maps with the specified pullback compositors.
Source: reviewed expansion step 3 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteWeilIterate (m : ℕ) : (r : ℕ) →
    (finiteDerivedPullback l E m (localPositivePower (D.geometricFrobenius Y₀).hom r)).obj
        (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m) ≅
      finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m
  | 0 => finiteUnit l E (D.geometricFrobenius Y₀).hom m
  | r + 1 =>
    (finiteCanonicalPullbackComposition l E (localPositivePower (D.geometricFrobenius Y₀).hom r)
      (D.geometricFrobenius Y₀).hom m).app _ ≪≫
      (finiteDerivedPullback l E m
        (localPositivePower (D.geometricFrobenius Y₀).hom r)).mapIso
          (finiteUnit l E (D.geometricFrobenius Y₀).hom m) ≪≫ finiteWeilIterate m r

/-- Iterate restriction-and-coprojection transport, retaining the actual finite comparisons.
Source: reviewed expansion step 4 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteTransportIterate (m : ℕ)
    (N : proEtaleDerivedCategory (Spec (.of D.k))
      (Padic.coefficientExtensionRing l E (m + 1))) : (r : ℕ) →
    (pointFiniteSections D.k
      (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.obj N ⟶
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.obj
        ((finiteDerivedPullback l E m (localPositivePower (frobeniusPointIso D).hom r)).obj N)
  | 0 => frobeniusPointTransportFinite D l hl E m N
  | r + 1 =>
    frobeniusPointTransportFinite D l hl E m N ≫
      finiteTransportIterate m
        ((finiteDerivedPullback l E m (frobeniusPointIso D).hom).obj N) r ≫
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
        ((finiteCanonicalPullbackComposition l E (localPositivePower (frobeniusPointIso D).hom r)
          (frobeniusPointIso D).hom m).inv.app N)

/-- The actual local finite operator at a semilinearly returning geometric point.
Source: reviewed expansion step 4 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def finiteOperator (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x) :=
  finiteTransportIterate l E D hl m
      ((finiteDerivedPullback l E m x).obj
        (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m)) r ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
      (((finiteCanonicalPullbackComposition l E
          (localPositivePower (frobeniusPointIso D).hom r) x m).symm.app
          (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m) ≪≫
        eqToIso (congrArg (fun (f : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) ↦
          (finiteDerivedPullback l E m f).obj
          (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m)) h.symm) ≪≫
        (finiteCanonicalPullbackComposition l E x
          (localPositivePower (D.geometricFrobenius Y₀).hom r) m).app
          (finiteConstantCoefficientObject l E (D.geometricFiber Y₀).left m)).hom) ≫
    (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.map
      ((finiteDerivedPullback l E m x).map (finiteWeilIterate l E D Y₀ m r).hom)



/-- The integral stalk in the published full constructible category.
Source: reviewed expansion step 6 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralStalk (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (constructibleIntegralPullback l E x).obj
    (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left)

/-- Iterate the published completed integral Weil comparison.
Source: reviewed expansion steps 3 and 7 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralWeilIterate : (r : ℕ) →
    (@constructibleIntegralPullback l _ E _ _ _ _ _
      (localPositivePower (D.geometricFrobenius Y₀).hom r)
      (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).obj
        (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left) ≅
      constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left
  | 0 => constantWeilConstructibleIntegralTheta l E D hl Y₀
  | r + 1 =>
    letI := sfWeilPrimeInvertible D l hl Y₀
    ((integralPullbackComposition l E).choose
      (localPositivePower (D.geometricFrobenius Y₀).hom r)
      (D.geometricFrobenius Y₀).hom).app _ ≪≫
      (constructibleIntegralPullback l E
        (localPositivePower (D.geometricFrobenius Y₀).hom r)).mapIso
          (constantWeilConstructibleIntegralTheta l E D hl Y₀) ≪≫
        integralWeilIterate r

/-- Iterate the actual integral point transports, with the specified composition maps.
Source: reviewed expansion step 7 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralTransportIterate (N : sfIntegralConstructibleCategory l E (Spec (.of D.k))) :
    (r : ℕ) →
    ((pointIntegralFibre D l hl E).obj N).obj ⟶
      ((pointIntegralFibre D l hl E).obj
        ((@constructibleIntegralPullback l _ E _ _ _ _ _
          (localPositivePower (frobeniusPointIso D).hom r)
          (frobeniusPointPrimeInvertible D l hl)
          (frobeniusPointPrimeInvertible D l hl)).obj N)).obj
  | 0 => frobeniusPointTransportIntegral D l hl E N.obj
  | r + 1 =>
    letI := frobeniusPointPrimeInvertible D l hl
    frobeniusPointTransportIntegral D l hl E N.obj ≫
      integralTransportIterate
        ((constructibleIntegralPullback l E (frobeniusPointIso D).hom).obj N) r ≫
      (pointFibreIntegralAmbient D l E).map
        (((integralPullbackComposition l E).choose
          (localPositivePower (frobeniusPointIso D).hom r)
          (frobeniusPointIso D).hom).inv.app N).hom

/-- Integral local Frobenius: transport, semilinear return, and the iterated Weil map.
Source: reviewed expansion step 7 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def integralOperator (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (r : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  integralTransportIterate l E D hl (integralStalk l E D hl Y₀ x) r ≫
    (pointFibreIntegralAmbient D l E).map
      ((((integralPullbackComposition l E).choose
          (localPositivePower (frobeniusPointIso D).hom r) x).symm.app
            (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left) ≪≫
        eqToIso (congrArg (fun (f : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) ↦
          (constructibleIntegralPullback l E f).obj
          (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left)) h.symm) ≪≫
        ((integralPullbackComposition l E).choose x
          (localPositivePower (D.geometricFrobenius Y₀).hom r)).app
            (constantWeilIntegralObject l E D hl (D.geometricFiber Y₀).left)).hom).hom ≫
    (pointFibreIntegralAmbient D l E).map
      ((constructibleIntegralPullback l E x).map (integralWeilIterate l E D hl Y₀ r).hom).hom

/-- Compatibility needed to form the lift for any base-field embedding of the
specified finite extension, rather than only the chosen subfield inclusion.
Source: reviewed expansion step 1 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: functoriality of Spec turns the base-field compatibility of the embedding
into the required equality; compose with the defining Over-morphism equation of x. -/
theorem embeddingPoint_compatible (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    (Spec.map (CommRingCat.ofHom ι) ≫ x.left) ≫ Y₀.hom =
      (𝟙 (Spec (.of D.k))) ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  sorry

/-- The actual geometric point from any allowed finite-field embedding.
Source: reviewed expansion step 1 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def embeddingPoint (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom ι) ≫ x.left) (𝟙 _)
    (embeddingPoint_compatible D Y₀ n hn x ι hι)

/-- The semilinear return for every base-field embedding into the closure.
Source: reviewed expansion step 1 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: every embedding has image the unique subfield of cardinality q^n. The nth
geometric Frobenius fixes it pointwise. Compare the two projections of the geometric
fiber pullback: the model maps agree by this fixed-field calculation and the closure
maps agree by the geometric Frobenius definition. Pullback uniqueness proves return. -/
theorem embeddingPoint_return (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    embeddingPoint D Y₀ n hn x ι hι ≫
        localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
      localPositivePower (frobeniusPointIso D).hom (n - 1) ≫
        embeddingPoint D Y₀ n hn x ι hι := by
  sorry

/-- The finite local operator is the coefficient identity under the canonical stalk iso.
Source: reviewed expansion steps 1--5 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the image of F_(q^n) is the unique subfield of its order, fixed pointwise by
geometric Frobenius to the nth power. Pullback uniqueness gives the semilinear return,
as in localExtensionPoint_return. Finite unit multiplication sends z tensor b to
c(z)b, commutes with the actual pullback compositor, and identifies the iterated
Weil maps with unit multiplication. Restriction, insertion in the inverse-image
colimit and sheafification all preserve a constant a. The tensor unit and multiplication
then send a to a. Naturality repeats the calculation at every transport in the iterate.
The return square has the same coefficient coordinates on both paths. Thus the entire
local composite is identity, including n=1 and m=0 (exponent one). -/
theorem finiteOperator_unit (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) (m : ℕ) :
    finiteOperator l E D hl Y₀ (embeddingPoint D Y₀ n hn x ι hι) m (n - 1)
        (embeddingPoint_return D Y₀ n hn x ι hι) ≫
      (finiteStalkUnit l E D Y₀ (embeddingPoint D Y₀ n hn x ι hι) m).hom =
        (finiteStalkUnit l E D Y₀ (embeddingPoint D Y₀ n hn x ι hι) m).hom := by
  sorry

/-- The completed integral local operator is identity on the whole derived stalk.
Source: reviewed expansion steps 1, 6 and 7 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the integral regular module is a flat-term K-flat model. Its finite reductions
are the regular quotient modules with the actual quotient transitions. The compatible
finite multiplication maps identify its pulled strict tower with the coefficient tower
at s. The zero-shifted-component comparison identifies the whole Roos complex with
the completed integral unit. Sectionwise limits and completeness identify sections
with O_E, and all projections with the quotient maps. The normalized inverse-image
comparison and whole-system point-transport power laws identify the actual integral
local operator with this reconstructed finite identity. This uses equality of strict
system maps and their normalized cone maps, not detection by unrelated finite reductions. -/
theorem integralOperator_unit (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    integralOperator l E D hl Y₀ (embeddingPoint D Y₀ n hn x ι hι) (n - 1)
        (embeddingPoint_return D Y₀ n hn x ι hι) ≫
      (integralStalkUnit l E D Y₀ (embeddingPoint D Y₀ n hn x ι hι)).hom =
        (integralStalkUnit l E D Y₀ (embeddingPoint D Y₀ n hn x ι hι)).hom := by
  sorry



/-- The fraction-field tensor of the regular integral module is the regular field module.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def rationalRegular :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)).obj
        (ModuleCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ≅
      ModuleCat.of (ULift.{u + 1} E) (ULift.{u + 1} E) :=
  letI := (pointIntegralToField l E).toAlgebra
  (TensorProduct.AlgebraTensorModule.rid (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (ULift.{u + 1} E) (ULift.{u + 1} E)).toModuleIso

/-- The actual rational stalk lifted to the section universe is the tensor of its
integral stalk; these are the prescribed object identities and size-descent counit.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def rationalFibreComparison (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    (pointFibreModuleLift E).mapDerivedCategory.obj
        (localPointComplex l E D hl Y₀ (constantWeilRationalComplex l E D hl Y₀) x).obj ≅
      (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (pointIntegralToField l E)).mapDerivedCategory.obj
          ((pointFibreIntegralAmbient D l E).obj (integralStalk l E D hl Y₀ x).obj) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := pointFibreSizeLift_equivalence E
  (pointFibreModuleLift E).mapDerivedCategory.mapIso
    ((DerivedCategory.pointFiniteDimensional E).ι.mapIso
      ((pointRationalFibre D l hl E).mapIso
        (localPullbackObjectIso l E x
          (constantWeilRationalObject l E D hl (D.geometricFiber Y₀).left)) ≪≫
        pointRationalFibreObjIso D l hl E
          ((sfRationalConstructibleLocalization l E (Spec (.of D.k))).obj
            (integralStalk l E D hl Y₀ x)))) ≪≫
    (DerivedCategory.pointFiniteDimensional (ULift.{u + 1} E)).ι.mapIso
      ((pointFibreSizeLift E).asEquivalence.counitIso.app
        (pointFibreRationalLarge D l hl E (integralStalk l E D hl Y₀ x)))

/-- The canonical large rational unit identification, obtained by tensoring the integral one.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def rationalStalkUnitLarge (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  rationalFibreComparison l E D hl Y₀ x ≪≫
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategory.mapIso (integralStalkUnit l E D Y₀ x) ≪≫
    ((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (pointIntegralToField l E)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (rationalRegular l E) ≪≫
    ((pointFibreModuleLift E).mapDerivedCategorySingleFunctor 0).symm.app (ModuleCat.of E E)

/-- The small rational unit is uniquely determined by its actual scalar-normalization square.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: the large map is integral unit multiplication tensor E, with the specified
rational object comparisons and size-descent counit. Its source and target have bounded
finite-dimensional cohomology. The equivalence pointFibreSizeLift is fully faithful
on this subcategory, so the large map and its inverse descend uniquely. Faithfulness
reflects both inverse equations. This gives a unique isomorphism with the displayed
normalization, not an arbitrary choice of a point-unit isomorphism. -/
theorem rationalStalkUnit_existsUnique
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :
    ∃! e : (localPointComplex l E D hl Y₀
        (constantWeilRationalComplex l E D hl Y₀) x).obj ≅
          (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of E E),
      (pointFibreModuleLift E).mapDerivedCategory.mapIso e =
        rationalStalkUnitLarge l E D hl Y₀ x := by
  sorry

/-- The rational geometric stalk identification with E[0], normalized by integral tensor.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit). -/
def rationalStalkUnit (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) :=
  (rationalStalkUnit_existsUnique l E D hl Y₀ x).exists.choose

/-- The rational local operator is identity in the same canonical coefficient coordinates.
Source: reviewed expansion steps 1 and 8 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: theta_E and rational point transport are the images of their integral counterparts
under exact tensor with E, with the recorded boundary comparisons. The rational pullback
compositors are the localized integral ones, so all three factors of localFrobeniusOperator
are the corresponding integral factors after tensor. Apply integralOperator_unit to the
whole-system identity, tensor it with E, and cancel the specified size equivalence. The
normalization of rationalStalkUnit makes its coefficient coordinate exactly E[0]. -/
theorem rationalOperator_unit (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (ι : D.extensionSubfield n hn →+* D.k)
    (hι : ι.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k) :
    (localFrobeniusOperator l E D hl Y₀
        (constantWeilRationalComplex l E D hl Y₀)
        (embeddingPoint D Y₀ n hn x ι hι) (n - 1)
        (embeddingPoint_return D Y₀ n hn x ι hι)).hom ≫
      (rationalStalkUnit l E D hl Y₀ (embeddingPoint D Y₀ n hn x ι hι)).hom =
        (rationalStalkUnit l E D hl Y₀ (embeddingPoint D Y₀ n hn x ι hι)).hom := by
  sorry

/-- The actual rational operator is tensor of the actual integral operator, under
the prescribed rational point comparison, so rationalization respects operator equality.
Source: reviewed expansion step 8 (blueprint: lem-zl-constant-geometric-stalk-unit).
Proof: localPullbackObjectIso identifies the underlying integral objects. The rational
Weil map, composition maps and transport are the localized integral maps. Naturality
of the size-descent counit then identifies each factor of the two local composites.
Exact scalar extension preserves their composition, yielding the displayed square. -/
theorem rationalOperator_scalar (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (r : ℕ) (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom r =
      localPositivePower (frobeniusPointIso D).hom r ≫ x) :
    (pointFibreModuleLift E).mapDerivedCategory.map
        (localFrobeniusOperator l E D hl Y₀
          (constantWeilRationalComplex l E D hl Y₀) x r h).hom ≫
      (rationalFibreComparison l E D hl Y₀ x).hom =
        (rationalFibreComparison l E D hl Y₀ x).hom ≫
          (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
            (pointIntegralToField l E)).mapDerivedCategory.map
              (integralOperator l E D hl Y₀ x r h) := by
  sorry

end WeilConjectures.ConstantGeometricStalkUnit
